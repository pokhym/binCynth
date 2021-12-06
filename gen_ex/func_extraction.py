# https://github.com/JonathanSalwan/Triton/issues/995
from __future__ import print_function
from typing import Dict, List, Tuple
from typing_extensions import runtime
from io_example import IOExample
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE
from os.path import abspath, exists

import sys
import os
import re
from execution_info import ExecutionInfo, InstructionInfo, InstructionType

# Script options
# TARGET = "/home/user/pysynth/tests/c/empty_main"
# TARGET = "/home/user/pysynth/tests/c/func_call"
TARGET = "/home/user/pysynth/tests/c/main_has_in_between"
INPUT_EXAMPLES = "/home/user/pysynth/tests/python/triton_int_only_example_1.txt"

# Memory mapping
BASE_ARGV  = 0x10000000
BASE_STACK = 0x7fffffff
BASE_LIBC  = 0x80000008

class FunctionExtractor:
    path_to_binary : str
    path_to_input_examples : str
    io_examples : Dict[Tuple[bytes, int], IOExample]
    ctx : TritonContext
    main_stack_offset : int
    execution_info : ExecutionInfo
    examples : List[str]
    next_call_site : bool # Next instruction is a call
    next_call_site_address : int # Address of the next call
    i_count : int 

    def __init__(self, path_to_input_examples : str, path_to_binary : str):
        self.path_to_input_examples = path_to_input_examples
        self.path_to_binary = path_to_binary
        self.io_examples = {}
        # Set the architecture
        self.ctx = TritonContext(ARCH.X86_64)
        # Set a symbolic optimization mode
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        # initialize all registers
        for reg in self.ctx.getAllRegisters():
            self.ctx.setConcreteRegisterValue(reg, 0)
        # Define a stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, BASE_STACK)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, BASE_STACK)
        self.main_stack_offset = CPUSIZE.QWORD
        self.execution_info = ExecutionInfo()
        self.examples = self.parse_examples()
        self.next_call_site = False
        self.next_call_site_address = None

        self.i_count = 0 # instruction count

    def check_type(self, type_val : Tuple[str, str]):
        if type_val[0] == "int32":
            return (CPUSIZE.DWORD, int(type_val[1]))
        else:
            print("Invalid example input type", type_val)
            exit(-1)
        
    def update_io_examples(self, input_example):
        # determine the max call depth of each unique call
        identifier_to_call_depth = {}
        for cd in sorted(self.execution_info.fi.keys(), reverse=True):
            for fi in self.execution_info.fi[cd]:
                if fi.identifier not in identifier_to_call_depth.keys():
                    identifier_to_call_depth.update({fi.identifier : fi.call_depth})
                elif fi.identifier in identifier_to_call_depth.keys():
                    if identifier_to_call_depth[fi.identifier] < fi.call_depth:
                        identifier_to_call_depth[fi.identifier] = fi.call_depth
        
        # update each FunctionInfo to reflect its max call depth
        for cd in sorted(self.execution_info.fi.keys(), reverse=True):
            for fi in self.execution_info.fi[cd]:
                fi.call_depth = identifier_to_call_depth[fi.identifier]

        # flatten all FunctionInfo into a list
        fi_list = []
        for cd in sorted(self.execution_info.fi.keys(), reverse=True):
            for fi in self.execution_info.fi[cd]:
                fi_list.append(fi)
            
        for fi in fi_list:
            if (fi.identifier, fi.call_depth) not in self.io_examples.keys():
                self.io_examples.update({(fi.identifier, fi.call_depth) : IOExample()})
            # if this is the init function call, we need to add the original input
            if fi.call_depth == 0:
                self.io_examples[(fi.identifier, fi.call_depth)].add_func0_iargs(input_example)
            else:
                self.io_examples[(fi.identifier, fi.call_depth)].add_iargs(fi.i_args)
            self.io_examples[(fi.identifier, fi.call_depth)].add_oargs(fi.o_args)
        
    def load_binary(self, ctx):
        import lief

        # Map the binary into the memory
        binary = lief.parse(self.path_to_binary)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            print('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
            ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)

        return binary

    def parse_examples(self):
        exs = []
        with open(abspath(self.path_to_input_examples), "r") as fd:
            while True:
                buf = fd.readline()
                if not buf:
                    break
                buf = buf.replace("\n", "")
                buf = buf.rstrip(",")
                # print(buf)
                buf = buf.split(",")
                assert(len(buf) % 2 == 0)
                # for i in range(0, len(buf), 2):
                #     print(i, i + 1)
                ex = []
                for i in range(0, len(buf), 2):
                    ex.append(self.check_type((buf[i], buf[i + 1])))
                    
                # ex = [self.check_type(buf)]
                exs.append(ex)
            fd.close()
        return exs

    def get_register_value(self, reg_in):
        for reg in self.ctx.getAllRegisters():
            if reg_in == reg:
                return self.ctx.getConcreteRegisterValue(reg)

        print("get_register_value: INVALID REGISTER", reg_in)
        exit(-1)

    def get_memory_value(self, addr):
        """
            [@0x7ffffff7]:64 bv[63..0]
            r"\[@0x[0-9a-f]+\]"

            Returns (size, value)
        """
        # match = re.findall(r"\[@0x[0-9a-f]+\]", addr_str)
        # assert(len(match) == 1)
        
        # match = int(match[0][2:-1], 16)

        # recall that the input to this function is w_addr[0]
        # alternatively w_addr[1].evaluate()
        mem = MemoryAccess(addr.getAddress(), addr.getSize())
        return (addr.getSize(), self.ctx.getConcreteMemoryValue(mem))

    def dump_instruction_accesses(self, instruction: Instruction):
        """
            TODO: Note that if an instruction reads and writes the same register/address
                this current implementation will get the new written value.
                    eg. mov rax, rax
                The written and read value will be the same
                To solve this pass the value before processing (we can check who reads/writes)
        """
        print(instruction, "|", self.i_count)
        
        eip = instruction.getAddress()
        inst_type : InstructionType
        return_regs : Dict[str, int]
        if "call" in str(instruction):
            inst_type = InstructionType.CALL_INST
        elif "ret" in str(instruction):
            inst_type = InstructionType.RET_INST
        elif "leave" in str(instruction):
            inst_type = InstructionType.LEAVE_INST
        else:
            inst_type = InstructionType.NORMAL_INST
        r_regs = {}
        w_regs = {}
        r_addrs = {}
        w_addrs = {}
        smt = []
        print("\t\tRead Registers:", end="")
        for r_reg in instruction.getReadRegisters():
            reg_name_val = (r_reg[0].getName(), self.get_register_value(r_reg[0]))
            r_regs.update({reg_name_val[0] : reg_name_val[1]})
            print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
        print()
        print("\t\tRead Addresses:", end="")
        for r_addr in instruction.getLoadAccess():
            addr_val = (r_addr[0].getAddress(), self.get_memory_value(r_addr[0]))
            r_addrs.update({addr_val[0] : addr_val[1]})
            print(hex(addr_val[0]) + "," + hex(addr_val[1][1]), end="|")
        print()
        print("\t\tWritten Registers:", end="")
        for w_reg in instruction.getWrittenRegisters():
            reg_name_val = (w_reg[0].getName(), self.get_register_value(w_reg[0]))
            w_regs.update({reg_name_val[0] : reg_name_val[1]})
            print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
        print()
        print("\t\tWritten Addresses:", end="")
        for w_addr in instruction.getStoreAccess():
            addr_val = (w_addr[0].getAddress(), self.get_memory_value(w_addr[0]))
            w_addrs.update({addr_val[0] : addr_val[1]})
            print(hex(addr_val[0]) + "," + hex(addr_val[1][1]), end="|")
        print()

        for expression in instruction.getSymbolicExpressions():
            smt.append((expression.getOrigin(), expression))
            # print(expression.getOrigin())
        
        # special case for the main, where it is the call site at the current address
        if self.i_count == 0:
            curr_ii = InstructionInfo(eip, True, instruction.getAddress(), self.i_count, inst_type, r_regs, w_regs, r_addrs, w_addrs, smt, instruction.getOpcode())
        # otherwise normal case
        else:
            curr_ii = InstructionInfo(eip, self.next_call_site, self.next_call_site_address, self.i_count, inst_type, r_regs, w_regs, r_addrs, w_addrs, smt, instruction.getOpcode())
        
        # if ret add the return registers
        if curr_ii.inst_type == InstructionType.RET_INST:
            for _rr in curr_ii.return_regs.keys():
                for r in self.ctx.getAllRegisters():
                    if r.getName() == _rr:
                        curr_ii.return_regs.update({_rr : self.ctx.getConcreteRegisterValue(r)})
        self.execution_info.ii.append(curr_ii)

        if "call" in str(instruction):
            call_operands = instruction.getOperands()
            assert(len(call_operands) == 1)
            self.next_call_site = True
            self.next_call_site_address = call_operands[0].getValue()
            print("########### CALL ###########")
        elif "ret" in str(instruction):
            self.next_call_site = False
            self.next_call_site_address = None
            print("########### RET ###########")
        else:
            self.next_call_site = False
            self.next_call_site_address = None
        
        self.i_count += 1

    def determine_stack_size(self):
        ctx = TritonContext(ARCH.X86_64)
        ctx.setMode(MODE.ALIGNED_MEMORY, True)
        for reg in ctx.getAllRegisters():
            ctx.setConcreteRegisterValue(reg, 0)
        ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
        ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)
        binary = self.load_binary(ctx)

        pc = binary.get_symbol('main').value
        instruction_count = 0
        while pc and instruction_count < 4:
            instruction_count += 1
            # Fetch opcode
            opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            ctx.processing(instruction)
            # dump_instruction_accesses(instruction)
            # print(instruction)

            if instruction.getType() == OPCODE.X86.HLT:
                break

            # Next
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

        assert("sub" in str(instruction))
        assert("rsp" == instruction.getOperands()[0].getName())

        # sub rsp, 0x20 <-- instruction.getOperands()[1].getValue() is 0x20
        # ctx.getConcreteRegisterValue(ctx.getRegister('rsp')) <-- gets the rsp value
        return (ctx.getConcreteRegisterValue(ctx.getRegister('rbp')), instruction.getOperands()[1].getValue(), ctx.getConcreteRegisterValue(ctx.getRegister('rsp')))
    
    def run_triton(self, input_example):
        """
            Main loop to do multiple runs of Triton
        """
        # Set the architecture
        self.ctx = TritonContext(ARCH.X86_64)
        # Set a symbolic optimization mode
        self.ctx.setMode(MODE.ALIGNED_MEMORY, True)
        # initialize all registers
        for reg in self.ctx.getAllRegisters():
            self.ctx.setConcreteRegisterValue(reg, 0)
        # Define a stack
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rbp, BASE_STACK)
        self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, BASE_STACK)
        
        # clear execution info
        self.execution_info = ExecutionInfo()
        # Load the binary
        binary = self.load_binary(self.ctx)

        # set init register state in ExecutionInfo
        self.execution_info.set_init_regs(self.ctx)

        """
            The first instructions to main
                endbr64
                push rbp        ; save rbp, also updates rbp - 8 (because rbp not ebp)
                mov rbp, rsp    ; rbp is now top of stack
                sub rsp, X      ; X is the space on the stack for local variables
        """
        rbp_main, rsp_main_sub, rsp_main = self.determine_stack_size()
        print(hex(rbp_main), hex(rsp_main_sub), hex(rsp_main))
        curr_offset = 0
        for arg_idx in range(len(input_example) - 1, -1, -1):
            arg = input_example[arg_idx]
            size = None
            if arg[0] == 4:
                size = CPUSIZE.DWORD
            else:
                exit(-1)
            mem = MemoryAccess(rbp_main - curr_offset - size, size)
            print("Modifying:", hex(rbp_main - curr_offset - size), "with", arg[1])
            self.ctx.setConcreteMemoryValue(mem, arg[1])
            # update offset to stack
            curr_offset += size

        # TODO: Set initial memory if we need to

        # TODO: Support argv
        # Define argvs
        # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x100, b'sample/sample_2')
        # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x200, b'hello world')
        # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 0, CPUSIZE.QWORD), BASE_ARGV + 0x100) # argv[0] = 'sample/sample_2'
        # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 8, CPUSIZE.QWORD), BASE_ARGV + 0x200) # argv[1] = 'hello world'
        # CTX.setConcreteRegisterValue(CTX.registers.rdi, 2)
        # ctx.setConcreteRegisterValue(ctx.registers.rsi, BASE_ARGV)


        # Let's emulate the binary from the entry point
        print('Starting emulation')
        self.emulate(binary.get_symbol('main').value)
        print('Emulation done')

        print("Processing ExecutionInfo...")
        print("Splitting functions...")
        self.execution_info.split_function()
        print("Processing function input/output per function...")
        self.execution_info.extract_function_input_output()
        print("Updating final IO examples...")
        self.update_io_examples(input_example)

    # Emulate the binary.
    def emulate(self, pc):
        while pc:
            # Fetch opcode
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            self.ctx.processing(instruction)
            self.dump_instruction_accesses(instruction)

            if instruction.getType() == OPCODE.X86.HLT:
                break

            # Next
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)

        return

    def flatten_final_io(self):
        """
            Finally flattens the examples into text format and writes them out
        """
        if len(self.io_examples.keys()) == 0:
            return None
        count = 0
        key_by_call_depth = self.io_examples.keys()
        key_by_call_depth = sorted(key_by_call_depth, key=lambda x: x[1], reverse=True)
        files_to_return = []
        for k_cd in key_by_call_depth:
            while True:
                curr_file_name = abspath("io_ex_" + str(count) + ".txt")
                if not exists(curr_file_name):
                    files_to_return.append(curr_file_name)
                    with open(curr_file_name, "w") as fd:
                        # TODO: Assuming only integer 32 bit
                        f_io = self.io_examples[k_cd]

                        # check number of examples are the same
                        assert(len(f_io.i_args) == len(f_io.o_args))
                        for example_idx in range(len(f_io.i_args)):
                            o_args = f_io.o_args[example_idx]
                            i_args = f_io.i_args[example_idx]
                            for o in o_args:
                                # TODO: Only 32 bit ints
                                fd.write("out,int32,")
                                fd.write(str(o[1]))
                                fd.write(",")
                            for i_ex in i_args:
                                # TODO: Only 32 bit ints
                                fd.write("in,int32,")
                                fd.write(str(i_ex[1][1]))
                                fd.write(",")
                            fd.write("\n")
                    fd.close()
                    count += 1
                    break
                # increment for next example
                count += 1
        return files_to_return
        
    def run(self):
        # IO_EXAMPLES.clear()
        examples = self.parse_examples()
        for ex in examples:
            self.run_triton(ex)
        for func_hash_id, io in self.io_examples.items():
            print(func_hash_id)
            print("\t", io.i_args)
            print("\t", io.o_args)
            print()
        return self.flatten_final_io()

if __name__ == "__main__":
    fe = FunctionExtractor(INPUT_EXAMPLES, TARGET)
    print(fe.run())