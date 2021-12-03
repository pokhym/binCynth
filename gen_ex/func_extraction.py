# https://github.com/JonathanSalwan/Triton/issues/995
from __future__ import print_function
from typing import Dict, List, Tuple
from typing_extensions import runtime
from io_example import IOExample
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

import sys
import os
import re
from execution_info import ExecutionInfo, InstructionInfo, InstructionType

# Script options
TARGET = "/home/user/pysynth/tests/c/empty_main"
TARGET = "/home/user/pysynth/tests/c/func_call"
INPUT_EXAMPLES = "/home/user/pysynth/tests/python/triton_int_only_example_1.txt"

# IO Examples
IO_EXAMPLES : Dict[bytes, IOExample] = {}

# Triton
CTX : TritonContext
MAIN_STACK_OFFSET = 8

# Execution Info
EXECUTION_INFO : ExecutionInfo

# Memory mapping
BASE_ARGV  = 0x10000000
BASE_STACK = 0x7fffffff
BASE_LIBC  = 0x80000008

def get_register_value(reg_in):
    for reg in CTX.getAllRegisters():
        if reg_in == reg:
            return CTX.getConcreteRegisterValue(reg)

    print("get_register_value: INVALID REGISTER", reg_in)
    exit(-1)

def get_memory_value(addr):
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
    return (addr.getSize(), CTX.getConcreteMemoryValue(mem))

def dump_instruction_accesses(instruction: Instruction):
    """
        TODO: Note that if an instruction reads and writes the same register/address
            this current implementation will get the new written value.
                eg. mov rax, rax
            The written and read value will be the same
            To solve this pass the value before processing (we can check who reads/writes)
    """
    print(instruction)
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
        reg_name_val = (r_reg[0].getName(), get_register_value(r_reg[0]))
        r_regs.update({reg_name_val[0] : reg_name_val[1]})
        print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
    print()
    print("\t\tRead Addresses:", end="")
    for r_addr in instruction.getLoadAccess():
        addr_val = (r_addr[0].getAddress(), get_memory_value(r_addr[0]))
        r_addrs.update({addr_val[0] : addr_val[1]})
        print(hex(addr_val[0]) + "," + hex(addr_val[1][1]), end="|")
    print()
    print("\t\tWritten Registers:", end="")
    for w_reg in instruction.getWrittenRegisters():
        reg_name_val = (w_reg[0].getName(), get_register_value(w_reg[0]))
        w_regs.update({reg_name_val[0] : reg_name_val[1]})
        print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
    print()
    print("\t\tgetStoreAccess:", end="")
    for w_addr in instruction.getStoreAccess():
        addr_val = (w_addr[0].getAddress(), get_memory_value(w_addr[0]))
        w_addrs.update({addr_val[0] : addr_val[1]})
        print(hex(addr_val[0]) + "," + hex(addr_val[1][1]), end="|")
    print()

    for expression in instruction.getSymbolicExpressions():
        smt.append((expression.getOrigin(), expression))
        # print(expression.getOrigin())
    
    # ''.join(r'\x'+hex(letter)[2:] for letter in instruction.getOpcode())
    curr_ii = InstructionInfo(eip, inst_type, r_regs, w_regs, r_addrs, w_addrs, smt, instruction.getOpcode())
    # if ret add the return registers
    if curr_ii.inst_type == InstructionType.RET_INST:
        for _rr in curr_ii.return_regs.keys():
            for r in CTX.getAllRegisters():
                if r.getName() == _rr:
                    curr_ii.return_regs.update({_rr : CTX.getConcreteRegisterValue(r)})
    EXECUTION_INFO.ii.append(curr_ii)

# Emulate the binary.
def emulate(ctx, pc):
    while pc:
        # Fetch opcode
        opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        ctx.processing(instruction)
        dump_instruction_accesses(instruction)

        if instruction.getType() == OPCODE.X86.HLT:
            break

        # Next
        pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

    return


def load_binary(ctx):
    import lief

    # Map the binary into the memory
    binary = lief.parse(TARGET)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        print('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)

    return binary

def run_triton(input_example):
    """
        Main loop to do multiple runs of Triton
    """
    global CTX, EXECUTION_INFO
    # Set the architecture
    CTX = TritonContext(ARCH.X86_64)

    EXECUTION_INFO = ExecutionInfo()

    # Set a symbolic optimization mode
    CTX.setMode(MODE.ALIGNED_MEMORY, True)

    # enable tainting
    # CTX.enableTaintEngine(True)

    # initialize all registers
    for reg in CTX.getAllRegisters():
        CTX.setConcreteRegisterValue(reg, 0)

    # Define a stack
    CTX.setConcreteRegisterValue(CTX.registers.rbp, BASE_STACK)
    CTX.setConcreteRegisterValue(CTX.registers.rsp, BASE_STACK)

    # Load the binary
    binary = load_binary(CTX)

    # set init register state in ExecutionInfo
    EXECUTION_INFO.set_init_regs(CTX)

    # set initial stack variables
    curr_offset = MAIN_STACK_OFFSET # 8
    for arg in input_example:
        print(arg)
        rbp = CTX.getConcreteRegisterValue(CTX.registers.rbp)
        print(hex(rbp - curr_offset - arg[0]))
        mem = MemoryAccess(rbp - curr_offset - arg[0], arg[0])
        CTX.setConcreteMemoryValue(mem, arg[1])
        # update offset to stack
        curr_offset += arg[0]

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
    emulate(CTX, binary.get_symbol('main').value)
    print('Emulation done')

    print("Processing ExecutionInfo...")
    print("Splitting functions...")
    EXECUTION_INFO.split_function()
    print("Calculating function identifiers...")
    EXECUTION_INFO.calculate_fi_hex_ids()
    print("Processing function input/output per function...")
    EXECUTION_INFO.extract_function_input_output()
    print("Updating final IO examples...")
    update_io_examples(input_example)

def update_io_examples(input_example):
    global IO_EXAMPLES
    for fi in EXECUTION_INFO.fi:
        if fi.hash_id not in IO_EXAMPLES.keys():
            IO_EXAMPLES.update({fi.hash_id : IOExample()})
        # if this is the init function call, we need to add the original input
        if fi.call_depth == 0:
            IO_EXAMPLES[fi.hash_id].add_func0_iargs(input_example)
        else:
            IO_EXAMPLES[fi.hash_id].add_iargs(fi.i_args)
        IO_EXAMPLES[fi.hash_id].add_oargs(fi.o_args)

def check_type(type_val : Tuple[str, str]):
    if type_val[0] == "int32":
        return (CPUSIZE.DWORD, int(type_val[1]))
    else:
        print("Invalid example input type", type_val)
        exit(-1)

def parse_examples():
    exs = []
    with open(INPUT_EXAMPLES, "r") as fd:
        while True:
            buf = fd.readline()
            if not buf:
                break
            buf = buf.replace("\n", "")
            buf = buf.rstrip(",")
            # print(buf)
            buf = buf.split(",")
            assert(len(buf) % 2 == 0)
            for i in range(0, len(buf), 2):
                print(i, i + 1)
            ex = [check_type(buf)]
            exs.append(ex)
        fd.close()
    return exs

if __name__ == '__main__':
    examples = parse_examples()
    for ex in examples:
        run_triton(ex)
    for func_hash_id, io in IO_EXAMPLES.items():
        print(func_hash_id)
        print("\t", io.i_args)
        print("\t", io.o_args)
        print()
    sys.exit(0)