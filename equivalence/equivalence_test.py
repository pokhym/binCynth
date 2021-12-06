from typing import List
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE
import re
from os.path import exists, abspath, splitext, join
import pathlib

OUTPUT_SMT = ""
SMT_FILE_NAME = "out.smt2"
PROGRAM_ID = 0
TARGET = "/home/user/pysynth/tests/c/main_has_in_between"
BASE_STACK = 0x7fffffff
BYTES_TO_SYMBOLIZE = 0xFF
NUM_ARGS = 0x2
ARG_SIZE = CPUSIZE.DWORD

CTX = TritonContext()
CTX.setArchitecture(ARCH.X86_64)
CTX.setMode(MODE.ALIGNED_MEMORY, True)


class EquivalenceChecker():
    ctx_0 : TritonContext
    ctx_1 : TritonContext
    base_stack : int
    bytes_to_symbolize : int
    num_iargs : int
    smt_0_init_ref : List[str]
    smt_1_init_ref : List[str]
    final_initial_conditions : str
    final_initial_conditions_ref : str
    equality_condition : str
    smt_file_name_prefix : str
    smt_file_name_suffix : str
    output_smt_path : str
    output_smt_name : str
    output_smt_0 : str
    output_smt_result_0 : str # Things to perform eq check on
    output_smt_result_0_ref : str
    output_smt_1 : str
    output_smt_result_1 : str # Things to perform eq check on
    output_smt_result_1_ref : str
    prog_path_0 : str
    prog_path_1 : str

    def __init__(self, num_iargs : int, prog_path_0 : str, prog_path_1 : str, output_smt_path : str, output_smt_name : str):
        # set up the Triton Contexts
        self.ctx_0 = TritonContext()
        self.ctx_0.setArchitecture(ARCH.X86_64)
        self.ctx_0.setMode(MODE.ALIGNED_MEMORY, True)
        self.ctx_1 = TritonContext()
        self.ctx_1.setArchitecture(ARCH.X86_64)
        self.ctx_0.setMode(MODE.ALIGNED_MEMORY, True)

        # set up constants for Triton
        self.base_stack = 0x7fffffff
        self.bytes_to_symbolize = 0xFF

        # number of input arguments
        self.num_iargs = num_iargs

        # the initial references to check equivalence on
        self.smt_0_init_ref = []
        self.smt_1_init_ref = []
        self.final_initial_conditions = ""
        self.final_initial_conditions_ref = ""

        # set equality condition
        self.equality_condition = ""

        # prefix/suffix for smt output file
        self.smt_file_name_prefix = "prog_"
        self.smt_file_name_suffix = ".smt2"
        # empty out the final smt for z3
        assert(exists(abspath(output_smt_path)))
        self.output_smt_path = output_smt_path
        self.output_smt_name = output_smt_name
        self.output_smt_0 = ""
        self.output_smt_result_0 = ""
        self.output_smt_result_0_ref = ""
        self.output_smt_1 = ""
        self.output_smt_result_1 = ""
        self.output_smt_result_1_ref = ""

        # set up input program paths
        assert(exists(abspath(prog_path_0)))
        assert(exists(abspath(prog_path_1)))
        self.prog_path_0 = abspath(prog_path_0)
        self.prog_path_1 = abspath(prog_path_1)


    def load_binary(self, ctx, prog_path):
        import lief

        # Map the binary into the memory
        binary = lief.parse(prog_path)
        phdrs  = binary.segments
        for phdr in phdrs:
            size   = phdr.physical_size
            vaddr  = phdr.virtual_address
            print('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
            ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)

        return binary

    def emulate(self, ctx, pc, prog_id):
        output_smt = ""
        call_count = 0
        ret_count = 0

        output_smt += "; INSTRUCTION EXECUTION RESULTS\n"
        while pc:
            # Fetch opcode
            opcode = ctx.getConcreteMemoryAreaValue(pc, 16)

            # Create the Triton instruction
            instruction = Instruction()
            instruction.setOpcode(opcode)
            instruction.setAddress(pc)

            # Process
            ctx.processing(instruction)
            print(instruction)
            #
            for expr in instruction.getSymbolicExpressions():
                output_smt += str(expr) + "\n"

            if instruction.getType() == OPCODE.X86.CALL:
                call_count += 1
                print("CALL REACHED")
                print("\tcall_count:", call_count)
                print("\tret_count:", ret_count)
            elif instruction.getType() == OPCODE.X86.RET:
                ret_count += 1
                print("RET REACHED")
                print("\tcall_count:", call_count)
                print("\tret_count:", ret_count)
            elif instruction.getType() == OPCODE.X86.HLT:
                break

            if call_count + 1 == ret_count:
                print("TERMINATE")
                print("\tcall_count:", call_count)
                print("\tret_count:", ret_count)
                break
            # Next
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

        output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

        if prog_id == 0:
            self.output_smt_0 += output_smt
        elif prog_id == 1:
            self.output_smt_1 += output_smt
        else:
            print("Invalid program ID (0 or 1)")
            exit(-1)

        return
    
    def symbolize_registers(self, ctx, prog_id):
        sym_regs = []

        output_smt = ""

        # symbolize anything that isnt rbp and rsp
        output_smt += "; SYMBOLIC REGISTERS\n"
        for reg in ctx.getAllRegisters():
            if reg.getName() != 'rbp' or reg.getName != 'rsp':
                sr = ctx.symbolizeRegister(reg, "prog_" + str(prog_id) + "_" + reg.getName() + "_sym")
                sym_regs.append("prog_" + str(prog_id) + "_ref!" + str(sr.getId()))
                # Declare sym var then output the references
                output_smt += "(declare-fun " + sr.getAlias() + "() (_ BitVec " + str(sr.getBitSize()) + "))\n"
                output_smt += str(ctx.getSymbolicExpression(sr.getId())) + "\n"
        output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

        return output_smt, sym_regs
    
    def symbolize_memory(self, ctx, prog_id):
        sym_mem = []
        output_smt = ""

        # symbolize memory around the stack
        output_smt += "; SYMBOLIC MEMORY\n"
        sm = ctx.symbolizeMemory(MemoryAccess(self.base_stack, CPUSIZE.BYTE), "prog_" + str(prog_id) + "_" + "mo_" + hex(0))
        sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # Declare sym var then output the references
        output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"

        # sm = ctx.symbolizeMemory(MemoryAccess(self.base_stack + 16, CPUSIZE.BYTE), "prog_" + str(prog_id) + "_" + "mo_" + hex(1))
        # sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # # Declare sym var then output the references
        # output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        # output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"

        for i in range(1, self.bytes_to_symbolize, 1):
            # print(output_smt)
            mem_plus = MemoryAccess(self.base_stack + i, CPUSIZE.BYTE)
            sm = ctx.symbolizeMemory(mem_plus, "prog_" + str(prog_id) + "_" + 'mp_' + hex(i))
            # Declare sym var then output the references
            output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
            output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
            sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
            mem_minus = MemoryAccess(self.base_stack - i, CPUSIZE.BYTE)
            sm = ctx.symbolizeMemory(mem_minus, "prog_" + str(prog_id) + "_" + 'mm_' + hex(i))
            # Declare sym var then output the references
            output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
            output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
            sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

        return output_smt, sym_mem

    def get_last_rax(self, ctx, prog_id):
        se = ctx.getSymbolicExpressions()
        output_smt = "; FINAL RAX\n"
        for k in sorted(se.keys(), reverse=True):
            v = se[k]
            print(v)
            print("\t",v.getId(), v.getOrigin())
            if(v.getOrigin().getName() == "rax" or v.getOrigin().getName() == "eax"):
                output_smt += "(define-fun prog_" + str(prog_id) + "_final_" + v.getOrigin().getName() + " () (_ BitVec " + str(v.getOrigin().getBitSize()) + ") " + "prog_" + str(prog_id) + "_ref!" + str(v.getId()) + ")\n"
                if prog_id == 0:
                    self.output_smt_result_0_ref = "prog_" + str(prog_id) + "_final_" + v.getOrigin().getName()
                elif prog_id == 1:
                    self.output_smt_result_1_ref = "prog_" + str(prog_id) + "_final_" + v.getOrigin().getName()
                else:
                    exit(-1)
                break
        output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
        return output_smt

    def get_initial_conditions(self):
        self.final_initial_conditions_ref = "init_cond"
        output_smt = "; INITIAL CONDITIONS\n"
        output_smt += "(define-fun init_cond () Bool \n"
        output_smt += "\t(and\n"
        assert(len(self.smt_0_init_ref) == len(self.smt_1_init_ref))
        for _0, _1 in zip(self.smt_0_init_ref, self.smt_1_init_ref):
            output_smt += "\t\t(= " + _0 + " " + _1 + ")\n"
            # print(_0, _1)
        output_smt += "\t)\n"
        output_smt += ")\n"
        output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
        return output_smt
    
    def gen_eq_condition(self):
        output_smt = ""
        output_smt += "(assert\n"
        output_smt += "\t(not\n"
        output_smt += "\t\t(=>\n"
        output_smt += "\t\t\t" + self.final_initial_conditions_ref + "\n"
        output_smt += "\t\t\t(=\n"
        output_smt += "\t\t\t\t" + self.output_smt_result_0_ref + "\n"
        output_smt += "\t\t\t\t" + self.output_smt_result_1_ref + "\n"
        output_smt += "\t\t\t)\n"
        output_smt += "\t\t)\n"
        output_smt += "\t)\n"
        output_smt += ")\n"
        output_smt += "(check-sat)\n"
        return output_smt


    
    def eq_check(self,):
        output_smt = ""
        init_reg_ref_0 = []
        init_reg_ref_1 = []
        init_mem_ref_0 = []
        init_mem_ref_1 = []
        prog_0_rax_final_ref = ""
        prog_1_rax_final_ref = ""

        # symbolize registers
        output_smt, init_reg_ref_0 = self.symbolize_registers(self.ctx_0, 0)
        self.output_smt_0 += output_smt
        for irr0 in init_reg_ref_0:
            self.smt_0_init_ref.append(irr0)
        output_smt, init_reg_ref_1 = self.symbolize_registers(self.ctx_1, 1)
        self.output_smt_1 += output_smt
        for irr1 in init_reg_ref_1:
            self.smt_1_init_ref.append(irr1)

        # symbolize memory
        output_smt, init_mem_ref_0 = self.symbolize_memory(self.ctx_0, 0)
        self.output_smt_0 += output_smt
        for imrf0 in init_mem_ref_0:
            self.smt_0_init_ref.append(imrf0)
        output_smt, init_mem_ref_1 = self.symbolize_memory(self.ctx_1, 1)
        self.output_smt_1 += output_smt
        for imrf1 in init_mem_ref_1:
            self.smt_1_init_ref.append(imrf1)

        # load binaries
        binary_0 = self.load_binary(self.ctx_0, self.prog_path_0)
        binary_1 = self.load_binary(self.ctx_1, self.prog_path_1)

        # emulate binaries
        self.emulate(self.ctx_0, binary_0.get_symbol('main').value, 0)
        self.emulate(self.ctx_1, binary_1.get_symbol('main').value, 1)

        # replace ref!0 with PROG_NAME_ref!0
        self.output_smt_0 = self.output_smt_0.replace("ref!", "prog_" + str(0) + "_" + "ref!")
        self.output_smt_1 = self.output_smt_1.replace("ref!", "prog_" + str(1) + "_" + "ref!")

        # obtain last expression that used rax/eax for the return value
        self.output_smt_result_0 = self.get_last_rax(self.ctx_0, 0)
        self.output_smt_result_1 = self.get_last_rax(self.ctx_1, 1)

        self.final_initial_conditions = self.get_initial_conditions()
        self.equality_condition = self.gen_eq_condition()

        # output smt
        fd = open(join(self.output_smt_path, self.output_smt_name + self.smt_file_name_suffix), "w")
        fd.write(self.output_smt_0)
        fd.write(self.output_smt_1)
        fd.write(self.final_initial_conditions)
        fd.write(self.output_smt_result_0)
        fd.write(self.output_smt_result_1)
        fd.write(self.equality_condition)
        fd.close()
        # fd = open(join(self.output_smt_path, self.smt_file_name_prefix + pathlib.Path(self.prog_path_0).resolve().stem + self.smt_file_name_suffix), "w")
        # fd.write(self.output_smt_0)
        # fd.close()
        # fd = open(join(self.output_smt_path, self.smt_file_name_prefix + pathlib.Path(self.prog_path_1).resolve().stem + self.smt_file_name_suffix), "w")
        # fd.write(self.output_smt_1)
        # fd.close()


if __name__ == "__main__":
    # def __init__(self, num_iargs : int, prog_path_0 : str, prog_path_1 : str, output_smt_path : str):
    ec = EquivalenceChecker(2, "/home/user/pysynth/equivalence/p1", "/home/user/pysynth/equivalence/p2", "/home/user/pysynth/equivalence", "eq")
    ec.eq_check()
    # sym_regs = []
    # sym_mem = []
    # # symbolize anything that isnt rbp and rsp
    # OUTPUT_SMT += "; SYMBOLIC REGISTERS\n"
    # for reg in CTX.getAllRegisters():
    #     if reg.getName() != 'rbp' or reg.getName != 'rsp':
    #         sr = CTX.symbolizeRegister(reg, reg.getName() + "_sym")
    #         sym_regs.append(sr)
    #         # Declare sym var then output the references
    #         OUTPUT_SMT += "(declare-fun " + sr.getAlias() + "() (_ BitVec " + str(sr.getBitSize()) + "))\n"
    #         OUTPUT_SMT += str(CTX.getSymbolicExpression(sr.getId())) + "\n"
    # OUTPUT_SMT += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
    
    # # symbolize memory around the stack
    # OUTPUT_SMT += "; SYMBOLIC MEMROY\n"
    # sm = CTX.symbolizeMemory(MemoryAccess(BASE_STACK, CPUSIZE.DWORD), "mo_" + hex(0))
    # # Declare sym var then output the references
    # OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
    # OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
    # for i in range(1, BYTES_TO_SYMBOLIZE, 1):
    #     mem_plus = MemoryAccess(BASE_STACK + i * CPUSIZE.DWORD, CPUSIZE.DWORD)
    #     sm = CTX.symbolizeMemory(mem_plus, 'mp_' + hex(i * CPUSIZE.DWORD))
    #     # Declare sym var then output the references
    #     OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
    #     OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
    #     sym_mem.append(sm)
    #     mem_minus = MemoryAccess(BASE_STACK - i * CPUSIZE.DWORD, CPUSIZE.DWORD)
    #     sm = CTX.symbolizeMemory(mem_minus, 'mm_' + hex(i * CPUSIZE.DWORD))
    #     # Declare sym var then output the references
    #     OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
    #     OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
    #     sym_mem.append(sm)
    # OUTPUT_SMT += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

    # # get binary
    # binary = load_binary(CTX)

    # # emulate 
    # emulate(binary.get_symbol('main').value)

    # # replace ref!0 with PROG_NAME_ref!0
    # OUTPUT_SMT = OUTPUT_SMT.replace("ref!", "prog_" + str(PROGRAM_ID) + "_" + "ref!")

    # se = CTX.getSymbolicExpressions()
    # for k in sorted(se.keys(), reverse=True):
    #     v = se[k]
    #     print(v)
    #     print("\t",v.getId(), v.getOrigin())
    #     if(v.getOrigin().getName() == "rax" or v.getOrigin().getName() == "eax"):
    #         OUTPUT_SMT += "(define-fun prog_" + str(PROGRAM_ID) + "_final_" + v.getOrigin().getName() + " () (_ BitVec " + str(v.getOrigin().getBitSize()) + ") " + "prog_" + str(PROGRAM_ID) + "!" + str(v.getId()) + ")"
    #         break

    # # output smt
    # fd = open("/home/user/pysynth/equivalence/" + SMT_FILE_NAME, "w")
    # fd.write(OUTPUT_SMT)
    # fd.close()

