import sys
sys.path.insert(0,"/usr/lib/python3.8/site-packages")
from typing import List
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE
import re
from os.path import exists, abspath, splitext, join

class EquivalenceTest():
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
        self.ctx_1.setMode(MODE.ALIGNED_MEMORY, True)

        # set up constants for Triton
        self.base_stack = 0x7fffffff
        self.bytes_to_symbolize = 0x10

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
            # print('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
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
            # print(instruction)

            for expr in instruction.getSymbolicExpressions():
                output_smt += str(expr) + "\n"

            if instruction.getType() == OPCODE.X86.CALL:
                call_count += 1
                # print("CALL REACHED")
                # print("\tcall_count:", call_count)
                # print("\tret_count:", ret_count)
            elif instruction.getType() == OPCODE.X86.RET:
                ret_count += 1
                # print("RET REACHED")
                # print("\tcall_count:", call_count)
                # print("\tret_count:", ret_count)
            elif instruction.getType() == OPCODE.X86.HLT:
                break

            if call_count + 1 == ret_count:
                # print("TERMINATE")
                # print("\tcall_count:", call_count)
                # print("\tret_count:", ret_count)
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

    def determine_stack_size(self, prog_path):
        ctx = TritonContext(ARCH.X86_64)
        ctx.setMode(MODE.ALIGNED_MEMORY, True)
        for reg in ctx.getAllRegisters():
            ctx.setConcreteRegisterValue(reg, 0)
        ctx.setConcreteRegisterValue(ctx.registers.rbp, self.base_stack)
        ctx.setConcreteRegisterValue(ctx.registers.rsp, self.base_stack)
        binary = self.load_binary(ctx, prog_path)

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
    
    def symbolize_registers(self, ctx, prog_id):
        sym_regs = []

        output_smt = ""

        # symbolize anything that isnt rbp and rsp
        output_smt += "; SYMBOLIC REGISTERS\n"
        for reg in ctx.getAllRegisters():
            if True: # reg.getName() != 'rbp' or reg.getName != 'rsp':
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

        # rbp_main, rsp_main_sub, rsp_main = self.determine_stack_size(self.prog_path_0)
        # curr_offset = 0
        # # for arg_idx in range(2 - 1, -1, -1):
        # #     size = CPUSIZE.DWORD
        # #     for i in range(size):
        # #         sm = ctx.symbolizeMemory(MemoryAccess(rbp_main - curr_offset - i, 1), "prog_" + str(prog_id) + "_" + "mo_" + hex(i + arg_idx * size))
        # #         sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # #         # Declare sym var then output the references
        # #         output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        # #         output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
        # #     # update offset to stack
        # #     curr_offset += size
        # # for arg_idx in range(0,2):

        # mem = MemoryAccess(rsp_main - rsp_main_sub, rsp_main_sub)
        # sm = ctx.symbolizeMemory(mem, "prog_" + str(prog_id) + "_" + "mo_" + hex(rsp_main_sub))
        # sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        # output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
        # return output_smt, sym_mem

        # # size = CPUSIZE.DWORD
        # # sm = ctx.symbolizeMemory(MemoryAccess(rbp_main - curr_offset + size, size), "prog_" + str(prog_id) + "_" + "mo_" + hex(0 * size))
        # # sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # # # Declare sym var then output the references
        # # output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        # # output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
        # # # update offset to stack
        # # curr_offset += size

        # size = CPUSIZE.DWORD
        # sm = ctx.symbolizeMemory(MemoryAccess(rbp_main - curr_offset - size, size), "prog_" + str(prog_id) + "_" + "mo_" + hex(1 * size))
        # sym_mem.append("prog_" + str(prog_id) + "_ref!" + str(sm.getId()))
        # # Declare sym var then output the references
        # output_smt += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        # output_smt += str(ctx.getSymbolicExpression(sm.getId())) + "\n"
        # # update offset to stack
        # curr_offset += size

        # output_smt += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

        # return output_smt, sym_mem

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
            # print(v)
            # print("\t",v.getId(), v.getOrigin())
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
        output_smt += "\t(and\n"
        # output_smt += "\t\t(and\n"
        output_smt += "\t\t\t" + self.final_initial_conditions_ref + "\n"
        output_smt += "\t\t\t(not (=\n"
        output_smt += "\t\t\t\t" + self.output_smt_result_0_ref + "\n"
        output_smt += "\t\t\t\t" + self.output_smt_result_1_ref + "\n"
        output_smt += "\t\t\t))\n"
        # output_smt += "\t\t)\n"
        output_smt += "\t)\n"
        output_smt += ")\n"
        output_smt += "(check-sat)\n"
        # # output_smt += "(get-model)\n"

        # output_smt = ""
        # output_smt += "(assert\n"
        # output_smt += "\t(and\n"
        # # output_smt += "\t\t(and\n"
        # output_smt += "\t\t\t" + self.final_initial_conditions_ref + "\n"
        # output_smt += "\t\t\t(not (=\n"
        # output_smt += "\t\t\t\t" + self.output_smt_result_0_ref + "\n"
        # output_smt += "\t\t\t\t" + self.output_smt_result_1_ref + "\n"
        # output_smt += "\t\t\t))\n"
        # # output_smt += "\t\t)\n"
        # output_smt += "\t)\n"
        # output_smt += ")\n"
        # output_smt += "(check-sat)\n"
        # output_smt += "(get-model)\n"
        
        # output_smt = ""
        # output_smt += "(assert\n"
        # output_smt += "\t(not\n"
        # output_smt += "\t\t(and\n"
        # output_smt += "\t\t\t" + self.final_initial_conditions_ref + "\n"
        # output_smt += "\t\t\t(=\n"
        # output_smt += "\t\t\t\t" + self.output_smt_result_0_ref + "\n"
        # output_smt += "\t\t\t\t" + self.output_smt_result_1_ref + "\n"
        # output_smt += "\t\t\t)\n"
        # output_smt += "\t\t)\n"
        # output_smt += "\t)\n"
        # output_smt += ")\n"
        # output_smt += "(check-sat)\n"

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
        return abspath(join(self.output_smt_path, self.output_smt_name + self.smt_file_name_suffix))


if __name__ == "__main__":
    import subprocess

    # This is Equivalent: Returns unsat
    ec0 = EquivalenceTest(2, "/home/user/pysynth/equivalence/p1", "/home/user/pysynth/equivalence/p2", "/home/user/pysynth/equivalence", "eq")
    dir0 = ec0.eq_check()
    subprocess.run(["z3", "-smt2", dir0], capture_output=False)
    
    # This is Equivalent: Returns unsat
    ec1 = EquivalenceTest(2, "/home/user/pysynth/equivalence/p1_1", "/home/user/pysynth/equivalence/p2_1", "/home/user/pysynth/equivalence", "eq_1")
    dir1 = ec1.eq_check()
    subprocess.run(["z3", "-smt2", dir1], capture_output=False)
    
    # This is Equivalent: Returns unsat
    ec2 = EquivalenceTest(2, "/home/user/pysynth/equivalence/p1_2", "/home/user/pysynth/equivalence/p2_2", "/home/user/pysynth/equivalence", "eq_2")
    dir2 = ec2.eq_check()
    subprocess.run(["z3", "-smt2", dir2], capture_output=False)
    
    # This is not Equivalent: Returns sat
    ec3 = EquivalenceTest(2, "/home/user/pysynth/equivalence/p1_3", "/home/user/pysynth/equivalence/p2_3", "/home/user/pysynth/equivalence", "eq_3")
    dir3 = ec3.eq_check()
    subprocess.run(["z3", "-smt2", dir3], capture_output=False)
