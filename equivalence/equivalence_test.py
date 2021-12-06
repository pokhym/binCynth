from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE
import re

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

def determine_stack_size():
    ctx = TritonContext(ARCH.X86_64)
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    for reg in ctx.getAllRegisters():
        ctx.setConcreteRegisterValue(reg, 0)
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)
    binary = load_binary(ctx)

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

def emulate(pc):
    global OUTPUT_SMT
    call_count = 0
    ret_count = 0

    OUTPUT_SMT += "; INSTRUCTION EXECUTION RESULTS\n"
    while pc:
        # Fetch opcode
        opcode = CTX.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        CTX.processing(instruction)
        print(instruction)
        #
        for expr in instruction.getSymbolicExpressions():
            OUTPUT_SMT += str(expr) + "\n"

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
        pc = CTX.getConcreteRegisterValue(CTX.registers.rip)

    OUTPUT_SMT += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
    return


if __name__ == "__main__":
    sym_regs = []
    sym_mem = []
    # symbolize anything that isnt rbp and rsp
    OUTPUT_SMT += "; SYMBOLIC REGISTERS\n"
    for reg in CTX.getAllRegisters():
        if reg.getName() != 'rbp' or reg.getName != 'rsp':
            sr = CTX.symbolizeRegister(reg, reg.getName() + "_sym")
            sym_regs.append(sr)
            # Declare sym var then output the references
            OUTPUT_SMT += "(declare-fun " + sr.getAlias() + "() (_ BitVec " + str(sr.getBitSize()) + "))\n"
            OUTPUT_SMT += str(CTX.getSymbolicExpression(sr.getId())) + "\n"
    OUTPUT_SMT += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"
    
    # symbolize memory around the stack
    OUTPUT_SMT += "; SYMBOLIC MEMROY\n"
    sm = CTX.symbolizeMemory(MemoryAccess(BASE_STACK, CPUSIZE.DWORD), "mo_" + hex(0))
    # Declare sym var then output the references
    OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
    OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
    for i in range(1, BYTES_TO_SYMBOLIZE, 1):
        mem_plus = MemoryAccess(BASE_STACK + i * CPUSIZE.DWORD, CPUSIZE.DWORD)
        sm = CTX.symbolizeMemory(mem_plus, 'mp_' + hex(i * CPUSIZE.DWORD))
        # Declare sym var then output the references
        OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
        sym_mem.append(sm)
        mem_minus = MemoryAccess(BASE_STACK - i * CPUSIZE.DWORD, CPUSIZE.DWORD)
        sm = CTX.symbolizeMemory(mem_minus, 'mm_' + hex(i * CPUSIZE.DWORD))
        # Declare sym var then output the references
        OUTPUT_SMT += "(declare-fun " + sm.getAlias() + "() (_ BitVec " + str(sm.getBitSize()) + "))\n"
        OUTPUT_SMT += str(CTX.getSymbolicExpression(sm.getId())) + "\n"
        sym_mem.append(sm)
    OUTPUT_SMT += ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n"

    # get binary
    binary = load_binary(CTX)

    # get rsp/rbp
    rbp_main, rsp_main_sub, rsp_main = determine_stack_size()
    print(hex(rbp_main), hex(rsp_main_sub), hex(rsp_main))

    # emulate 
    emulate(binary.get_symbol('main').value)

    # replace ref!0 with PROG_NAME_ref!0
    OUTPUT_SMT = OUTPUT_SMT.replace("ref!", "prog_" + str(PROGRAM_ID) + "_" + "ref!")

    se = CTX.getSymbolicExpressions()
    for k in sorted(se.keys(), reverse=True):
        v = se[k]
        print(v)
        print("\t",v.getId(), v.getOrigin())
        if(v.getOrigin().getName() == "rax" or v.getOrigin().getName() == "eax"):
            OUTPUT_SMT += "(define-fun prog_" + str(PROGRAM_ID) + "_final_" + v.getOrigin().getName() + " () (_ BitVec " + str(v.getOrigin().getBitSize()) + ") " + "prog_" + str(PROGRAM_ID) + "!" + str(v.getId()) + ")"
            break

    # output smt
    fd = open("/home/user/pysynth/equivalence/" + SMT_FILE_NAME, "w")
    fd.write(OUTPUT_SMT)
    fd.close()

