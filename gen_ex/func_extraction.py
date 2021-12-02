# https://github.com/JonathanSalwan/Triton/issues/995
from __future__ import print_function
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

import sys
import os
import re
from execution_info import ExecutionInfo, InstructionInfo, InstructionType

# Registers Used
# REGISTERS

# Script options
TARGET = "/home/user/pysynth/tests/c/empty_main"
TARGET = "/home/user/pysynth/tests/c/func_call"

# Triton
CTX : TritonContext

# Execution Info
EXECUTION_INFO : ExecutionInfo = ExecutionInfo()

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
    """
    # match = re.findall(r"\[@0x[0-9a-f]+\]", addr_str)
    # assert(len(match) == 1)
    
    # match = int(match[0][2:-1], 16)

    # recall that the input to this function is w_addr[0]
    # alternatively w_addr[1].evaluate()
    mem = MemoryAccess(addr.getAddress(), addr.getSize())
    return CTX.getConcreteMemoryValue(mem)

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
    if "call" in str(instruction):
        inst_type = InstructionType.CALL_INST
    elif "ret" in str(instruction):
        inst_type = InstructionType.RET_INST
    else:
        inst_type = InstructionType.NORMAL_INST
    r_regs = []
    w_regs = []
    r_addrs = []
    w_addrs = []
    smt = []
    print("\tRead Registers:", end="")
    for r_reg in instruction.getReadRegisters():
        reg_name_val = (r_reg[0].getName(), get_register_value(r_reg[0]))
        r_regs.append(reg_name_val)
        print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
    print()
    print("\tRead Addresses:", end="")
    for r_addr in instruction.getLoadAccess():
        addr_val = (r_addr[0].getAddress(), get_memory_value(r_addr[0]))
        r_addrs.append(addr_val)
        print(hex(addr_val[0]) + "," + hex(addr_val[1]), end="|")
    print()
    print("\tWritten Registers:", end="")
    for w_reg in instruction.getWrittenRegisters():
        reg_name_val = (w_reg[0].getName(), get_register_value(w_reg[0]))
        w_regs.append(reg_name_val)
        print(reg_name_val[0] + "," + hex(reg_name_val[1]), end="|")
    print()
    print("\tgetStoreAccess:", end="")
    for w_addr in instruction.getStoreAccess():
        addr_val = (w_addr[0].getAddress(), get_memory_value(w_addr[0]))
        w_addrs.append(addr_val)
        print(hex(addr_val[0]) + "," + hex(addr_val[1]), end="|")
    print()

    for expression in instruction.getSymbolicExpressions():
        smt.append((expression.getOrigin(), expression))
        # print(expression.getOrigin())
    
    curr_ii = InstructionInfo(eip, inst_type, r_regs, w_regs, r_addrs, w_addrs, smt)
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


def loadBinary(ctx):
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


if __name__ == '__main__':
    # Set the architecture
    CTX = TritonContext(ARCH.X86_64)

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
    binary = loadBinary(CTX)

    # set init register state in ExecutionInfo
    EXECUTION_INFO.set_init_regs(CTX)

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

    sys.exit(0)