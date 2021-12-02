# https://github.com/JonathanSalwan/Triton/issues/995
from __future__ import print_function
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

import sys
import os
import re

# Script options
TARGET = "/home/user/pysynth/tests/c/empty_main"
TARGET = "/home/user/pysynth/tests/c/func_call"

# Triton Context
CTX : TritonContext

# Memory mapping
BASE_ARGV  = 0x10000000
BASE_STACK = 0x7fffffff
BASE_LIBC  = 0x80000008

def get_register_value(reg_str : str):
    if "rax" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rbx)
    elif "rbx"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rbx)
    elif "rcx"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rcx)
    elif "rdx"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rdx)
    elif "rdi"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rdi)
    elif "rsi"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rsi)
    elif "rsp"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rsp)
    elif "rbp"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rbp)
    elif "rip"  in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.rip)
    elif "eax" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.eax)
    elif "ebx" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.ebx)
    elif "ecx" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.ecx)
    elif "edx" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.edx)
    elif "edi" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.edi)
    elif "esi" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.esi)
    elif "esp" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.esi)
    elif "ebp" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.ebp)
    elif "eip" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.eip)
    elif "eflags" or "cf" or "pf" or "af" or "zf" or "sf" or "tf" or \
                "if" or "df" or "of" or "nt" or "rf" or "vm" or "ac" or \
                "vif" or "vip" or "id" in reg_str:
        return CTX.getConcreteRegisterValue(CTX.registers.eflags)
    elif "r8" in reg_str:
        print("r8 not yet implemented")
        exit(-1)
    elif "r9"   in reg_str:
        print("r9 not yet implemented")
        exit(-1)
    elif "r10"  in reg_str:
        print("r10 not yet implemented")
        exit(-1)
    elif "r11"  in reg_str:
        print("r11 not yet implemented")
        exit(-1)
    elif "r12"  in reg_str:
        print("r12 not yet implemented")
        exit(-1)
    elif "r13"  in reg_str:
        print("r13 not yet implemented")
        exit(-1)
    elif "r14"  in reg_str:
        print("r14 not yet implemented")
        exit(-1)
    elif "r15"  in reg_str:
        print("r15 not yet implemented")
        exit(-1)
    elif "mm0"  in reg_str:
        print("mm0 not yet implemented")
        exit(-1)
    elif "mm1"  in reg_str:
        print("mm1 not yet implemented")
        exit(-1)
    elif "mm2"  in reg_str:
        print("mm2 not yet implemented")
        exit(-1)
    elif "mm3"  in reg_str:
        print("mm3 not yet implemented")
        exit(-1)
    elif "mm4"  in reg_str:
        print("mm4 not yet implemented")
        exit(-1)
    elif "mm5"  in reg_str:
        print("mm5 not yet implemented")
        exit(-1)
    elif "mm6"  in reg_str:
        print("mm6 not yet implemented")
        exit(-1)
    elif "mm7"  in reg_str:
        print("mm7 not yet implemented")
        exit(-1)
    elif "ymm0" in reg_str:
        print("ymm0 not yet implemented")
        exit(-1)
    elif "ymm1" in reg_str:
        print("ymm1 not yet implemented")
        exit(-1)
    elif "ymm2" in reg_str:
        print("ymm2 not yet implemented")
        exit(-1)
    elif "ymm3" in reg_str:
        print("ymm3 not yet implemented")
        exit(-1)
    elif "ymm4" in reg_str:
        print("ymm4 not yet implemented")
        exit(-1)
    elif "ymm5" in reg_str:
        print("ymm5 not yet implemented")
        exit(-1)
    elif "ymm6" in reg_str:
        print("ymm6 not yet implemented")
        exit(-1)
    elif "ymm7" in reg_str:
        print("ymm7 not yet implemented")
        exit(-1)
    elif "zmm0" in reg_str:
        print("zmm0 not yet implemented")
        exit(-1)
    elif "zmm1" in reg_str:
        print("zmm1 not yet implemented")
        exit(-1)
    elif "zmm2" in reg_str:
        print("zmm2 not yet implemented")
        exit(-1)
    elif "zmm3" in reg_str:
        print("zmm3 not yet implemented")
        exit(-1)
    elif "zmm4" in reg_str:
        print("zmm4 not yet implemented")
        exit(-1)
    elif "zmm5" in reg_str:
        print("zmm5 not yet implemented")
        exit(-1)
    elif "zmm6" in reg_str:
        print("zmm6 not yet implemented")
        exit(-1)
    elif "zmm7" in reg_str:
        print("zmm7 not yet implemented")
        exit(-1)
    elif "zmm8" in reg_str:
        print("zmm8 not yet implemented")
        exit(-1)
    elif "zmm9" in reg_str:
        print("zmm9 not yet implemented")
        exit(-1)
    elif "zmm10" in reg_str:
        print("zmm10 not yet implemented")
        exit(-1)
    elif "zmm11" in reg_str:
        print("zmm11 not yet implemented")
        exit(-1)
    elif "zmm12" in reg_str:
        print("zmm12 not yet implemented")
        exit(-1)
    elif "zmm13" in reg_str:
        print("zmm13 not yet implemented")
        exit(-1)
    elif "zmm14" in reg_str:
        print("zmm14 not yet implemented")
        exit(-1)
    elif "zmm15" in reg_str:
        print("zmm15 not yet implemented")
        exit(-1)
    elif "zmm16" in reg_str:
        print("zmm16 not yet implemented")
        exit(-1)
    elif "zmm17" in reg_str:
        print("zmm17 not yet implemented")
        exit(-1)
    elif "zmm18" in reg_str:
        print("zmm18 not yet implemented")
        exit(-1)
    elif "zmm19" in reg_str:
        print("zmm19 not yet implemented")
        exit(-1)
    elif "zmm20" in reg_str:
        print("zmm20 not yet implemented")
        exit(-1)
    elif "zmm21" in reg_str:
        print("zmm21 not yet implemented")
        exit(-1)
    elif "zmm22" in reg_str:
        print("zmm22 not yet implemented")
        exit(-1)
    elif "zmm23" in reg_str:
        print("zmm23 not yet implemented")
        exit(-1)
    elif "zmm24" in reg_str:
        print("zmm24 not yet implemented")
        exit(-1)
    elif "zmm25" in reg_str:
        print("zmm25 not yet implemented")
        exit(-1)
    elif "zmm26" in reg_str:
        print("zmm26 not yet implemented")
        exit(-1)
    elif "zmm27" in reg_str:
        print("zmm27 not yet implemented")
        exit(-1)
    elif "zmm28" in reg_str:
        print("zmm28 not yet implemented")
        exit(-1)
    elif "zmm29" in reg_str:
        print("zmm29 not yet implemented")
        exit(-1)
    elif "zmm30" in reg_str:
        print("zmm30 not yet implemented")
        exit(-1)
    elif "zmm31" in reg_str:
        print("zmm13 not yet implemented")
        exit(-1)
    elif "mxcsr" in reg_str:
        print("mxcsr not yet implemented")
        exit(-1)
    elif "cr0"  in reg_str:
        print("cr0 not yet implemented")
        exit(-1)
    elif "cr1"  in reg_str:
        print("cr1 not yet implemented")
        exit(-1)
    elif "cr2"  in reg_str:
        print("cr2 not yet implemented")
        exit(-1)
    elif "cr3"  in reg_str:
        print("cr3 not yet implemented")
        exit(-1)
    elif "cr4"  in reg_str:
        print("cr4 not yet implemented")
        exit(-1)
    elif "cr5"  in reg_str:
        print("cr5 not yet implemented")
        exit(-1)
    elif "cr6"  in reg_str:
        print("cr6 not yet implemented")
        exit(-1)
    elif "cr7"  in reg_str:
        print("cr7 not yet implemented")
        exit(-1)
    elif "cr8"  in reg_str:
        print("cr8 not yet implemented")
        exit(-1)
    elif "cr9"  in reg_str:
        print("cr9 not yet implemented")
        exit(-1)
    elif "cr10" in reg_str:
        print("cr10 not yet implemented")
        exit(-1)
    elif "cr11" in reg_str:
        print("cr11 not yet implemented")
        exit(-1)
    elif "cr12" in reg_str:
        print("cr12 not yet implemented")
        exit(-1)
    elif "cr13" in reg_str:
        print("cr13 not yet implemented")
        exit(-1)
    elif "cr14" in reg_str:
        print("cr14 not yet implemented")
        exit(-1)
    elif "cr15" in reg_str:
        print("cr15 not yet implemented")
        exit(-1)
    elif "cs"   in reg_str:
        print("cs not yet implemented")
        exit(-1)
    elif "ds"   in reg_str:
        print("ds not yet implemented")
        exit(-1)
    elif "es"   in reg_str:
        print("es not yet implemented")
        exit(-1)
    elif "fs"   in reg_str:
        print("fs not yet implemented")
        exit(-1)
    elif "gs"   in reg_str:
        print("gs not yet implemented")
        exit(-1)
    elif "ss"   in reg_str:
        print("ss not yet implemented")
        exit(-1)
    elif "dr0"  in reg_str:
        print("dr0 not yet implemented")
        exit(-1)
    elif "dr1"  in reg_str:
        print("dr1 not yet implemented")
        exit(-1)
    elif "dr2"  in reg_str:
        print("dr2 not yet implemented")
        exit(-1)
    elif "dr3"  in reg_str:
        print("dr3 not yet implemented")
        exit(-1)
    elif "dr6"  in reg_str:
        print("dr6 not yet implemented")
        exit(-1)
    elif "dr7"  in reg_str:
        print("dr7 not yet implemented")
        exit(-1)
    else:
        print("get_register_value: INVALID REGISTER NAME", reg_str)
        exit(-1)

def get_memory_value(addr_str : str):
    """
        [@0x7ffffff7]:64 bv[63..0]
        r"\[@0x[0-9a-f]+\]"
    """
    match = re.findall(r"\[@0x[0-9a-f]+\]", addr_str)
    assert(len(match) == 1)
    
    match = int(match[0][2:-1], 16)

    # assume 64 bit access
    # TODO: NEED TO FIX THIS maybe with MemoryAccess.getBaseRegoster
    mem = MemoryAccess(match, 8)
    return CTX.getConcreteMemoryValue(mem)

def dump_instruction_accesses(instruction: Instruction):
    print(instruction)
    print("\tRead Registers:", end="")
    for r_reg in instruction.getReadRegisters():
        reg_name_val = (r_reg[0], hex(get_register_value(str(r_reg[0]))))
        print(reg_name_val, end="|")
    print()
    print("\tRead Addresses:", end="")
    for r_addr in instruction.getLoadAccess():
        addr_val = (r_addr[0], hex(get_memory_value(str(r_addr[0]))))
        print(addr_val, end="|")
    print()
    print("\tWritten Registers:", end="")
    for w_reg in instruction.getWrittenRegisters():
        reg_name_val = (w_reg[0], hex(get_register_value(str(w_reg[0]))))
        print(reg_name_val, end="|")
    print()
    print("\tgetStoreAccess:", end="")
    for w_addr in instruction.getStoreAccess():
        addr_val = (w_addr[0], hex(get_memory_value(str(w_addr[0]))))
        print(addr_val, end="|")
    print()

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

    # Load the binary
    binary = loadBinary(CTX)

    # Define a stack
    CTX.setConcreteRegisterValue(CTX.registers.rbp, BASE_STACK)
    CTX.setConcreteRegisterValue(CTX.registers.rsp, BASE_STACK)

    # Define argvs
    # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x100, b'sample/sample_2')
    # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x200, b'hello world')
    # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 0, CPUSIZE.QWORD), BASE_ARGV + 0x100) # argv[0] = 'sample/sample_2'
    # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 8, CPUSIZE.QWORD), BASE_ARGV + 0x200) # argv[1] = 'hello world'
    CTX.setConcreteRegisterValue(CTX.registers.rdi, 2)
    # ctx.setConcreteRegisterValue(ctx.registers.rsi, BASE_ARGV)

    # Let's emulate the binary from the entry point
    print('Starting emulation')
    emulate(CTX, binary.get_symbol('main').value)
    print('Emulation done')

    sys.exit(0)