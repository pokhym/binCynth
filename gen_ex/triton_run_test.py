# from __future__ import print_function
# from triton     import *

# import ctypes
# import random
# import string
# import sys
# import lief
# import os
# import platform

# tc = TritonContext()
# tc.setArchitecture(ARCH.X86_64)

# def load_binary(filename):
#         """Load in memory every opcode from an elf program."""
#         #lief.Logger.disable()
#         binary = lief.parse(filename)
#         phdrs  = binary.segments
#         for phdr in phdrs:
#             size   = phdr.physical_size
#             vaddr  = phdr.virtual_address
#             tc.setConcreteMemoryAreaValue(vaddr, phdr.content)

# # def test_defcamp_2015(self):
# #         """Load binary, self.Triton.setup environment and solve challenge with sym eval."""
# #         # Load the binary
# #         binary_file = os.path.join(os.path.dirname(__file__), "misc", "defcamp-2015-r100.bin")
# #         self.load_binary(binary_file)

# #         # Define a fake stack
# #         self.Triton.setConcreteRegisterValue(self.Triton.registers.rbp, 0x7fffffff)
# #         self.Triton.setConcreteRegisterValue(self.Triton.registers.rsp, 0x6fffffff)

# #         # Define an user input
# #         self.Triton.setConcreteRegisterValue(self.Triton.registers.rdi, 0x10000000)

# #         # Symbolize user inputs (30 bytes)
# #         for index in range(30):
# #             self.Triton.symbolizeMemory(MemoryAccess(0x10000000+index, CPUSIZE.BYTE))

# #         # Emulate from the verification function
# #         solution = self.emulate(0x4006FD)
# #         self.assertEqual(solution, 'Code_Talkers')

# load_binary("/home/user/pysynth/gen_ex/empty_main")

# # Define a fake stack
# tc.setConcreteRegisterValue(tc.registers.rbp, 0x7fffffff)
# tc.setConcreteRegisterValue(tc.registers.rsp, 0x6fffffff)

# # Define an user input
# tc.setConcreteRegisterValue(tc.registers.rdi, 0x10000000)

# astCtxt = tc.getAstContext()
# pc = 0x1040
# while pc:
#     # Fetch opcode
#     opcode = tc.getConcreteMemoryAreaValue(pc, 16)

#     # Create the Triton instruction
#     instruction = Instruction()
#     instruction.setOpcode(opcode)
#     instruction.setAddress(pc)

#     # Process
#     tc.processing(instruction)
    
#     print(instruction)
#     print('    ---------------')
#     print('    Is memory read :', instruction.isMemoryRead())
#     print('    Is memory write:', instruction.isMemoryWrite())
#     print('    ---------------')
#     for op in instruction.getOperands():
#         print('    Operand:', op)
#         if op.getType() == OPERAND.MEM:
#             print('    - segment :', op.getSegmentRegister())
#             print('    - base    :', op.getBaseRegister())
#             print('    - index   :', op.getIndexRegister())
#             print('    - scale   :', op.getScale())
#             print('    - disp    :', op.getDisplacement())
#         print('    ---------------')

#     print()

#     pc = tc.getConcreteRegisterValue(tc.registers.rip)


from __future__ import print_function
from triton     import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE

import sys
import os

# Script options
TARGET = "/home/user/pysynth/gen_ex/empty_main" # os.path.join(os.path.dirname(__file__), 'samples/sample_2')
# LIBC   = os.path.join(os.path.dirname(__file__), 'samples/libc.so.6')

# Memory mapping
BASE_ARGV  = 0x10000000
BASE_STACK = 0x7fffffff
BASE_LIBC  = 0x80000008


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
        print(instruction)
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

    # # Map the libc into the memory
    # libc  = lief.parse(LIBC)
    # phdrs = libc.segments
    # for phdr in phdrs:
    #     size   = phdr.physical_size
    #     vaddr  = BASE_LIBC + phdr.virtual_address
    #     print('Loading 0x%06x - 0x%06x' %(vaddr, vaddr + size))
    #     ctx.setConcreteMemoryAreaValue(vaddr, phdr.content)

    # Functions that you want to bind
    # let_bind = [
    #     "strlen",
    #     # ...
    # ]

    relocations = [x for x in binary.pltgot_relocations]
    relocations.extend([x for x in binary.dynamic_relocations])

    # Fill the plt/got
    for rel in relocations:
        symbolName = rel.symbol.name
        symbolRelo = rel.address
        # if symbolName in let_bind:
        #     print('Hooking %s' %(symbolName))
        #     libc_sym_addr = libc.get_symbol(symbolName).value
        #     ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), BASE_LIBC + libc_sym_addr)

    return binary


if __name__ == '__main__':
    # Set the architecture
    ctx = TritonContext(ARCH.X86_64)

    # Set a symbolic optimization mode
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    # Load the binary
    binary = loadBinary(ctx)

    # Define a stack
    ctx.setConcreteRegisterValue(ctx.registers.rbp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.rsp, BASE_STACK)

    # Define argvs
    # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x100, b'sample/sample_2')
    # ctx.setConcreteMemoryAreaValue(BASE_ARGV + 0x200, b'hello world')
    # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 0, CPUSIZE.QWORD), BASE_ARGV + 0x100) # argv[0] = 'sample/sample_2'
    # ctx.setConcreteMemoryValue(MemoryAccess(BASE_ARGV + 8, CPUSIZE.QWORD), BASE_ARGV + 0x200) # argv[1] = 'hello world'
    ctx.setConcreteRegisterValue(ctx.registers.rdi, 2)
    # ctx.setConcreteRegisterValue(ctx.registers.rsi, BASE_ARGV)

    # Let's emulate the binary from the entry point
    print('Starting emulation')
    emulate(ctx, binary.get_symbol('main').value)
    print('Emulation done')

    sys.exit(0)