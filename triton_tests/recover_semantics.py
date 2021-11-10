from __future__ import print_function
# import sys
# sys.path.insert(0, "/usr/lib/python3.8/site-packages")
from triton import *

# Initialize Triton
ctx = TritonContext()
# Set to x86 with 64 Bits
ctx.setArchitecture(ARCH.X86_64)
# Print using PYTHON syntax default SMT2
ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

# create symbolic registers for RAX and RBX
rax = ctx.symbolizeRegister(ctx.registers.rax)
rbx = ctx.symbolizeRegister(ctx.registers.rbx)

# Note that RAX and RBX are equivalent of ref_0 and ref_1 as they were initialized that way
print("RAX", rax, "RAX ID", "ref_" + str(rax.getId()))
print("RBX", rbx, "RAX ID", "ref_" + str(rbx.getId()))

# Create an instruction that begins at a specific address
inst = Instruction()
inst.setOpcode(b"\x48\x01\xD8") # add rax, rbx
inst.setAddress(0x400000)

# If not symbolic can concretize values here
# inst.updateContext(Register(REG.RAX, 0x4444444455555555))
# inst.updateContext(Register(REG.RBX, 0x1111111122222222))

# Execute instruction
ctx.processing(inst)

# Print the instruction
print(inst)

# For everything that was updated in the instruction print the symbolic expresssions
for expression in inst.getSymbolicExpressions():
    print("\t", expression)
