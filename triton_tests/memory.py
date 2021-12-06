from triton import TritonContext, Instruction, ARCH, MemoryAccess


code1 = [
    (0x1000, b"\x89\x7D\xFC"),  # mov DWORD PTR [rbp-0x4],edi
    (0x1003, b"\x8B\x45\xFC")   # mov    eax,DWORD PTR [rbp-0x4]
]

ctx = TritonContext()
ctx.setArchitecture(ARCH.X86_64)
ctx.setConcreteRegisterValue(ctx.getRegister('rbp'), 0x7ffffff)

for (addr, opcode) in code1:
    inst = Instruction()
    inst.setOpcode(opcode)
    inst.setAddress(addr)
    ctx.processing(inst)
    for expr in inst.getSymbolicExpressions():
            print(expr)

print()
print("###########################################")
print("Symbolic Memory")
for k, v in list(ctx.getSymbolicMemory().items()):
    print(hex(k), v)
print("###########################################")
print()

print()
print("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
print()

ctx = TritonContext()
ctx.setArchitecture(ARCH.X86_64)
ctx.setConcreteRegisterValue(ctx.getRegister('rbp'), 0x7ffffff)

code2 = [
    (0x1000, b"\x89\x7D\xFC"),          # mov    DWORD PTR [rbp-0x4],edi
    (0x1003, b"\xB8\x05\x00\x00\x00"),  # mov    eax,0x5
    (0x1008, b"\x8B\x45\xFC")           # mov    eax,DWORD PTR [rbp-0x4]
]

for (addr, opcode) in code2:
    inst = Instruction()
    inst.setOpcode(opcode)
    inst.setAddress(addr)
    ctx.processing(inst)
    for expr in inst.getSymbolicExpressions():
            print(expr)

print()
print("###########################################")
print("Symbolic Memory")
for k, v in list(ctx.getSymbolicMemory().items()):
    print(hex(k), v)
print("###########################################")
print()
