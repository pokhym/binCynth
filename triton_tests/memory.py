from triton import TritonContext, Instruction, ARCH, MemoryAccess, AST_REPRESENTATION


code1 = [
    (0x1000, b"\x89\x7D\xFC"),  # mov DWORD PTR [rbp-0x4],edi
    (0x1003, b"\x8B\x45\xFC")   # mov    eax,DWORD PTR [rbp-0x4]
]

ctx = TritonContext()
ctx.setArchitecture(ARCH.X86_64)
ctx.enableSymbolicEngine(True)
ctx.setConcreteRegisterValue(ctx.getRegister('rbp'), 0x7ffffff)
# getSymbolicRegisters()
rr = ctx.symbolizeRegister(ctx.getRegister('esp'), 'espsym')
r = ctx.symbolizeRegister(ctx.getRegister('edi'), 'edisym')
print(ctx.isRegisterSymbolized(ctx.getRegister('edi')))
# for i in range(100):
#     ctx.setConcreteMemoryValue(0x7ffffff - i, 0xde)
#     ctx.setConcreteMemoryValue(0x7ffffff + i, 0xbe)

# SymbolicVariable symbo lizeMemory(MemoryAccess mem, string symVarAlias)
a = ctx.symbolizeMemory(MemoryAccess(0x7ffffff - 4, 4), "-4")
b = ctx.symbolizeMemory(MemoryAccess(0x7ffffff - 8, 4), "-8")
c = ctx.symbolizeMemory(MemoryAccess(0x7ffffff - 12, 4), "-12")
d = ctx.symbolizeMemory(MemoryAccess(0x7ffffff - 16, 4), "-16")
print(ctx.isMemorySymbolized(0x7ffffff - 4))

# ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

for (addr, opcode) in code1:
    inst = Instruction()
    inst.setOpcode(opcode)
    inst.setAddress(addr)
    ctx.processing(inst)
    for expr in inst.getSymbolicExpressions():
            print(expr)
    print("###", ctx.getSymbolicMemory(0x7ffffff - 4))

for i in range(6):
    print(hex(ctx.getConcreteMemoryValue(0x7ffffff - i)))
    print(hex(ctx.getConcreteMemoryValue(0x7ffffff + i)))

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
