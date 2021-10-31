#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./src/examples/python/symbolic_emulation_1.py
##  400000: movabs rax, 0x4142434445464748
##          ref!0 = (_ bv4702394921427289928 64) ; MOVABS operation
##          ref!1 = (_ bv4194314 64) ; Program Counter
##
##  40000a: mov rsi, 8
##          ref!2 = (_ bv8 64) ; MOV operation
##          ref!3 = (_ bv4194321 64) ; Program Counter
##
##  400011: mov rdi, 0x10000
##          ref!4 = (_ bv65536 64) ; MOV operation
##          ref!5 = (_ bv4194328 64) ; Program Counter
##
##  400018: mov qword ptr [rdi + rsi*2 + 0x1234], rax
##          ref!6 = ((_ extract 63 56) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!7 = ((_ extract 55 48) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!8 = ((_ extract 47 40) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!9 = ((_ extract 39 32) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!10 = ((_ extract 31 24) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!11 = ((_ extract 23 16) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!12 = ((_ extract 15 8) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!13 = ((_ extract 7 0) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##          ref!15 = (_ bv4194336 64) ; Program Counter
##
##  Display emulated information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  Instruction : mov qword ptr [rdi + rsi*2 + 0x1234], rax
##  Write at    : 0x11244L
##  Content     : 0x41424344L
##  RAX value   : 0x4142434445464748L
##  RSI value   : 0x8L
##  RDI value   : 0x10000L
##
##  Symbolic registers information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  rsi:64 bv[63..0] ref!2 = (_ bv8 64) ; MOV operation
##  rax:64 bv[63..0] ref!0 = (_ bv4702394921427289928 64) ; MOVABS operation
##  rip:64 bv[63..0] ref!15 = (_ bv4194336 64) ; Program Counter
##  rdi:64 bv[63..0] ref!4 = (_ bv65536 64) ; MOV operation
##
##  Symbolic memory information
##  ~~~~~~~~~~~~~~~~~~~~~~~~~~~
##  0x11244L ref!13 = ((_ extract 7 0) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11245L ref!12 = ((_ extract 15 8) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11246L ref!11 = ((_ extract 23 16) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11247L ref!10 = ((_ extract 31 24) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11248L ref!9 = ((_ extract 39 32) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x11249L ref!8 = ((_ extract 47 40) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x1124aL ref!7 = ((_ extract 55 48) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##  0x1124bL ref!6 = ((_ extract 63 56) ((_ extract 63 0) ref!0)) ; byte reference - MOV operation
##
##  Craft symbolic stuffs
##  ~~~~~~~~~~~~~~~~~~~~~
##  Memory at 0x11248 : (concat ((_ extract 7 0) ref!6) ((_ extract 7 0) ref!7) ((_ extract 7 0) ref!8) ((_ extract 7 0) ref!9))
##  Compute memory    : 0x41424344L
##  Register AH       : ((_ extract 15 8) ref!0)
##  Compute  AH       : 0x47L
##

from __future__ import print_function
import sys
sys.path.insert(0, "/usr/lib/python3.8/site-packages")

from triton     import TritonContext, ARCH, Instruction, MemoryAccess, CPUSIZE


# code = [
#     (0x400000, b"\x48\xB8\x48\x47\x46\x45\x44\x43\x42\x41"),     # movabs rax, 0x4142434445464748
#     (0x40000a, b"\x48\xC7\xC6\x08\x00\x00\x00"),                 # mov    rsi, 0x8
#     (0x400011, b"\x48\xC7\xC7\x00\x00\x01\x00"),                 # mov    rdi, 0x10000
#     (0x400018, b"\x48\x89\x84\x77\x34\x12\x00\x00"),             # mov    QWORD PTR [rdi+rsi*2+0x1234], rax
# ]

"""
int main(){
    int a;;
    if(a != 0)
        return a * a;
    else
        return a + 5;
}
"""
code = [
    (0x0000000000001129, b"\xf3\x0f\x1e\xfa"),     # .endbr64 
    (0x000000000000112d, b"\x55"), #      push   %rbp
    (0x000000000000112e, b"\x48\x89\xe5"), #        mov    %rsp,%rbp
    (0x0000000000001131, b"\x83\x7d\xfc\x00"), #     cmpl   $0x0,-0x4(%rbp)
    (0x0000000000001135, b"\x74\x08"), #   je     0x113f <main+22>
    (0x0000000000001137, b"\x8b\x45\xfc"), #        mov    -0x4(%rbp),%eax
    (0x000000000000113a, b"\x0f\xaf\xc0"), #       imul   %eax,%eax
    (0x000000000000113d, b"\xeb\x06"), #   jmp    0x1145 <main+28>
    (0x000000000000113f, b"\x8b\x45\xfc"), #        mov    -0x4(%rbp),%eax
    (0x0000000000001142, b"\x83\xc0\x05"), #        add    $0x5,%eax
    (0x0000000000001145, b"\x5d"), #      pop    %rbp
    (0x0000000000001146, b"\xc3"), #      retq  
]


if __name__ == '__main__':

    Triton = TritonContext()

    # Set the architecture
    Triton.setArchitecture(ARCH.X86_64)

    for (addr, opcode) in code:
        # Build an instruction
        inst = Instruction()

        # Setup opcode
        inst.setOpcode(opcode)

        # Setup Address
        inst.setAddress(addr)

        # Process everything
        Triton.processing(inst)

        # Display instruction
        print(inst)

        # Display symbolic expressions
        for expr in inst.getSymbolicExpressions():
            print('\t', expr)

        print()


    print('Display emulated information')
    print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
    # write = inst.getOperands()[0].getAddress()
    # print('Instruction :', inst.getDisassembly())
    # print('Write at    :', hex(write))
    # print('Content     :', hex(Triton.getConcreteMemoryValue(MemoryAccess(write+4, CPUSIZE.DWORD))))
    # print('RAX value   :', hex(Triton.getConcreteRegisterValue(Triton.registers.rax)))
    # print('RSI value   :', hex(Triton.getConcreteRegisterValue(Triton.registers.rsi)))
    # print('RDI value   :', hex(Triton.getConcreteRegisterValue(Triton.registers.rdi)))


    print()
    print('Symbolic registers information')
    print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
    for k, v in list(Triton.getSymbolicRegisters().items()):
        print(Triton.getRegister(k), v)

    print()
    print('Symbolic memory information')
    print('~~~~~~~~~~~~~~~~~~~~~~~~~~~')
    for k, v in list(Triton.getSymbolicMemory().items()):
        print(hex(k), v)

    print()
    print('Craft symbolic stuffs')
    print('~~~~~~~~~~~~~~~~~~~~~')
    ah  = Triton.getRegisterAst(Triton.registers.ah)
    mem = Triton.getMemoryAst(MemoryAccess(0x11248, 4))
    print('Memory at 0x11248 :', mem)
    print('Compute memory    :', hex(mem.evaluate()))
    print('Register AH       :', ah)
    print('Compute  AH       :', hex(ah.evaluate()))

    sys.exit(0)
