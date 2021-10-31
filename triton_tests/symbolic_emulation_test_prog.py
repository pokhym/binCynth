#!/usr/bin/env python3
## -*- coding: utf-8 -*-
##
## 0x1129: endbr64
##          (define-fun ref!0 () (_ BitVec 64) (_ bv4397 64)) ; Program Counter - 0x1129: endbr64
## 
## 0x112d: push rbp
##          (define-fun ref!1 () (_ BitVec 64) (bvsub (_ bv0 64) (_ bv8 64))) ; Stack alignment - 0x112d: push rbp
##          (define-fun ref!2 () (_ BitVec 8) ((_ extract 63 56) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!3 () (_ BitVec 8) ((_ extract 55 48) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!4 () (_ BitVec 8) ((_ extract 47 40) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!5 () (_ BitVec 8) ((_ extract 39 32) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!6 () (_ BitVec 8) ((_ extract 31 24) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!7 () (_ BitVec 8) ((_ extract 23 16) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!8 () (_ BitVec 8) ((_ extract 15 8) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!9 () (_ BitVec 8) ((_ extract 7 0) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!10 () (_ BitVec 64) (concat ((_ extract 63 56) (_ bv0 64)) ((_ extract 55 48) (_ bv0 64)) ((_ extract 47 40) (_ bv0 64)) ((_ extract 39 32) (_ bv0 64)) ((_ extract 31 24) (_ bv0 64)) ((_ extract 23 16) (_ bv0 64)) ((_ extract 15 8) (_ bv0 64)) ((_ extract 7 0) (_ bv0 64)))) ; Temporary concatenation reference - PUSH operation - 0x112d: push rbp
##          (define-fun ref!11 () (_ BitVec 64) (_ bv4398 64)) ; Program Counter - 0x112d: push rbp
## 
## 0x112e: mov rbp, rsp
##          (define-fun ref!12 () (_ BitVec 64) ref!1) ; MOV operation - 0x112e: mov rbp, rsp
##          (define-fun ref!13 () (_ BitVec 64) (_ bv4401 64)) ; Program Counter - 0x112e: mov rbp, rsp
## 
## 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!14 () (_ BitVec 32) (bvsub (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) (_ bv0 32))) ; CMP operation - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!15 () (_ BitVec 1) (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor ref!14 (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) (_ bv0 32))))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!16 () (_ BitVec 1) ((_ extract 31 31) (bvxor (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) (bvxor (_ bv0 32) ref!14)) (bvand (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) ref!14) (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) (_ bv0 32)))))) ; Carry flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!17 () (_ BitVec 1) ((_ extract 31 31) (bvand (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) (_ bv0 32)) (bvxor (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)) ref!14)))) ; Overflow flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!18 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!14) (_ bv7 8))))) ; Parity flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!19 () (_ BitVec 1) ((_ extract 31 31) ref!14)) ; Sign flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!20 () (_ BitVec 1) (ite (= ref!14 (_ bv0 32)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x1131: cmp dword ptr [rbp - 4], 0
##          (define-fun ref!21 () (_ BitVec 64) (_ bv4405 64)) ; Program Counter - 0x1131: cmp dword ptr [rbp - 4], 0
## 
## 0x1135: je 0x113f
##          (define-fun ref!22 () (_ BitVec 64) (ite (= ref!20 (_ bv1 1)) (_ bv4415 64) (_ bv4407 64))) ; Program Counter - 0x1135: je 0x113f
## 
## 0x1137: mov eax, dword ptr [rbp - 4]
##          (define-fun ref!23 () (_ BitVec 64) ((_ zero_extend 32) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)))) ; MOV operation - 0x1137: mov eax, dword ptr [rbp - 4]
##          (define-fun ref!24 () (_ BitVec 64) (_ bv4410 64)) ; Program Counter - 0x1137: mov eax, dword ptr [rbp - 4]
## 
## 0x113a: imul eax, eax
##          (define-fun ref!25 () (_ BitVec 64) ((_ zero_extend 32) (bvmul ((_ extract 31 0) ref!23) ((_ extract 31 0) ref!23)))) ; IMUL operation - 0x113a: imul eax, eax
##          (define-fun ref!26 () (_ BitVec 1) (ite (= ((_ sign_extend 32) (bvmul ((_ extract 31 0) ref!23) ((_ extract 31 0) ref!23))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) ref!23)) ((_ sign_extend 32) ((_ extract 31 0) ref!23)))) (_ bv0 1) (_ bv1 1))) ; Carry flag - 0x113a: imul eax, eax
##          (define-fun ref!27 () (_ BitVec 1) (ite (= ((_ sign_extend 32) (bvmul ((_ extract 31 0) ref!23) ((_ extract 31 0) ref!23))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) ref!23)) ((_ sign_extend 32) ((_ extract 31 0) ref!23)))) (_ bv0 1) (_ bv1 1))) ; Overflow flag - 0x113a: imul eax, eax
##          (define-fun ref!28 () (_ BitVec 64) (_ bv4413 64)) ; Program Counter - 0x113a: imul eax, eax
## 
## 0x113d: jmp 0x1145
##          (define-fun ref!29 () (_ BitVec 64) (_ bv4421 64)) ; Program Counter - 0x113d: jmp 0x1145
## 
## 0x113f: mov eax, dword ptr [rbp - 4]
##          (define-fun ref!30 () (_ BitVec 64) ((_ zero_extend 32) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8)))) ; MOV operation - 0x113f: mov eax, dword ptr [rbp - 4]
##          (define-fun ref!31 () (_ BitVec 64) (_ bv4418 64)) ; Program Counter - 0x113f: mov eax, dword ptr [rbp - 4]
## 
## 0x1142: add eax, 5
##          (define-fun ref!32 () (_ BitVec 64) ((_ zero_extend 32) (bvadd ((_ extract 31 0) ref!30) (_ bv5 32)))) ; ADD operation - 0x1142: add eax, 5
##          (define-fun ref!33 () (_ BitVec 1) (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor ((_ extract 31 0) ref!32) (bvxor ((_ extract 31 0) ref!30) (_ bv5 32))))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x1142: add eax, 5
##          (define-fun ref!34 () (_ BitVec 1) ((_ extract 31 31) (bvxor (bvand ((_ extract 31 0) ref!30) (_ bv5 32)) (bvand (bvxor (bvxor ((_ extract 31 0) ref!30) (_ bv5 32)) ((_ extract 31 0) ref!32)) (bvxor ((_ extract 31 0) ref!30) (_ bv5 32)))))) ; Carry flag - 0x1142: add eax, 5
##          (define-fun ref!35 () (_ BitVec 1) ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) ref!30) (bvnot (_ bv5 32))) (bvxor ((_ extract 31 0) ref!30) ((_ extract 31 0) ref!32))))) ; Overflow flag - 0x1142: add eax, 5
##          (define-fun ref!36 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv7 8))))) ; Parity flag - 0x1142: add eax, 5
##          (define-fun ref!37 () (_ BitVec 1) ((_ extract 31 31) ref!32)) ; Sign flag - 0x1142: add eax, 5
##          (define-fun ref!38 () (_ BitVec 1) (ite (= ((_ extract 31 0) ref!32) (_ bv0 32)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x1142: add eax, 5
##          (define-fun ref!39 () (_ BitVec 64) (_ bv4421 64)) ; Program Counter - 0x1142: add eax, 5
## 
## 0x1145: pop rbp
##          (define-fun ref!40 () (_ BitVec 64) (concat ref!2 ref!3 ref!4 ref!5 ref!6 ref!7 ref!8 ref!9)) ; POP operation - 0x1145: pop rbp
##          (define-fun ref!41 () (_ BitVec 64) (bvadd ref!1 (_ bv8 64))) ; Stack alignment - 0x1145: pop rbp
##          (define-fun ref!42 () (_ BitVec 64) (_ bv4422 64)) ; Program Counter - 0x1145: pop rbp
## 
## 0x1146: ret
##          (define-fun ref!43 () (_ BitVec 64) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8))) ; Program Counter - 0x1146: ret
##          (define-fun ref!44 () (_ BitVec 64) (bvadd ref!41 (_ bv8 64))) ; Stack alignment - 0x1146: ret
## 
## Display emulated information
## ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
## 
## Symbolic registers information
## ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
## of:1 bv[0..0] (define-fun ref!35 () (_ BitVec 1) ((_ extract 31 31) (bvand (bvxor ((_ extract 31 0) ref!30) (bvnot (_ bv5 32))) (bvxor ((_ extract 31 0) ref!30) ((_ extract 31 0) ref!32))))) ; Overflow flag - 0x1142: add eax, 5
## af:1 bv[0..0] (define-fun ref!33 () (_ BitVec 1) (ite (= (_ bv16 32) (bvand (_ bv16 32) (bvxor ((_ extract 31 0) ref!32) (bvxor ((_ extract 31 0) ref!30) (_ bv5 32))))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x1142: add eax, 5
## sf:1 bv[0..0] (define-fun ref!37 () (_ BitVec 1) ((_ extract 31 31) ref!32)) ; Sign flag - 0x1142: add eax, 5
## rip:64 bv[63..0] (define-fun ref!43 () (_ BitVec 64) (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8))) ; Program Counter - 0x1146: ret
## rsp:64 bv[63..0] (define-fun ref!44 () (_ BitVec 64) (bvadd ref!41 (_ bv8 64))) ; Stack alignment - 0x1146: ret
## pf:1 bv[0..0] (define-fun ref!36 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!32) (_ bv7 8))))) ; Parity flag - 0x1142: add eax, 5
## rbp:64 bv[63..0] (define-fun ref!40 () (_ BitVec 64) (concat ref!2 ref!3 ref!4 ref!5 ref!6 ref!7 ref!8 ref!9)) ; POP operation - 0x1145: pop rbp
## zf:1 bv[0..0] (define-fun ref!38 () (_ BitVec 1) (ite (= ((_ extract 31 0) ref!32) (_ bv0 32)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x1142: add eax, 5
## cf:1 bv[0..0] (define-fun ref!34 () (_ BitVec 1) ((_ extract 31 31) (bvxor (bvand ((_ extract 31 0) ref!30) (_ bv5 32)) (bvand (bvxor (bvxor ((_ extract 31 0) ref!30) (_ bv5 32)) ((_ extract 31 0) ref!32)) (bvxor ((_ extract 31 0) ref!30) (_ bv5 32)))))) ; Carry flag - 0x1142: add eax, 5
## rax:64 bv[63..0] (define-fun ref!32 () (_ BitVec 64) ((_ zero_extend 32) (bvadd ((_ extract 31 0) ref!30) (_ bv5 32)))) ; ADD operation - 0x1142: add eax, 5
## 
## Symbolic memory information
## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
## 0xfffffffffffffff8 (define-fun ref!9 () (_ BitVec 8) ((_ extract 7 0) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffff9 (define-fun ref!8 () (_ BitVec 8) ((_ extract 15 8) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffffa (define-fun ref!7 () (_ BitVec 8) ((_ extract 23 16) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffffb (define-fun ref!6 () (_ BitVec 8) ((_ extract 31 24) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffffc (define-fun ref!5 () (_ BitVec 8) ((_ extract 39 32) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffffd (define-fun ref!4 () (_ BitVec 8) ((_ extract 47 40) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xfffffffffffffffe (define-fun ref!3 () (_ BitVec 8) ((_ extract 55 48) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 0xffffffffffffffff (define-fun ref!2 () (_ BitVec 8) ((_ extract 63 56) (_ bv0 64))) ; Byte reference - PUSH operation - 0x112d: push rbp
## 
## Craft symbolic stuffs
## ~~~~~~~~~~~~~~~~~~~~~
## Memory at 0x11248 : (concat (_ bv0 8) (_ bv0 8) (_ bv0 8) (_ bv0 8))
## Compute memory    : 0x0
## Register AH       : ((_ extract 15 8) ref!32)
## Compute  AH       : 0x0

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
