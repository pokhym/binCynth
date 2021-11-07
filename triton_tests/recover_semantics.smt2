(define-fun ref!3 () (_ BitVec 64) (_ bv4702394921427289928 64)) ; MOVABS operation - 0x400000: movabs rax, 0x4142434445464748
(define-fun ref!4 () (_ BitVec 64) (_ bv4194314 64)) ; Program Counter - 0x400000: movabs rax, 0x4142434445464748

(define-fun ref!5 () (_ BitVec 64) (_ bv8 64)) ; MOV operation - 0x40000a: mov rsi, 8
(define-fun ref!6 () (_ BitVec 64) (_ bv4194321 64)) ; Program Counter - 0x40000a: mov rsi, 8

(define-fun ref!7 () (_ BitVec 64) (_ bv65536 64)) ; MOV operation - 0x400011: mov rdi, 0x10000
(define-fun ref!8 () (_ BitVec 64) (_ bv4194328 64)) ; Program Counter - 0x400011: mov rdi, 0x10000

(define-fun ref!9 () (_ BitVec 64) ((_ zero_extend 32) (bvmul ((_ extract 31 0) ref!3) ((_ extract 31 0) ref!3)))) ; IMUL operation - 0x400014: imul eax, eax
(define-fun ref!10 () (_ BitVec 1) (ite (= ((_ sign_extend 32) (bvmul ((_ extract 31 0) ref!3) ((_ extract 31 0) ref!3))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) ref!3)) ((_ sign_extend 32) ((_ extract 31 0) ref!3)))) (_ bv0 1) (_ bv1 1))) ; Carry flag - 0x400014: imul eax, eax
(define-fun ref!11 () (_ BitVec 1) (ite (= ((_ sign_extend 32) (bvmul ((_ extract 31 0) ref!3) ((_ extract 31 0) ref!3))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) ref!3)) ((_ sign_extend 32) ((_ extract 31 0) ref!3)))) (_ bv0 1) (_ bv1 1))) ; Overflow flag - 0x400014: imul eax, eax
(define-fun ref!12 () (_ BitVec 64) (_ bv4194327 64)) ; Program Counter - 0x400014: imul eax, eax

(define-fun ref!13 () (_ BitVec 8) ((_ extract 63 56) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!14 () (_ BitVec 8) ((_ extract 55 48) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!15 () (_ BitVec 8) ((_ extract 47 40) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!16 () (_ BitVec 8) ((_ extract 39 32) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!17 () (_ BitVec 8) ((_ extract 31 24) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!18 () (_ BitVec 8) ((_ extract 23 16) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!19 () (_ BitVec 8) ((_ extract 15 8) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!20 () (_ BitVec 8) ((_ extract 7 0) ref!9)) ; Byte reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!21 () (_ BitVec 64) (concat ((_ extract 63 56) ref!9) ((_ extract 55 48) ref!9) ((_ extract 47 40) ref!9) ((_ extract 39 32) ref!9) ((_ extract 31 24) ref!9) ((_ extract 23 16) ref!9) ((_ extract 15 8) ref!9) ((_ extract 7 0) ref!9))) ; Temporary concatenation reference - MOV operation - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax
(define-fun ref!22 () (_ BitVec 64) (_ bv4194339 64)) ; Program Counter - 0x40001b: mov qword ptr [rdi + rsi*2 + 0x1234], rax


(declare-fun asdf () (_ BitVec 64))

(assert (= asdf ref!9))
(check-sat)
(get-model)