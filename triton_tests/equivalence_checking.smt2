(declare-fun rax_init () (_ BitVec 64))
(declare-fun rbx_init () (_ BitVec 64))
(declare-fun prog1_ref!0 () (_ BitVec 64))
(declare-fun prog1_ref!1 () (_ BitVec 64))
(declare-fun prog2_ref!0 () (_ BitVec 64))
(declare-fun prog2_ref!1 () (_ BitVec 64))
(define-fun prog1_rax_shared () Bool (= rax_init prog1_ref!0))
(define-fun prog1_rbx_shared () Bool (= rbx_init prog1_ref!1))
(define-fun prog2_rax_shared () Bool (= rax_init prog2_ref!0))
(define-fun prog2_rbx_shared () Bool (= rbx_init prog2_ref!1))
(define-fun prog1_ref!2 () (_ BitVec 64) (bvadd prog1_ref!0 prog1_ref!1)) ; ADD operation - 0x400000: add rax, rbx
(define-fun prog1_ref!3 () (_ BitVec 1) (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor prog1_ref!2 (bvxor prog1_ref!0 prog1_ref!1)))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x400000: add rax, rbx
(define-fun prog1_ref!4 () (_ BitVec 1) ((_ extract 63 63) (bvxor (bvand prog1_ref!0 prog1_ref!1) (bvand (bvxor (bvxor prog1_ref!0 prog1_ref!1) prog1_ref!2) (bvxor prog1_ref!0 prog1_ref!1))))) ; Carry flag - 0x400000: add rax, rbx
(define-fun prog1_ref!5 () (_ BitVec 1) ((_ extract 63 63) (bvand (bvxor prog1_ref!0 (bvnot prog1_ref!1)) (bvxor prog1_ref!0 prog1_ref!2)))) ; Overflow flag - 0x400000: add rax, rbx
(define-fun prog1_ref!6 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog1_ref!2) (_ bv7 8))))) ; Parity flag - 0x400000: add rax, rbx
(define-fun prog1_ref!7 () (_ BitVec 1) ((_ extract 63 63) prog1_ref!2)) ; Sign flag - 0x400000: add rax, rbx
(define-fun prog1_ref!8 () (_ BitVec 1) (ite (= prog1_ref!2 (_ bv0 64)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x400000: add rax, rbx
(define-fun prog1_ref!9 () (_ BitVec 64) (_ bv4194307 64)) ; Program Counter - 0x400000: add rax, rbx
(define-fun prog2_ref!2 () (_ BitVec 64) (bvadd prog2_ref!0 prog2_ref!1)) ; ADD operation - 0x400000: add rax, rbx
(define-fun prog2_ref!3 () (_ BitVec 1) (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor prog2_ref!2 (bvxor prog2_ref!0 prog2_ref!1)))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x400000: add rax, rbx
(define-fun prog2_ref!4 () (_ BitVec 1) ((_ extract 63 63) (bvxor (bvand prog2_ref!0 prog2_ref!1) (bvand (bvxor (bvxor prog2_ref!0 prog2_ref!1) prog2_ref!2) (bvxor prog2_ref!0 prog2_ref!1))))) ; Carry flag - 0x400000: add rax, rbx
(define-fun prog2_ref!5 () (_ BitVec 1) ((_ extract 63 63) (bvand (bvxor prog2_ref!0 (bvnot prog2_ref!1)) (bvxor prog2_ref!0 prog2_ref!2)))) ; Overflow flag - 0x400000: add rax, rbx
(define-fun prog2_ref!6 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!2) (_ bv7 8))))) ; Parity flag - 0x400000: add rax, rbx
(define-fun prog2_ref!7 () (_ BitVec 1) ((_ extract 63 63) prog2_ref!2)) ; Sign flag - 0x400000: add rax, rbx
(define-fun prog2_ref!8 () (_ BitVec 1) (ite (= prog2_ref!2 (_ bv0 64)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x400000: add rax, rbx
(define-fun prog2_ref!9 () (_ BitVec 64) (_ bv4194307 64)) ; Program Counter - 0x400000: add rax, rbx
(define-fun prog2_ref!10 () (_ BitVec 64) (bvadd prog2_ref!2 (_ bv0 64))) ; ADD operation - 0x400002: add rax, 0
(define-fun prog2_ref!11 () (_ BitVec 1) (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor prog2_ref!10 (bvxor prog2_ref!2 (_ bv0 64))))) (_ bv1 1) (_ bv0 1))) ; Adjust flag - 0x400002: add rax, 0
(define-fun prog2_ref!12 () (_ BitVec 1) ((_ extract 63 63) (bvxor (bvand prog2_ref!2 (_ bv0 64)) (bvand (bvxor (bvxor prog2_ref!2 (_ bv0 64)) prog2_ref!10) (bvxor prog2_ref!2 (_ bv0 64)))))) ; Carry flag - 0x400002: add rax, 0
(define-fun prog2_ref!13 () (_ BitVec 1) ((_ extract 63 63) (bvand (bvxor prog2_ref!2 (bvnot (_ bv0 64))) (bvxor prog2_ref!2 prog2_ref!10)))) ; Overflow flag - 0x400002: add rax, 0
(define-fun prog2_ref!14 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) prog2_ref!10) (_ bv7 8))))) ; Parity flag - 0x400002: add rax, 0
(define-fun prog2_ref!15 () (_ BitVec 1) ((_ extract 63 63) prog2_ref!10)) ; Sign flag - 0x400002: add rax, 0
(define-fun prog2_ref!16 () (_ BitVec 1) (ite (= prog2_ref!10 (_ bv0 64)) (_ bv1 1) (_ bv0 1))) ; Zero flag - 0x400002: add rax, 0
(define-fun prog2_ref!17 () (_ BitVec 64) (_ bv4194310 64)) ; Program Counter - 0x400002: add rax, 0
(define-fun eq_0 () Bool(= prog1_ref!2 prog2_ref!10))
(assert (not (=> (and prog1_rax_shared prog1_rbx_shared prog2_rax_shared prog2_rbx_shared) (and eq_0))))
(check-sat)