(define-fun p1_ref!0 () (_ BitVec 8) ((_ extract 31 24) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!1 () (_ BitVec 8) ((_ extract 23 16) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!2 () (_ BitVec 8) ((_ extract 15 8) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!3 () (_ BitVec 8) ((_ extract 7 0) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!4 () (_ BitVec 32) (concat ((_ extract 31 24) (_ bv0 32)) ((_ extract 23 16) (_ bv0 32)) ((_ extract 15 8) (_ bv0 32)) ((_ extract 7 0) (_ bv0 32)))) ; Temporary concatenation reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!5 () (_ BitVec 64) (_ bv4099 64)) ; Program Counter - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p1_ref!6 () (_ BitVec 64) ((_ zero_extend 32) (_ bv5 32))) ; MOV operation - 0x1003: mov eax, 5
(define-fun p1_ref!7 () (_ BitVec 64) (_ bv4104 64)) ; Program Counter - 0x1003: mov eax, 5
(define-fun p1_ref!8 () (_ BitVec 64) ((_ zero_extend 32) (concat p1_ref!0 p1_ref!1 p1_ref!2 p1_ref!3))) ; MOV operation - 0x1008: mov eax, dword ptr [rbp - 4]
(define-fun p1_ref!9 () (_ BitVec 64) (_ bv4107 64)) ; Program Counter - 0x1008: mov eax, dword ptr [rbp - 4]

(define-fun p2_ref!0 () (_ BitVec 8) ((_ extract 31 24) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!1 () (_ BitVec 8) ((_ extract 23 16) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!2 () (_ BitVec 8) ((_ extract 15 8) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!3 () (_ BitVec 8) ((_ extract 7 0) (_ bv0 32))) ; Byte reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!4 () (_ BitVec 32) (concat ((_ extract 31 24) (_ bv0 32)) ((_ extract 23 16) (_ bv0 32)) ((_ extract 15 8) (_ bv0 32)) ((_ extract 7 0) (_ bv0 32)))) ; Temporary concatenation reference - MOV operation - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!5 () (_ BitVec 64) (_ bv4099 64)) ; Program Counter - 0x1000: mov dword ptr [rbp - 4], edi
(define-fun p2_ref!6 () (_ BitVec 64) ((_ zero_extend 32) (concat p2_ref!0 p2_ref!1 p2_ref!2 p2_ref!3))) ; MOV operation - 0x1003: mov eax, dword ptr [rbp - 4]
(define-fun p2_ref!7 () (_ BitVec 64) (_ bv4102 64)) ; Program Counter - 0x1003: mov eax, dword ptr [rbp - 4]


;(assert
;    (not
;        (=>
;            (and
;                (= p1_ref!0 p2_ref!0)
;                (= p1_ref!1 p2_ref!1)
;                (= p1_ref!2 p2_ref!2)
;                (= p1_ref!3 p2_ref!3))
;            (= p2_ref!6 p1_ref!8))))
;(check-sat)

(assert
    (not
        ;(=>
            (and
                (= p1_ref!0 p2_ref!0)
                (= p1_ref!1 p2_ref!1)
                (= p1_ref!2 p2_ref!2)
                (= p1_ref!3 p2_ref!3)
                (= p2_ref!6 p1_ref!8)
            )
        ;)
    )
)
