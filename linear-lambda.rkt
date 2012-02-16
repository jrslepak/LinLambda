#lang racket
(require redex)

(define-language Linλ
  (e x
     (q n)
     (if0 e e e)
     (q pair e e)
     (split e (x x) e)
     (q λ (x τ) e)
     (e e)
     (op e e)
     (fix e))
  (v x
     (q n)
     (q pair v v)
     (q λ (x τ)))
  (n integer)
  (op + - *)
  (q lin
     un)
  (p Int
     (p -> p)
     (p * p))
  (τ (q p))
  (Γ ((x τ) ...))
  (E hole
     (if0 E e e)
     (q pair E e)
     (q pair v E)
     (split E (x x) e)
     (E e)
     (v E)
     (op E e)
     (op v E)
     (fix E)))

(define ->β
  (reduction-relation
   Linλ
   [--> (in-hole E (if0 (q 0) e_1 e_2))
        (in-hole E e_1)
        if0-true]
   [--> (in-hole E (if0 e_0 e_1 e_2))
        (in-hole E e_2)
        (side-condition (not (redex-match Linλ (q 0) (term e_0))))
        if0-false]
   [--> (in-hole E (split (q pair e_1 e_2) (x_1 x_2) e_3))
        (in-hole E (var-sub ((x_1 e_1) (x_2 e_2)) e_3))
        split-pair]))


;-------------------------------------------------------------------------------
; utility metafunctions
;-------------------------------------------------------------------------------
(define-metafunction Linλ
  var-sub : (x e) ... e -> e
  ;; base case: operating on a variable
  [(var-sub ((x_0 e_0) ... (x_1 e_1) (x_2 e_2) ...) x_1)  e_1]
  ;; interesting cases: binding forms
  ;; 1. λ which rebinds variable
  [(var-sub ((x_0 e_0) ... (x_param e_param) (x_2 e_2) ...)
            (λ (x_param τ_param) e_body))
   (λ (x_param τ_param) (var-sub ((x_0 e_0) ... (x_2 e_2) ...) e_body))]
  ;; 2. λ which does not rebind variable
  [(var-sub ((x_0 e_0) ... (x_1 e_1) (x_2 e_2) ...)
            (λ (x_param τ_param) e_body))
   (λ (x_param τ_param) ((x_0 e_0) ... (x_1 e_1) (x_2 e_2) ...))]
  ;; 3. split which rebinds both variables (they may appear in either order)
  [(var-sub ((x_0 e_0) ...
             (x_left e_left)
             (x_2 e_2) ...
             (x_right e_right)
             (x_3 e_3) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...
                    (x_3 e_3) ...) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...
                    (x_3 e_3) ...) e_body))]
  [(var-sub ((x_0 e_0) ...
             (x_right e_right)
             (x_2 e_2) ...
             (x_left e_left)
             (x_3 e_3) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...
                    (x_3 e_3) ...) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...
                    (x_3 e_3) ...) e_body))]
  ;; 4. split which rebinds only the left variable
  [(var-sub ((x_0 e_0) ...
             (x_left e_left)
             (x_2 e_2) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...
                    (x_2 e_2)) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2)) e_body))]
  ;; 5. split which rebinds only the right variable
  [(var-sub ((x_0 e_0) ...
             (x_right e_right)
             (x_2 e_2) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...
                    (x_2 e_2)) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2)) e_body))]



;-------------------------------------------------------------------------------
; ->β tests
;-------------------------------------------------------------------------------
;; if0-true
(test--> ->β (term (if0 (un 0) (un 4) (un 2))) (term (un 4)))
;; if0-false
(test--> ->β (term (if0 (un 3) (un 4) (un 2))) (term (un 2)))
