#lang racket
(require redex)

(define-language Linλ
  ; expressions
  (e (q n)             ; everything that will be a value must be annotated with
     (q pair e e)      ; a type qualifier, e.g. (lin 4) for a numeric 4 which
     (q λ (x τ) e)     ; must be used exactly once
     (if0 e e e)       ; conditional execution
     (split e (x x) e) ; bind both elements of a pair at once
     (e e)             ; function application
     (op e e)          ; primitive operations
     (fix e)           ; fixpoint operator
     x)                ; variable
  ; value forms
  (v x
     (q n)
     (q pair v v)
     (q λ (x τ) e))
  (n integer)
  (x variable-not-otherwise-mentioned)
  (op + - *)
  ; type qualifiers
  (q lin               ; linear: must use exactly once on each control path
     un)               ; unrestricted: can use any number of times
  ; pre-types
  (p Int               ; integer, the only base type
     (p -> p)          ; function
     (p * p))          ; pair
  ; full types, i.e. types with qualifiers
  (τ (q p))
  ; evaluation contexts
  (E hole
     (if0 E e e)       ; don't look down the branches -- just eval the condition
     (q pair E e)      ; evaluate elements left to right
     (q pair v E)
     (split E (x x) e) ; evaluate the pair to be bound
     (E e)             ; reduce "function" side to a value before applying it
     ; must not include (v E)
     ; (fix e) ↦ (e (fix e)) does not play nice w/ call-by-value
     (op E e)          ; evaluate arguments left to right
     (op v E))
  ; (var type) environments -- for type checking, not part of surface syntax
  (Γ ((x τ) ...)))

;; The reduction semantics essentially ignores types -- it is assumed
;; that typechecking happens before evaluation. This could be rewritten
;; to work via type erasure, but knowing about linearity is potentially
;; useful at a later stage.
(define ->β
  (reduction-relation
   Linλ
   [--> (in-hole E (if0 (q 0) e_1 e_2))
        (in-hole E e_1)
        if0-true]
   [--> (in-hole E (if0 v e_1 e_2))
        (in-hole E e_2)
        (side-condition (not (redex-match Linλ (q 0) (term v))))
        if0-false]
   [--> (in-hole E (split (q pair e_1 e_2) (x_1 x_2) e_3))
        (in-hole E (var-sub ((x_1 e_1) (x_2 e_2)) e_3))
        split-pair]
   [--> (in-hole E ((q λ (x τ) e_body) e_arg))
        (in-hole E (var-sub ((x e_arg)) e_body))
        app-name]
   [--> (in-hole E (+ (q_1 n_1) (q_2 n_2)))
        (in-hole E (un ,(+ (term n_1) (term n_2))))
        op+]
   [--> (in-hole E (- (q_1 n_1) (q_2 n_2)))
        (in-hole E (un ,(- (term n_1) (term n_2))))
        op-]
   [--> (in-hole E (* (q_1 n_1) (q_2 n_2)))
        (in-hole E (un ,(* (term n_1) (term n_2))))
        op*]
   [--> (in-hole E (fix e))
        (in-hole E (e (fix e)))
        fixpoint]
   ))


;-------------------------------------------------------------------------------
; utility metafunctions
;-------------------------------------------------------------------------------
(define-metafunction Linλ
  var-sub : ((x e) ...) e -> e
  
  ;; base cases: operating on a variable or literal
  ;; 1. a variable from the substitution list
  [(var-sub ((x_0 e_0) ... (x_1 e_1) (x_2 e_2) ...) x_1)  e_1]
  ;; 2. a variable not in the substitution list
  [(var-sub ((x_0 e_0) ...) x_1)  x_1]
  ;; 3. base value literal
  [(var-sub ((x_0 e_0) ...)
            (q n))
   (q n)]
  
  
  ;; interesting recursive cases: binding forms
  ;; 1. λ which rebinds variable
  [(var-sub ((x_0 e_0) ... (x_param e_param) (x_2 e_2) ...)
            (q λ (x_param τ_param) e_body))
   (q λ (x_param τ_param) (var-sub ((x_0 e_0) ... (x_2 e_2) ...) e_body))]
  ;; 2. λ which does not rebind variable
  [(var-sub ((x_0 e_0) ...)
            (q λ (x_param τ_param) e_body))
   (q λ (x_param τ_param) (var-sub ((x_0 e_0) ...) e_body))]
  
  ;; 3. split which rebinds both variables (they may appear in either order)
  [(var-sub ((x_0 e_0) ...
             (x_left e_left)
             (x_2 e_2) ...
             (x_right e_right)
             (x_3 e_3) ...)
            (split e_pair (x_left x_right) e_body))
   ;; must respect new bindings in e_body but old bindings in e_pair
   (split (var-sub ((x_0 e_0) ...
                    (x_left e_left)
                    (x_2 e_2) ...
                    (x_right e_right)
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
                    (x_right e_right)
                    (x_2 e_2) ...
                    (x_left e_left)
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
                    (x_left e_left)
                    (x_2 e_2) ...) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...) e_body))]
  ;; 5. split which rebinds only the right variable
  [(var-sub ((x_0 e_0) ...
             (x_right e_right)
             (x_2 e_2) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...
                    (x_right e_right)
                    (x_2 e_2) ...) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...
                    (x_2 e_2) ...) e_body))]
  ;; 6. split which rebinds neither variable
  [(var-sub ((x_0 e_0) ...)
            (split e_pair (x_left x_right) e_body))
   (split (var-sub ((x_0 e_0) ...) e_pair)
          (x_left x_right)
          (var-sub ((x_0 e_0) ...) e_body))]
  
  ;; uninteresting recursive cases: if0, pair, app, op, fix, literal
  ;; just pass through to the subexpressions
  ;; if0
  [(var-sub ((x_0 e_0) ...)
            (if0 e_ante e_cons e_alt))
   (if0 (var-sub ((x_0 e_0) ...) e_ante)
        (var-sub ((x_0 e_0) ...) e_cons)
        (var-sub ((x_0 e_0) ...) e_alt))]
  ;; pair
  [(var-sub ((x_0 e_0) ...)
            (q pair e_left e_right))
   (q pair
      (var-sub ((x_0 e_0) ...) e_left)
      (var-sub ((x_0 e_0) ...) e_right))]
  ;; app
  [(var-sub ((x_0 e_0) ...)
            (e_fun e_arg))
   ((var-sub ((x_0 e_0) ...) e_fun)
    (var-sub ((x_0 e_0) ...) e_arg))]
  ;; op
  [(var-sub ((x_0 e_0) ...)
            (op e_left e_right))
   (op (var-sub ((x_0 e_0) ...) e_left)
       (var-sub ((x_0 e_0) ...) e_right))]
  ;; fix
  [(var-sub ((x_0 e_0) ...)
            (fix e_fun))
   (fix (var-sub ((x_0 e_0) ...) e_fun))]
  )


;-------------------------------------------------------------------------------
; var-sub tests
;-------------------------------------------------------------------------------
(test-equal (term (var-sub ((x (un 4)) (y (un 1))) x))
            (term (un 4)))
(test-equal (term (var-sub ((x (un 4)) (y (un 1))) z))
            (term z))

(test-equal (term (var-sub ((x (un 4)) (y (un 1))) (un λ (x (lin Int)) x)))
            (term (un λ (x (lin Int)) x)))
(test-equal (term (var-sub ((x (un 4)) (y (un 1))) (un λ (x (lin Int)) y)))
            (term (un λ (x (lin Int)) (un 1))))
(test-equal (term (var-sub ((x (un 4)) (y (un 1))) (un λ (y (lin Int)) x)))
            (term (un λ (y (lin Int)) (un 4))))

(test-equal (term (var-sub ((x (un 3)) (y (un 4))) (split x (y z) y)))
            (term (split (un 3) (y z) y)))
(test-equal (term (var-sub ((x (un 3)) (y (un 4))) (split y (y z) x)))
            (term (split (un 4) (y z) (un 3))))
(test-equal (term (var-sub ((z (un 3)) (y (un 4))) (split z (y z) z)))
            (term (split (un 3) (y z) z)))

(test-equal (term (var-sub ((z (un 3)) (x (un 0))) (if0 x y z)))
            (term (if0 (un 0) y (un 3))))
(test-equal (term (var-sub ((z (un 3)) (x (un 0))) (if0 x (un λ (x (un Int)) z) z)))
            (term (if0 (un 0) (un λ (x (un Int)) (un 3)) (un 3))))
(test-equal (term (var-sub ((z (un 3)) (x (un 0))) (if0 x (un λ (x (un Int)) x) z)))
            (term (if0 (un 0) (un λ (x (un Int)) x) (un 3))))

(test-equal (term (var-sub ((z (un 3)) (x (un 0))) (lin pair (un λ (x (un Int)) x) z)))
            (term (lin pair (un λ (x (un Int)) x) (un 3))))

(test-equal (term (var-sub ((z (un 3)) (x (un 0))) ((lin λ (x (lin Int)) (+ z x)) x)))
            (term ((lin λ (x (lin Int)) (+ (un 3) x)) (un 0))))
(test-equal (term (var-sub ((x (lin 4)) (z (lin λ (x (lin Int)) (+ x (lin 4))))) (z x)))
            (term ((lin λ (x (lin Int)) (+ x (lin 4))) (lin 4))))

(test-equal (term (var-sub ((z (un 3)) (x (un 0))) (+ z ((lin λ (x (lin Int)) (+ z x)) x))))
            (term (+ (un 3) ((lin λ (x (lin Int)) (+ (un 3) x)) (un 0)))))

(test-equal (term (var-sub ((x (un 3))) (fix (un λ (f (un Int)) x))))
            (term (fix (un λ (f (un Int)) (un 3)))))

;-------------------------------------------------------------------------------
; ->β tests
;-------------------------------------------------------------------------------
;; if0-true
(test--> ->β (term (if0 (un 0) (un 4) (un 2))) (term (un 4)))
;; if0-false
(test--> ->β (term (if0 (un 3) (un 4) (un 2))) (term (un 2)))

;; hits if0-true, if0-false, fixpoint, app-name, op+, op-, op*
(define Linλ-fact
  (term (fix (un λ (f (un (Int -> Int)))
                 (un λ (x (un Int))
                     (if0 x
                          (un 1)
                          (* x (f (- x (un 1))))))))))
(test-->> ->β (term (,Linλ-fact (+ (un 3) (un 2)))) (term (un 120)))

;; hits app-name, split, op+
(define Linλ-curry
  (term (un λ (f (un ((Int * Int) -> Int)))
            (un λ (x (un Int))
                (un λ (y (un Int))
                    (f (un pair x y)))))))
(define Linλ-uncurry
  (term (un λ (f (un (Int -> (Int -> Int))))
            (un λ (xy (un (Int * Int)))
                (split xy (x y) ((f x) y))))))
(define curried-add (term (un λ (x (un Int)) (un λ (y (un Int)) (+ x y)))))
(define uncurried-add (term (un λ (xy (un (Int * Int))) (split xy (x y) (+ x y)))))
(test-->> ->β (term ((,Linλ-uncurry ,curried-add) (un pair (un 3) (un 2)))) (term (un 5)))
(test-->> ->β (term (((,Linλ-curry ,uncurried-add) (un 3)) (un 2))) (term (un 5)))
