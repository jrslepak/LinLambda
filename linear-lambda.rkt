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
     (τ -> τ)          ; function
     (τ * τ))          ; pair
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
        fixpoint]))


;-------------------------------------------------------------------------------
; typechecking
;-------------------------------------------------------------------------------
(define-judgment-form Linλ
  #:mode(typeof I I O O)
  #:contract(typeof Γ e τ Γ)
  ; int literals just use their annotated type qualifier
  [(typeof Γ (q n) (q Int) Γ)]
  
  ; using an unrestricted variable does not change the output environment
  [(typeof ((x_0 τ_0) ... (x_1 (un p)) (x_2 τ_2) ...)
           x_1
           (un p)
           ((x_0 τ_0) ... (x_1 (un p)) (x_2 τ_2) ...))]
  
  ; linear variable has been used -- exclude it from the output environment
  [(typeof ((x_0 τ_0) ... (x_1 (lin p)) (x_2 τ_2) ...)
           x_1
           (lin p)
           ((x_0 τ_0) ... (x_2 τ_2) ...))]
  
  ; antecedent must be Int with any qualifier (if0 uses it exactly once)
  ; consequent and alternate must be of the same type
  [(typeof Γ_1 e_ante (q Int) Γ_2)
   (typeof Γ_2 e_cons τ Γ_3)
   (typeof Γ_2 e_alt τ Γ_3)
   ---
   (typeof Γ_1 (if0 e_ante e_cons e_alt) τ Γ_3)]
  
  ; pair must be at least as restrictive as its components
  [(typeof Γ_1 e_left (q_left p_left) Γ_2)
   (typeof Γ_2 e_right (q_right p_right) Γ_3)
   (subkind q_pair q_left)
   (subkind q_pair q_right)
   ---
   (typeof Γ_1 (q_pair pair e_left e_right) (q_pair ((q_left p_left) * (q_right p_right))) Γ_3)]
  
  ; split
  [(typeof Γ_1 e_pair (q (τ_left * τ_right)) Γ_2)
   (typeof (ext-type-env (ext-type-env Γ_2 (x_left τ_left)) (x_right τ_right)) e_body τ Γ_3)
   (ctxt-diff Γ_3 ( (x_left τ_left) (x_right τ_right) ) Γ_difference)
   ---
   (typeof Γ_1 (split e_pair (x_left x_right) e_body) τ Γ_difference)]
  
  ; primitive ops give unrestricted results
  ; looks a lot like pair rule, only no qualifier on result
  [(typeof Γ_1 e_left (q_left Int) Γ_2)
   (typeof Γ_2 e_right (q_right Int) Γ_3)
   ---
   (typeof Γ_1 (op e_left e_right) (un Int) Γ_3)]
  
  ; linear lambda and unrestricted lambda are treated slightly differently
  ; with unrestricted case, must use context difference to ensure no linear
  ; variables from the outside environment are used inside the function body
  [(typeof (ext-type-env Γ_1 (x τ_arg)) e_body τ_ret Γ_2)
   (ctxt-diff Γ_2 ((x τ_arg)) Γ_3)
   ---
   (typeof Γ_1 (lin λ (x τ_arg) e_body) (lin (τ_arg -> τ_ret)) Γ_3)]
  [(typeof (ext-type-env Γ_1 (x τ_arg)) e_body τ_ret Γ_2)
   (ctxt-diff Γ_2 ((x τ_arg)) Γ_3)
   (ctxt-diff Γ_2 ((x τ_arg)) Γ_1)
   ---
   (typeof Γ_1 (un λ (x τ_arg) e_body) (un (τ_arg -> τ_ret)) Γ_3)]
  
  ; application
  [(typeof Γ_1 e_fun (q (τ_arg -> τ_ret)) Γ_2)
   (typeof Γ_2 e_arg τ_arg Γ_3)
   ---
   (typeof Γ_1 (e_fun e_arg) τ_ret Γ_3)]
  
  ; fix cannot be used on linear function because it must be possible to
  ; apply the function an arbitrary number of times
  [(typeof Γ_1 e (un (τ -> τ)) Γ_2)
   ---
   (typeof Γ_1 (fix e) τ Γ_2)]
  
  )

;; judgment for "at least as restrictive as" relation
(define-judgment-form Linλ
  #:mode(subkind I I)
  #:contract(subkind q q)
  [(subkind un un)]
  [(subkind lin un)]
  [(subkind lin lin)])

;; judgment for context difference
(define-judgment-form Linλ
  #:mode(ctxt-diff I I O)
  #:contract(ctxt-diff Γ Γ Γ)
  [(ctxt-diff Γ () Γ)]
  [(ctxt-diff Γ_1 ((x_0 τ_0) ...) Γ_3)
   (side-condition (excludes (x (lin p)) Γ_3))
   ;(ctxt-diff () () (excludes (x (lin p)) Γ_3))
   ---
   (ctxt-diff Γ_1 ((x_0 τ_0) ... (x (lin p))) Γ_3)]
   
  [(ctxt-diff Γ ((x_0 τ_0) ...) ((x_1 τ_1) ... (x_un (un p)) (x_2 τ_2) ...))
   ---
   (ctxt-diff Γ ((x_0 τ_0) ... (x_un (un p))) ((x_1 τ_1) ... (x_2 τ_2) ...))]
  )

;-------------------------------------------------------------------------------
; utility metafunctions
;-------------------------------------------------------------------------------
;; list exclusion check
;; used for context difference judgment
(define-metafunction Linλ
  excludes : (x (lin p)) Γ -> any
  [(excludes (x (lin p)) ()) #t]
  [(excludes (x (lin p)) ((x (lin p)) (x_others τ_others) ...)) #f]
  [(excludes (x (lin p)) ((x_other τ_other) (x_more τ_more) ...))
   (excludes (x (lin p)) ((x_more τ_more) ...))])
  

(define-metafunction Linλ
  concat-type-env : Γ Γ -> Γ
  [(concat-type-env ((x_0 τ_0) ...) ((x_1 τ_1) ...)) ((x_0 τ_0) ... (x_1 τ_1) ...)])

(define-metafunction Linλ
  ext-type-env : Γ (x τ) -> Γ
  [(ext-type-env ((x_0 τ_0) ...) (x_1 τ_1)) ((x_0 τ_0) ... (x_1 τ_1))])

;; substitution of free variables
(define-metafunction Linλ
  var-sub : ((x e) ...) e -> e
  
  ;; base cases: operating on a variable or literal
  ;; 1. a variable from the substitution list
  [(var-sub ((x_0 e_0) ... (x_1 e_1) (x_2 e_2) ...) x_1)  e_1]
  ;; 2. a variable not in the substitution list
  [(var-sub ((x_0 e_0) ...) x_1)  x_1]
  ;; 3. base value literal
  [(var-sub ((x_0 e_0) ...) (q n))
   (q n)]
  
  
  ;; interesting recursive cases: binding forms
  ;; 1. λ which rebinds variable
  [(var-sub ((x_0 e_0) ... (x_arg e_arg) (x_2 e_2) ...)
            (q λ (x_arg τ_arg) e_body))
   (q λ (x_arg τ_arg) (var-sub ((x_0 e_0) ... (x_2 e_2) ...) e_body))]
  ;; 2. λ which does not rebind variable
  [(var-sub ((x_0 e_0) ...)
            (q λ (x_arg τ_arg) e_body))
   (q λ (x_arg τ_arg) (var-sub ((x_0 e_0) ...) e_body))]
  
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
   (fix (var-sub ((x_0 e_0) ...) e_fun))])


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
  (term (fix (un λ (f (un ((un Int) -> (un Int))))
                 (un λ (x (un Int))
                     (if0 x
                          (un 1)
                          (* x (f (- x (un 1))))))))))
(test-->> ->β (term (,Linλ-fact (+ (un 3) (un 2)))) (term (un 120)))

;; hits app-name, split, op+
(define Linλ-curry
  (term (un λ (f (un ((un ((un Int) * (un Int))) -> (un Int))))
            (un λ (x (un Int))
                (un λ (y (un Int))
                    (f (un pair x y)))))))
(define Linλ-uncurry
  (term (un λ (f (un ((un Int) -> (un ((un Int) -> (un Int))))))
            (un λ (xy (un ((un Int) * (un Int))))
                (split xy (x y) ((f x) y))))))
(define curried-add (term (un λ (x (un Int)) (un λ (y (un Int)) (+ x y)))))
(define uncurried-add (term (un λ (xy (un ((un Int) * (un Int)))) (split xy (x y) (+ x y)))))
(test-->> ->β (term ((,Linλ-uncurry ,curried-add) (un pair (un 3) (un 2)))) (term (un 5)))
(test-->> ->β (term (((,Linλ-curry ,uncurried-add) (un 3)) (un 2))) (term (un 5)))



;-------------------------------------------------------------------------------
; typeof tests
;-------------------------------------------------------------------------------
; unrestricted integer
(test-equal
 (judgment-holds (typeof () (un 3) τ Γ) (τ Γ))
 '( ((un Int)
     ()) ))

; linear integer
(test-equal
 (judgment-holds (typeof () (lin 3) τ Γ) (τ Γ))
 '( ((lin Int)
     ()) ))

; unrestricted variable
(test-equal
 (judgment-holds
  (typeof ((x (un Int))
           (y (un ((un Int) -> (un Int))))
           (z (lin Int)))
          x τ Γ)
  (τ Γ))
 '( ((un Int)
     ((x (un Int))
      (y (un ((un Int) -> (un Int))))
      (z (lin Int)))) ))

; linear variable
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (lin ((un Int) -> (un Int))))
                          (z (lin Int)))
                         y τ Γ)
                 (τ Γ))
 '( ((lin ((un Int) -> (un Int)))
     ((x (un Int))
      (z (lin Int)))) )) ; unused linear variable still present

; free variable
(test-equal
 (judgment-holds
  (typeof ((x (un Int))
           (y (un ((un Int) -> (un Int))))
           (z (lin Int)))
          w τ Γ))
 #f)

; if0 -- linear antecedent
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (lin ((un Int) -> (un Int))))
                          (z (lin ((un Int) -> (un Int)))))
                         (if0 x y y) τ Γ)
                 (τ Γ))
 '( ((lin ((un Int) -> (un Int)))
     ((x (un Int))
      (z (lin ((un Int) -> (un Int)))))) ))

; if0 -- consequent and alternate mismatched
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (lin ((un Int) -> (un Int))))
                          (z (un ((un Int) -> (un Int)))))
                         (if0 x y z) τ Γ))
 #f)

; pair -- un and lin can make lin, consumes lin variable
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (lin ((un Int) -> (un Int)))))
                         (lin pair x y) τ Γ)
                 (τ Γ))
 '( ((lin ((un Int) * (lin ((un Int) -> (un Int)))))
     ((x (un Int)))) ))

; pair -- un and lin cannot make un
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (lin ((un Int) -> (un Int)))))
                         (un pair x y) τ Γ))
 #f)

; pair -- un and un can make lin
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (un ((un Int) -> (un Int)))))
                         (lin pair x y) τ Γ)
                 (τ Γ))
 '( ((lin ((un Int) * (un ((un Int) -> (un Int)))))
     ((x (un Int))
      (y (un ((un Int) -> (un Int)))))) ))


; split -- uses the linear component
(test-equal
 (judgment-holds (typeof ()
                         (split (lin pair (lin 2) (un 3)) (x y) x) τ Γ)
                 (τ Γ))
            '( ((lin Int)
                ()) ))

; split -- doesn't use the linear component, so doesn't typecheck
(test-equal
 (judgment-holds (typeof ()
                         (split (lin pair (lin 2) (un 3)) (x y) y) τ Γ))
 #f)

; arithmetic -- uses up the linear variables
(test-equal
 (judgment-holds (typeof ((x (lin Int))
                          (y (lin Int))
                          (z (un Int)))
                         (+ x y) τ Γ)
                 (τ Γ))
 '( ((un Int) ( (z (un Int)) )) ))

; arithmetic -- no linear variables to use
(test-equal
 (judgment-holds (typeof ((x (un Int))
                          (y (un Int))
                          (z (un Int)))
                         (+ x y) τ Γ)
                 (τ Γ))
 '( ((un Int) ( (x (un Int))
                (y (un Int))
                (z (un Int)) )) ))

; arithmetic -- some linear variables unused
(test-equal
 (judgment-holds (typeof ((x (lin Int))
                          (y (lin Int))
                          (z (un Int)))
                         (+ x z) τ Γ)
                 (τ Γ))
 '( ((un Int) ( (y (lin Int))
                (z (un Int)) )) ))

; arithmetic -- linear variable overused
(test-equal
 (judgment-holds (typeof ((x (lin Int))
                          (y (un Int))
                          (z (un Int)))
                         (+ x x) τ Γ))
 #f)

; lambda -- using unrestricted variable from environment is ok
(test-equal
 (judgment-holds (typeof ((k (un Int)))
                         (un λ (x (lin Int)) (* k x)) τ Γ)
                 (τ Γ))
 '( ((un ((lin Int) -> (un Int)))
     ((k (un Int))) ) ))
(test-equal
 (judgment-holds (typeof ((k (un Int)))
                         (lin λ (x (lin Int)) (* k x)) τ Γ)
                 (τ Γ))
 '( ((lin ((lin Int) -> (un Int)))
     ((k (un Int))) ) ))

; lambda -- can't make an unrestricted lambda that uses a linear variable
(test-equal
 (judgment-holds (typeof ((k (lin Int)))
                         (un λ (x (lin Int)) (* k x)) τ Γ))
 #f)

; application -- unrestricted value can bind to unrestricted variable
(test-equal
 (judgment-holds (typeof () ((un λ (x (un Int)) (+ x (un 3)))
                             (un 5)) τ Γ) (τ Γ))
 '(((un Int) ())))

; application -- linear value can bind to linear variable
; addition still returns an unrestricted Int
(test-equal
 (judgment-holds (typeof () ((un λ (x (lin Int)) (+ x (un 3)))
                             (lin 5)) τ Γ) (τ Γ))
 '(((un Int) ())))

; application -- can't bind a linear value to an unrestricted variable
(test-equal
 (judgment-holds (typeof () ((un λ (x (un Int)) (+ x (un 3)))
                             (lin 5)) τ Γ))
 #f)

; application -- can't bind an unrestricted value to a linear variable
(test-equal
 (judgment-holds (typeof () ((un λ (x (lin Int)) (+ x (un 3)))
                             (un 5)) τ Γ))
 #f)

; fix
(test-equal
 (judgment-holds (typeof () (fix (un λ (x (un Int)) (+ x (un 3)))) τ Γ) (τ Γ))
 '(((un Int) ())))

; fix -- cannot use fixed point operator on linear-typed function
(test-equal
 (judgment-holds (typeof () (fix (lin λ (x (un Int)) (+ x (un 3)))) τ Γ))
 #f)

; fix -- cannot use fixed point operator on function with different
; input and output types
(test-equal
 (judgment-holds (typeof () (fix (lin λ (x (un ((un Int) -> (un Int)))) (x (un 3)))) τ Γ))
 #f)
(test-equal
 (judgment-holds (typeof () (fix (lin λ (x (lin Int)) (+ x (un 3)))) τ Γ))
 #f)

; test the typing judgment on programs used for testing the semantics
(test-equal
 (judgment-holds (typeof ()
                         ((,Linλ-uncurry ,curried-add) (un pair (un 3) (un 2))) τ Γ)
                 τ)
 '((un Int)))
(test-equal
 (judgment-holds (typeof ()
                         (((,Linλ-curry ,uncurried-add) (un 3)) (un 2)) τ Γ)
                 τ)
 '((un Int)))
