#lang racket
(require "pipeline.rkt")
(require rackunit)

;; # SYMBOLIC EXECUTION

;; se : TinyPPL -> (List Formula (Hash Var Number))
;; Collects both results of symbolic-execution into a list for comparison.
(define (se e)
  (call-with-values (λ () (symbolic-execution e)) list))

;; A single flip becomes one fresh variable
(check-equal? (se (flipE 1/3))
              (list (varF 0) (hash 0 1/3)))

;; not wraps the subformula
(check-equal? (se (notE (flipE 1/4)))
              (list (notF (varF 0)) (hash 0 1/4)))

;; Two flips get two different variables
(check-equal? (se (andE (flipE 1/3) (flipE 1/5)))
              (list (andF (varF 0) (varF 1)) (hash 0 1/3 1 1/5)))

(check-equal? (se (orE (flipE 1/3) (flipE 1/5)))
              (list (orF (varF 0) (varF 1)) (hash 0 1/3 1 1/5)))

;; xor is a primitive formula
(check-equal? (se (xorE (flipE 1/2) (flipE 1/3)))
              (list (xorF (varF 0) (varF 1)) (hash 0 1/2 1 1/3)))

;; if runs the condition once (three variables, not four) and shares its formula
(check-equal? (se (ifE (flipE 1/2) (flipE 1/3) (flipE 1/4)))
              (list (orF (andF (varF 0) (varF 1))
                         (andF (notF (varF 0)) (varF 2)))
                    (hash 0 1/2 1 1/3 2 1/4)))

;; Variables are numbered left to right
(check-equal? (se (andE (orE (flipE 1/2) (flipE 1/3)) (flipE 1/4)))
              (list (andF (orF (varF 0) (varF 1)) (varF 2))
                    (hash 0 1/2 1 1/3 2 1/4)))

;; let shares one variable instead of creating a new one
(check-equal? (se (letE 'x (flipE 1/2) (andE (varE 'x) (notE (varE 'x)))))
              (list (andF (varF 0) (notF (varF 0))) (hash 0 1/2)))

;; Nested lets
(check-equal? (se (letE 'x (flipE 1/2)
                        (letE 'y (flipE 1/2)
                              (orE (varE 'x) (varE 'y)))))
              (list (orF (varF 0) (varF 1)) (hash 0 1/2 1 1/2)))

;; A let can bind a compound formula, not just a variable
(check-equal? (se (letE 'x (andE (flipE 1/2) (flipE 1/3))
                        (notE (varE 'x))))
              (list (notF (andF (varF 0) (varF 1))) (hash 0 1/2 1 1/3)))

;; An unused let still creates its variable
(check-equal? (se (letE 'x (flipE 1/2) (flipE 1/3)))
              (list (varF 1) (hash 0 1/2 1 1/3)))

;; An inner let shadows an outer one with the same name
(check-equal? (se (letE 'x (flipE 1/2)
                        (letE 'x (flipE 1/3) (varE 'x))))
              (list (varF 1) (hash 0 1/2 1 1/3)))

;; Numbering restarts at 0 for each program, even after a larger one
(void (se (andE (flipE 1/2) (andE (flipE 1/2) (flipE 1/2)))))
(check-equal? (se (flipE 1/3)) (list (varF 0) (hash 0 1/3)))

;; An unbound variable is an error
(check-exn exn:fail? (λ () (symbolic-execution (varE 'z))))


;; # SMART CONSTRUCTORS

;; Constants are programs too
(check-equal? (se #t) (list #t (hash)))
(check-equal? (se #f) (list #f (hash)))

;; and: #t is the identity, #f absorbs (the flip still creates its variable)
(check-equal? (se (andE #t (flipE 1/2))) (list (varF 0) (hash 0 1/2)))
(check-equal? (se (andE (flipE 1/2) #t)) (list (varF 0) (hash 0 1/2)))
(check-equal? (se (andE #f (flipE 1/2))) (list #f (hash 0 1/2)))
(check-equal? (se (andE (flipE 1/2) #f)) (list #f (hash 0 1/2)))

;; or: #f is the identity, #t absorbs
(check-equal? (se (orE #f (flipE 1/2))) (list (varF 0) (hash 0 1/2)))
(check-equal? (se (orE (flipE 1/2) #t)) (list #t (hash 0 1/2)))

;; xor: #f is the identity, #t negates
(check-equal? (se (xorE (flipE 1/2) #f)) (list (varF 0) (hash 0 1/2)))
(check-equal? (se (xorE #t (flipE 1/2))) (list (notF (varF 0)) (hash 0 1/2)))

;; not: constants flip, double negation cancels
(check-equal? (se (notE #t)) (list #f (hash)))
(check-equal? (se (notE (notE (flipE 1/2)))) (list (varF 0) (hash 0 1/2)))

;; The same object: x ∧ x = x, x ∨ x = x, x ⊕ x = #f
(check-equal? (se (letE 'x (flipE 1/2) (andE (varE 'x) (varE 'x))))
              (list (varF 0) (hash 0 1/2)))
(check-equal? (se (letE 'x (flipE 1/2) (orE (varE 'x) (varE 'x))))
              (list (varF 0) (hash 0 1/2)))
(check-equal? (se (letE 'x (flipE 1/2) (xorE (varE 'x) (varE 'x))))
              (list #f (hash 0 1/2)))

;; Equal-looking but separate coins are not merged
(check-equal? (se (andE (flipE 1/2) (flipE 1/2)))
              (list (andF (varF 0) (varF 1)) (hash 0 1/2 1 1/2)))

;; A constant condition picks its branch (both branches still run)
(check-equal? (se (ifE #t (flipE 1/3) (flipE 1/4)))
              (list (varF 0) (hash 0 1/3 1 1/4)))
(check-equal? (se (ifE #f (flipE 1/3) (flipE 1/4)))
              (list (varF 1) (hash 0 1/3 1 1/4)))

;; Constant branches: if c then #t else #f is c, if c then #f else #t is ¬c
(check-equal? (se (ifE (flipE 1/2) #t #f)) (list (varF 0) (hash 0 1/2)))
(check-equal? (se (ifE (flipE 1/2) #f #t)) (list (notF (varF 0)) (hash 0 1/2)))

;; One-time pad with a constant message: each ciphertext bit is just a key bit
(check-equal? (se (letE 'k (flipE 1/2) (xorE (varE 'k) #f)))
              (list (varF 0) (hash 0 1/2)))
(check-equal? (se (letE 'k (flipE 1/2) (xorE (varE 'k) #t)))
              (list (notF (varF 0)) (hash 0 1/2)))

;; Simplification preserves sharing: ¬¬x returns the original x object
(let-values ([(phi w) (symbolic-execution
                       (letE 'x (flipE 1/2)
                             (andE (varE 'x) (notE (notE (varE 'x))))))])
  (check-equal? phi (varF 0)))


;; # KNOWLEDGE COMPILATION

(define kc knowledge-compilation)
(define x (varF 0))
(define y (varF 1))
(define z (varF 2))

;; Constants compile to terminals
(check-eq? (kc #t) #t)
(check-eq? (kc #f) #f)

;; A single variable is one node: if x then #t else #f
(check-equal? (BddNode-v (kc x)) 0)
(check-eq? (BddNode-h (kc x)) #t)
(check-eq? (BddNode-l (kc x)) #f)

;; Negating a variable swaps the terminals
(check-eq? (BddNode-h (kc (notF x))) #f)
(check-eq? (BddNode-l (kc (notF x))) #t)

;; Compiling the same formula twice gives the same node
(check-eq? (kc (andF x y)) (kc (andF x y)))

;; Different functions give different nodes
(check-not-eq? (kc (andF x y)) (kc (orF x y)))
(check-not-eq? (kc (xorF x y)) (kc (orF x y)))

;; Contradiction and tautology collapse to terminals
(check-eq? (kc (andF x (notF x))) #f)
(check-eq? (kc (orF x (notF x))) #t)

;; Double negation
(check-eq? (kc (notF (notF x))) (kc x))

;; Idempotence
(check-eq? (kc (andF x x)) (kc x))
(check-eq? (kc (orF x x)) (kc x))

;; Commutativity
(check-eq? (kc (andF x y)) (kc (andF y x)))
(check-eq? (kc (orF x y)) (kc (orF y x)))
(check-eq? (kc (xorF x y)) (kc (xorF y x)))

;; De Morgan
(check-eq? (kc (orF x y)) (kc (notF (andF (notF x) (notF y)))))
(check-eq? (kc (andF x y)) (kc (notF (orF (notF x) (notF y)))))

;; Absorption
(check-eq? (kc (orF x (andF x y))) (kc x))
(check-eq? (kc (andF x (orF x y))) (kc x))

;; Distributivity
(check-eq? (kc (andF x (orF y z)))
           (kc (orF (andF x y) (andF x z))))

;; Reduction: y doesn't matter, so its nodes disappear
(check-eq? (kc (orF (andF x y) (andF x (notF y)))) (kc x))

;; Ordering: the smallest variable is at the root, whatever the formula's order
(check-equal? (BddNode-v (kc (andF y x))) 0)
(check-equal? (BddNode-v (BddNode-h (kc (andF y x)))) 1)

;; xor matches its definition (x ∧ ¬y) ∨ (¬x ∧ y)
(check-eq? (kc (xorF x y))
           (kc (orF (andF x (notF y)) (andF (notF x) y))))

;; xor laws: x ⊕ x = #f, x ⊕ ¬x = #t, x ⊕ #f = x, x ⊕ #t = ¬x
(check-eq? (kc (xorF x x)) #f)
(check-eq? (kc (xorF x (notF x))) #t)
(check-eq? (kc (xorF x #f)) (kc x))
(check-eq? (kc (xorF x #t)) (kc (notF x)))

;; xor cancels: (x ⊕ y) ⊕ y = x, the reason the one-time pad decrypts
(check-eq? (kc (xorF (xorF x y) y)) (kc x))

;; xor is associative
(check-eq? (kc (xorF (xorF x y) z)) (kc (xorF x (xorF y z))))


;; # WEIGHTED MODEL COUNTING

;; Terminals
(check-equal? (bdd-wmc #t (hash)) 1)
(check-equal? (bdd-wmc #f (hash)) 0)

;; A single variable has its own weight
(check-equal? (bdd-wmc (kc x) (hash 0 1/3)) 1/3)
(check-equal? (bdd-wmc (kc (notF x)) (hash 0 1/3)) 2/3)

;; Independent conjunction, disjunction, and exclusive or
(check-equal? (bdd-wmc (kc (andF x y)) (hash 0 1/3 1 1/4)) 1/12)
(check-equal? (bdd-wmc (kc (orF x y)) (hash 0 1/3 1 1/4)) 1/2)
(check-equal? (bdd-wmc (kc (xorF x y)) (hash 0 1/3 1 1/4)) 5/12)

;; The same BDD gives different answers under different weights
(check-equal? (bdd-wmc (kc (andF x y)) (hash 0 1/2 1 1/2)) 1/4)

;; A skipped level: x ∧ z ignores y, so y contributes a factor of 1
(check-equal? (bdd-wmc (kc (andF x z)) (hash 0 1/2 1 1/7 2 1/3)) 1/6)


;; # TinyPPL: ONE CONSTRUCT AT A TIME

;; constants
(check-equal? (compiler #t) 1)
(check-equal? (compiler #f) 0)
(check-equal? (compiler (andE #t (flipE 2/7))) 2/7)
(check-equal? (compiler (orE #f (flipE 2/7))) 2/7)
(check-equal? (compiler (xorE #t (flipE 2/7))) 5/7)
(check-equal? (compiler (ifE #f (flipE 1/3) (flipE 2/7))) 2/7)

;; flip
(check-equal? (compiler (flipE 2/7)) 2/7)
(check-equal? (compiler (flipE 0)) 0)
(check-equal? (compiler (flipE 1)) 1)

;; not
(check-equal? (compiler (notE (flipE 2/7))) 5/7)
(check-equal? (compiler (notE (notE (flipE 3/8)))) 3/8)

;; and: independent flips multiply
(check-equal? (compiler (andE (flipE 1/2) (andE (flipE 1/3) (flipE 1/4)))) 1/24)
(check-equal? (compiler (andE (flipE 1) (flipE 3/5))) 3/5)
(check-equal? (compiler (andE (flipE 0) (flipE 3/5))) 0)

;; or: 1 - P(all false) = 1 - 1/2 · 2/3 · 3/4
(check-equal? (compiler (orE (flipE 1/2) (orE (flipE 1/3) (flipE 1/4)))) 3/4)
(check-equal? (compiler (orE (flipE 0) (flipE 3/5))) 3/5)
(check-equal? (compiler (orE (flipE 1) (flipE 3/5))) 1)

;; xor: exactly one side is true, 1/3 · 3/4 + 2/3 · 1/4
(check-equal? (compiler (xorE (flipE 1/3) (flipE 1/4))) 5/12)
(check-equal? (compiler (xorE (flipE 0) (flipE 2/7))) 2/7)
(check-equal? (compiler (xorE (flipE 1) (flipE 2/7))) 5/7)

;; xor of a coin with itself is never true; with its negation, always
(check-equal? (compiler (letE 'x (flipE 2/5) (xorE (varE 'x) (varE 'x)))) 0)
(check-equal? (compiler (letE 'x (flipE 2/5) (xorE (varE 'x) (notE (varE 'x))))) 1)

;; Equality of two coins is ¬(a ⊕ b): 1 - 5/12
(check-equal? (compiler (notE (xorE (flipE 1/3) (flipE 1/4)))) 7/12)

;; One-time pad: a fair key bit hides any message bit
(check-equal? (compiler (letE 'm (flipE 1/7) (xorE (flipE 1/2) (varE 'm)))) 1/2)
(check-equal? (compiler (letE 'm (flipE 1) (xorE (flipE 1/2) (varE 'm)))) 1/2)

;; if: 1/3 · 1/2 + 2/3 · 1/5
(check-equal? (compiler (ifE (flipE 1/3) (flipE 1/2) (flipE 1/5))) 3/10)

;; A certain condition picks one branch
(check-equal? (compiler (ifE (flipE 1) (flipE 2/7) (flipE 5/9))) 2/7)
(check-equal? (compiler (ifE (flipE 0) (flipE 2/7) (flipE 5/9))) 5/9)

;; Identical branches make the condition irrelevant
(check-equal? (compiler (ifE (flipE 1/3) (flipE 2/5) (flipE 2/5))) 2/5)

;; The condition is one coin, not two: if it were copied,
;; this would be c1 ∨ ¬c2 = 3/4 instead of 1
(check-equal? (compiler (ifE (flipE 1/2) (flipE 1) (flipE 1))) 1)

;; The condition can be used in a branch: 1/4 + 3/4 · 1/2
(check-equal? (compiler (letE 'c (flipE 1/4)
                              (ifE (varE 'c) (varE 'c) (flipE 1/2))))
              5/8)

;; if c then c else ¬c is always true
(check-equal? (compiler (letE 'c (flipE 1/3)
                              (ifE (varE 'c) (varE 'c) (notE (varE 'c)))))
              1)

;; if a then b else #f is a ∧ b
(check-equal? (compiler (letE 'a (flipE 1/3)
                              (letE 'b (flipE 1/4)
                                    (ifE (varE 'a) (varE 'b) (flipE 0)))))
              1/12)

;; let: one shared coin vs. two separate coins
(check-equal? (compiler (letE 'x (flipE 2/5) (orE (varE 'x) (varE 'x)))) 2/5)
(check-equal? (compiler (orE (flipE 2/5) (flipE 2/5))) 16/25)

;; let can bind a compound expression, which is then shared
(check-equal? (compiler (letE 'x (orE (flipE 1/2) (flipE 1/2))
                              (andE (varE 'x) (varE 'x))))
              3/4)

;; An unused let doesn't change the result
(check-equal? (compiler (letE 'x (flipE 1/9) (flipE 2/3))) 2/3)

;; Shadowing: the inner binding wins
(check-equal? (compiler (letE 'x (flipE 1/5) (letE 'x (flipE 4/5) (varE 'x)))) 4/5)

;; An inner let refers to an outer one:
;; y = x ∧ f, so y ∨ ¬x = f ∨ ¬x, and 1 - P(x ∧ ¬f) = 1 - 1/2 · 2/3
(check-equal? (compiler (letE 'x (flipE 1/2)
                              (letE 'y (andE (varE 'x) (flipE 1/3))
                                    (orE (varE 'y) (notE (varE 'x))))))
              2/3)


;; # TinyPPL: COMBINED PROGRAMS

;; Correlation: a coin against itself
(check-equal? (compiler (letE 'x (flipE 3/7) (orE (varE 'x) (notE (varE 'x))))) 1)
(check-equal? (compiler (letE 'x (flipE 3/7) (andE (varE 'x) (notE (varE 'x))))) 0)

;; Implication a → b, written ¬a ∨ b: 1 - P(a ∧ ¬b) = 1 - 1/3 · 3/4
(check-equal? (compiler (letE 'a (flipE 1/3)
                              (letE 'b (flipE 1/4)
                                    (orE (notE (varE 'a)) (varE 'b)))))
              3/4)

;; Majority of three coins with p = 1/3: 3p2(1 - p) + p3 = 7/27
(check-equal? (compiler (letE 'a (flipE 1/3)
                              (letE 'b (flipE 1/3)
                                    (letE 'c (flipE 1/3)
                                          (orE (andE (varE 'a) (varE 'b))
                                               (orE (andE (varE 'a) (varE 'c))
                                                    (andE (varE 'b) (varE 'c))))))))
              7/27)

;; Encrypt then decrypt with the same key gives back the message:
;; (m ⊕ k) ⊕ k = m, so this is always true
(check-equal? (compiler (letE 'm (flipE 1/3)
                              (letE 'k (flipE 1/2)
                                    (letE 'c (xorE (varE 'm) (varE 'k))
                                          (notE (xorE (xorE (varE 'c) (varE 'k))
                                                      (varE 'm)))))))
              1)

;; and-chain : Natural -> TinyPPL
;; The conjunction of n separate fair coins.
(define (and-chain n)
  (if (= n 1)
      (flipE 1/2)
      (andE (flipE 1/2) (and-chain (- n 1)))))

;; Many variables: probability 1/2^40
(check-equal? (compiler (and-chain 40)) (expt 1/2 40))

;; parity : Natural -> TinyPPL
;; Whether an odd number of n coins (each with p = 1/3) come up true.
;; Each accumulator is let-bound, so the formula shares it rather than copying it.
(define (parity n)
  (define (acc i) (string->symbol (format "acc~a" i)))
  (define (build i)
    (if (= i n)
        (varE (acc (- n 1)))
        (letE (acc i) (xorE (varE (acc (- i 1))) (flipE 1/3))
              (build (+ i 1)))))
  (letE (acc 0) (flipE 1/3) (build 1)))

;; P(odd) = (1 - (1 - 2p)^n) / 2
(check-equal? (compiler (parity 8)) (/ (- 1 (expt 1/3 8)) 2))

;; Scale: 200 chained xors
(check-equal? (compiler (parity 200)) (/ (- 1 (expt 1/3 200)) 2))

;; if-chain : Natural -> TinyPPL
;; n nested ifs, each choosing between the previous result and a fresh coin.
;; The shared condition formulas make this a DAG, like parity.
(define (if-chain n)
  (define (acc i) (string->symbol (format "r~a" i)))
  (define (build i)
    (if (= i n)
        (varE (acc (- n 1)))
        (letE (acc i) (ifE (flipE 1/2) (varE (acc (- i 1))) (flipE 1/3))
              (build (+ i 1)))))
  (letE (acc 0) (flipE 1/3) (build 1)))

;; Every coin has p = 1/3 and every branch keeps a coin with p = 1/3
(check-equal? (compiler (if-chain 100)) 1/3)


;; # TinyPPL: EXHAUSTIVE AND RANDOM TESTING AGAINST A REFERENCE

;; reference : TinyPPL -> Number
;; Computes the probability of #t by enumerating outcomes directly,
;; without symbolic execution, BDDs, or model counting.
;; Unlike symbolic-execution, ifE runs only the branch that is taken.
(define (reference e)
  ;; An Outcomes is a (List (Pair #t Number) (Pair #f Number))
  (define (merge os)
    (list (cons #t (for/sum ([o os] #:when (car o)) (cdr o)))
          (cons #f (for/sum ([o os] #:unless (car o)) (cdr o)))))
  ;; outcomes : TinyPPL (Hash Symbol Boolean) -> Outcomes
  (define (outcomes e env)
    (match e
      [#t (list (cons #t 1) (cons #f 0))]
      [#f (list (cons #t 0) (cons #f 1))]
      [(flipE p) (list (cons #t p) (cons #f (- 1 p)))]
      [(notE e1)
       (merge (for/list ([o (outcomes e1 env)])
                (cons (not (car o)) (cdr o))))]
      [(andE e1 e2)
       (merge (for*/list ([o1 (outcomes e1 env)] [o2 (outcomes e2 env)])
                (cons (and (car o1) (car o2)) (* (cdr o1) (cdr o2)))))]
      [(orE e1 e2)
       (merge (for*/list ([o1 (outcomes e1 env)] [o2 (outcomes e2 env)])
                (cons (or (car o1) (car o2)) (* (cdr o1) (cdr o2)))))]
      [(xorE e1 e2)
       (merge (for*/list ([o1 (outcomes e1 env)] [o2 (outcomes e2 env)])
                (cons (not (eq? (car o1) (car o2))) (* (cdr o1) (cdr o2)))))]
      [(ifE c t f)
       (merge (for*/list ([oc (outcomes c env)]
                          [ob (outcomes (if (car oc) t f) env)])
                (cons (car ob) (* (cdr oc) (cdr ob)))))]
      [(varE x) (merge (list (cons (hash-ref env x) 1)))]
      [(letE x a body)
       (merge (for*/list ([o1 (outcomes a env)]
                          [o2 (outcomes body (hash-set env x (car o1)))])
                (cons (car o2) (* (cdr o1) (cdr o2)))))]))
  (cdr (first (outcomes e (hash)))))

;; The reference agrees with hand-computed answers
(check-equal? (reference #t) 1)
(check-equal? (reference (andE #t (flipE 2/7))) 2/7)
(check-equal? (reference (orE (flipE 2/5) (flipE 2/5))) 16/25)
(check-equal? (reference (parity 8)) (/ (- 1 (expt 1/3 8)) 2))
(check-equal? (reference (xorE (flipE 1/3) (flipE 1/4))) 5/12)
(check-equal? (reference (ifE (flipE 1/3) (flipE 1/2) (flipE 1/5))) 3/10)

(define names '(x y))

;; all-programs : Natural (Listof Symbol) (Listof (U Number Boolean)) -> (Listof TinyPPL)
;; Every program of depth at most d whose variables are all in scope.
;; Each atom is a flip probability, or a Boolean used as a constant.
;; ifE takes its three parts from the leaves only, since all combinations
;; of three smaller programs would be too many to test.
(define (all-programs d scope atoms)
  (define leaves (append (for/list ([a atoms]) (if (boolean? a) a (flipE a)))
                         (map varE (remove-duplicates scope))))
  (if (= d 0)
      leaves
      (let ([smaller (all-programs (- d 1) scope atoms)])
        (append leaves
                (map notE smaller)
                (for*/list ([a smaller] [b smaller]) (andE a b))
                (for*/list ([a smaller] [b smaller]) (orE a b))
                (for*/list ([a smaller] [b smaller]) (xorE a b))
                (for*/list ([c leaves] [t leaves] [f leaves]) (ifE c t f))
                (for*/list ([x names]
                            [a smaller]
                            [b (all-programs (- d 1) (cons x scope) atoms)])
                  (letE x a b))))))

;; Every program up to depth 2 built from two kinds of flip
(define small-programs (all-programs 2 '() '(1/3 1/2)))

;; Every program up to depth 1 that mixes a flip with constants,
;; so each simplification rule is exercised in every position
(define constant-programs (all-programs 1 '() '(1/3 #t #f)))

;; Every program matches the reference, and basic laws hold
(for ([p (append small-programs constant-programs)])
  (define msg (~a p))
  (define pr (compiler p))
  (check-equal? pr (reference p) msg)
  ;; a probability is between 0 and 1
  (check-true (<= 0 pr 1) msg)
  ;; complement
  (check-equal? (compiler (notE p)) (- 1 pr) msg)
  ;; two copies of a program are independent runs
  (check-equal? (compiler (andE p p)) (* pr pr) msg)
  ;; binding a program and using it twice is one run
  (check-equal? (compiler (letE 'shared p (andE (varE 'shared) (varE 'shared)))) pr msg)
  ;; an unused binding changes nothing
  (check-equal? (compiler (letE 'unused (flipE 1/7) p)) pr msg)
  ;; two independent runs differ with probability 2P(1 - P)
  (check-equal? (compiler (xorE p p)) (* 2 pr (- 1 pr)) msg)
  ;; one run never differs from itself
  (check-equal? (compiler (letE 'shared p (xorE (varE 'shared) (varE 'shared)))) 0 msg)
  ;; whichever branch runs, it is one run of p
  (check-equal? (compiler (ifE (flipE 1/3) p p)) pr msg)
  ;; if p then #t else #f is p
  (check-equal? (compiler (ifE p (flipE 1) (flipE 0))) pr msg))

(define random-probs '(0 1/5 1/4 1/3 1/2 2/3 3/4 1))
(define random-names '(x y z))

;; pick : (Listof X) -> X
(define (pick xs) (list-ref xs (random (length xs))))

;; random-program : Natural (Listof Symbol) -> TinyPPL
;; A random program of depth at most d whose variables are all in scope.
(define (random-program d scope)
  (define (leaf)
    (case (random 4)
      [(0) (if (pair? scope) (varE (pick scope)) (flipE (pick random-probs)))]
      [(1) (pick '(#t #f))]
      [else (flipE (pick random-probs))]))
  (define (sub) (random-program (- d 1) scope))
  (if (= d 0)
      (leaf)
      (case (random 7)
        [(0) (leaf)]
        [(1) (notE (sub))]
        [(2) (andE (sub) (sub))]
        [(3) (orE (sub) (sub))]
        [(4) (xorE (sub) (sub))]
        [(5) (ifE (sub) (sub) (sub))]
        [(6) (let ([x (pick random-names)])
               (letE x (sub) (random-program (- d 1) (cons x scope))))])))

;; Fixed seed, so failures can be reproduced
(random-seed 2026)

;; Larger random programs match the reference
(for ([_ (in-range 300)])
  (define p (random-program 6 '()))
  (check-equal? (compiler p) (reference p) (~a p)))

;; Inclusion-exclusion on random pairs: P(a ∧ b) + P(a ∨ b) = P(a) + P(b)
(for ([_ (in-range 200)])
  (define a (random-program 3 '()))
  (define b (random-program 3 '()))
  (check-equal? (+ (compiler (andE a b)) (compiler (orE a b)))
                (+ (compiler a) (compiler b))
                (~a (list a b))))
