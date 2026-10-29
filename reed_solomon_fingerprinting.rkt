#lang roulette/example/disrupt

;; Reed-Solomon Fingerprinting
;; Based on "Proofs, Arguments, and Zero-Knowledge" by Justin Thaler
;; (Section 2.1)

(define p 101)

;; # DEFINITIONS

;; A FieldElement is a Natural in [0, p)
;; Interpretation: An element of the finite field F_p

;; A Vector is a (List-of FieldElement)
;; Interpretation: The coefficients a_0, a_1, ..., a_{n-1} of a polynomial 
;; P(x) = a_0 + a_1*x + ... + a_{n-1}*x^{n-1}

;; A Fingerprint is a (FieldElement -> FieldElement)
;; Interpretation: A polynomial representing the vector, evaluated at a challenge r


;; # FIELD ARITHMETIC

;; Finite field operations to strictly enforce integer outputs (No Reals)
(define (mod-add a b) (modulo (+ a b) p))
(define (mod-sub a b) (modulo (- a b) p))
(define (mod-mul a b) (modulo (* a b) p))
(define (mod-expt base exp)
  (let loop ([b (modulo base p)] [e exp] [res 1])
    (cond
      [(zero? e) res]
      [(even? e)
       (loop (modulo (* b b) p) (/ e 2) res)]
      [else
       (loop (modulo (* b b) p)
             (quotient e 2)
             (modulo (* res b) p))])))

;; Fermat's Little Theorem for modular inverse
;; a^(-1) = a^(p-2) mod p
(define (mod-inv n)
  (mod-expt n (- p 2)))

(define (mod-div a b) (mod-mul a (mod-inv b)))
(define (mod-sum lst) (foldl mod-add 0 lst))
(define (mod-product lst) (foldl mod-mul 1 lst))


;; # PRIMITIVES

;; finite-field : Natural -> Distribution
;; Samples a FieldElement uniformly at random from {0, 1, ..., p-1}.
(define (finite-field p)
   (define (make-pairs lo hi prob)
     (if (> lo hi)
         '()
         (cons (cons lo prob)
               (make-pairs (add1 lo) hi prob))))
   (make-categorical (make-pairs 0 (- p 1) (/ 1 p))))


;; # HASH FUNCTION

;; h : Natural Vector -> Fingerprint
;; Recursively constructs the polynomial P(r) = sum(a_i * r^{i + current-degree})
(define (h current-degree assignments)
  (cond
    [(empty? assignments) (λ (r) 0)]
    [else (λ (r) (mod-add
                  (mod-mul (car assignments) (mod-expt r current-degree))
                  ((h (+ current-degree 1) (cdr assignments)) r)))]))


;; # VECTORS

;; vector-a : Vector
;; P_A(x) = 5 + 10x + 9x^2 + 3x^3
(define vector-a (list 5 10 9 3))

;; vector-b : Vector
;; P_B(x) = 5 + 20x + 9x^2 + 3x^3
(define vector-b (list 5 20 9 3))

;; hash-1 : Fingerprint
;; The polynomial function for vector A
(define hash-1 (h 0 vector-a))

;; hash-2 : Fingerprint
;; The polynomial function for vector B
(define hash-2 (h 0 vector-b))


;; # EVALUATION

;; compare-fingerprints : Fingerprint Fingerprint -> Distribution
;; Samples a challenge r uniformly at random from F_p and checks if f1(r) = f2(r)
(define (compare-fingerprints f1 f2)
  (define r (finite-field p))
  (= (f1 r) (f2 r)))

;; [Completeness]
;; If the vectors are identical, their fingerprints match at every r.
;; Pr[hash-1(r) = hash-1(r)] = 1
(compare-fingerprints hash-1 hash-1)

;; [Soundness]
;; Vectors A and B are distinct. The degree of the difference polynomial is n - 1 = 3.
;; By the Schwartz-Zippel Lemma, the probability of a collision is at most (n - 1) / p.
;; Pr[hash-1(r) = hash-2(r)] <= 3 / 101 ~ 0.0297
(compare-fingerprints hash-1 hash-2)