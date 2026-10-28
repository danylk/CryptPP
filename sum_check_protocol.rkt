#lang roulette/example/disrupt

;; Sum-Check Protocol
;; Based on "Proofs, Arguments, and Zero-Knowledge" by Justin Thaler
;; (Section 4.1)

(define p 11)

;; # DEFINITIONS

;; A FieldElement is a Natural in [0, p)
;; Interpretation: An element of the finite field F_p

;; A Bit is one of
;; - 1
;; - 0
;; Interpretation: A coordinate of a point on the Boolean hypercube {0,1}^v

;; A Polynomial is a function (List-of FieldElement) -> FieldElement
;; Interpretation: A v-variate polynomial g over F_p, evaluated at a full
;; assignment (x_1, ..., x_v);
;; the verifier has oracle access to it

;; A Message is a (List-of FieldElement)
;; Interpretation: The evaluations s_j(0), s_j(1), ..., s_j(d_j) of the
;; prover's univariate round-j polynomial;
;; d_j + 1 values fix a polynomial of degree <= d_j

;; A Prover is a function
;;   Natural Natural Polynomial (List-of FieldElement) FieldElement -> Message
;; Interpretation: Given the number of variables, the current degree bound, g,
;; the challenges so far, and the claim being checked, returns the round message


;; # FIELD ARITHMETIC

;; Finite field operations to strictly enforce integer outputs (No Reals)
(define (mod-add a b) (modulo (+ a b) p))
(define (mod-sub a b) (modulo (- a b) p))
(define (mod-mul a b) (modulo (* a b) p))

;; Fermat's Little Theorem for modular inverse
;; a^(-1) = a^(p-2) mod p
(define (mod-inv n)
  (let loop ([base (modulo n p)] [exp (- p 2)] [res 1])
    (cond
      [(zero? exp) res]
      [(even? exp)
       (loop (modulo (* base base) p) (/ exp 2) res)]
      [else
       (loop (modulo (* base base) p)
             (quotient exp 2)
             (modulo (* res base) p))])))

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

;; boolean-hypercube : Natural -> (List-of (List-of Bit))
;; Lists all 2^n points of the Boolean hypercube {0,1}^n.
(define (boolean-hypercube n)
  (if (zero? n)
      '(())
      (append (map (λ (lst) (cons 0 lst)) (boolean-hypercube (- n 1)))
              (map (λ (lst) (cons 1 lst)) (boolean-hypercube (- n 1))))))

;; interpolate : Message -> (FieldElement -> FieldElement)
;; Lagrange-interpolates the unique polynomial of degree <= k through
;; (0, y_0), (1, y_1), ..., (k, y_k).
(define (interpolate ys)
  (define xs (range (length ys)))
  (lambda (x)
    (mod-sum
     (for/list ([xi xs]
                [yi ys])
       (mod-mul yi
                (mod-product
                 (for/list ([xj xs]
                            #:when (not (= xi xj)))
                   (mod-div (mod-sub x xj) (mod-sub xi xj)))))))))

;; honest-evaluations : Natural Natural Polynomial (List-of FieldElement) -> Message
;; Computes s_j(xi) = sum of g(r_1, ..., r_{j-1}, xi, tail) over all Boolean tails,
;; for xi = 0, 1, ..., d_j.
(define (honest-evaluations v current-degree v-variate-poly list-of-query)
  (define remaining-vars (- v (length list-of-query) 1))
  (define boolean-assignments (boolean-hypercube remaining-vars))
  (for/list ([xi (range (+ current-degree 1))])
    (mod-sum
     (for/list ([tail boolean-assignments])
       (v-variate-poly (append list-of-query (list xi) tail))))))


;; # PROVERS

;; prover : Prover
;; Honest Prover: sends the prescribed round polynomial (ignores the claim).
(define (prover v current-degree v-variate-poly list-of-query expected-val)
  (honest-evaluations v current-degree v-variate-poly list-of-query))

;; prover* : Prover
;; Malicious Prover: keeps the honest s(0) and forges s(1) = expected-val - s(0),
;; so that s(0) + s(1) passes the round check for a false claim.
;; If deg = 0, s is a constant c with s(0) + s(1) = 2c, so it sends c = expected-val / 2.
(define (prover* v current-degree v-variate-poly list-of-query expected-val)
  (define honest
    (honest-evaluations v current-degree v-variate-poly list-of-query))
  (define y0 (car honest))
  (if (null? (cdr honest))
      (list (mod-div expected-val 2))
      (cons y0 (cons (mod-sub expected-val y0) (cddr honest)))))


;; # VERIFIER

;; verifier : Natural (List-of Natural) Polynomial FieldElement (List-of Distribution) Prover -> Distribution
;; Runs the sum-check protocol for the claim H = sum of g over {0,1}^v and
;; returns the distribution of accept (#t) / reject (#f) over the random challenges.
(define (verifier total-vars degrees g H random-challenges prover-fn)
  (verify-rounds total-vars degrees g H random-challenges prover-fn '()))

;; verify-rounds : Natural (List-of Natural) Polynomial FieldElement (List-of Distribution) Prover (List-of FieldElement)
;;                 -> Distribution
;; Checks the remaining rounds against the current claim, given the
;; challenges used so far, and ends with the final oracle check.
(define (verify-rounds v degrees g claim challenges prover-fn queries)
  (if (null? degrees)
      ;; --- FINAL ORACLE CHECK ---
      (= claim (g queries))

      ;; --- ROUND i ---
      (let* ([deg (car degrees)]
             [r (car challenges)]
             [ys (prover-fn v deg g queries claim)]
             [s (interpolate ys)])
        (cond
          ;; Degree check: at most d_i + 1 evaluations means deg <= d_i
          [(> (length ys) (+ deg 1)) #f]
          [else
           (if (not (= (mod-add (s 0) (s 1)) claim))
               #f
               (verify-rounds v (cdr degrees) g (s r) (cdr challenges)
                              prover-fn (append queries (list r))))]))))


;; # POLYNOMIAL

;; g : Polynomial
;; g(X_1,X_2,X_3) = 2X_1^3 + X_1X_3 + X_2X_3, evaluated modulo p.
(define (g assignments)
  (match assignments
    [(list x1 x2 x3)
     (modulo (+ (* 2 x1 x1 x1)
                (* x1 x3)
                (* x2 x3))
             p)]))

;; True sum over {0,1}^3: 12 mod 11 = 1
(define H
  (mod-sum
   (for*/list ([x1 '(0 1)] [x2 '(0 1)] [x3 '(0 1)])
     (g (list x1 x2 x3)))))

;; challenges : -> (List-of Distribution)
;; Samples the three random challenges r_1, r_2, r_3 uniformly from F_p.
(define (challenges)
  (list (finite-field p) (finite-field p) (finite-field p)))


;; # EVALUATION

;; [Completeness]
;; 1. Honest Prover, true claim H = 1 -> #t with probability 1
(verifier 3 '(3 1 1) g H (challenges) prover)

;; [Soundness]
;; 2. Honest Prover, false claim H = 3 -> #f with probability 1
(verifier 3 '(3 1 1) g 3 (challenges) prover)

;; 3. Malicious Prover, false claim H = 3 -> #t 531/1331, #f 800/1331
(verifier 3 '(3 1 1) g 3 (challenges) prover*)
;; Soundness Error: Pr[accept] = 531/1331 ~ 0.399 <= (3+1+1)/11 ~ 0.455 <= vd/p = 9/11 ~ 0.818
