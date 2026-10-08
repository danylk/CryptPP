#lang roulette/example/disrupt

;; Reed-Solomon Fingerprint Protocol
;; Based on "Proofs, Arguments, and Zero-Knowledge" by Jusin Thaler

;; -----------------------------------------------------------------------------
;; PRIMITIVES
;; -----------------------------------------------------------------------------

;; eval-poly : (Listof Natural) Natural Natural -> Natural
;; Evaluates a polynomial P(x) = c0 + c1*x + c2*x^2 + ... at point r modulo p.
(define (eval-poly coeffs r p)
  (foldr (lambda (c acc)
           (modulo (+ c (* r acc)) p))
         0
         coeffs))

;; sample-field-element : Natural -> Natural
;; Samples a uniform random element r from F_p = {0, 1, ..., p-1}.
(define (sample-field-element p)
  ;; Sample a uniform choice over [0, p-1] using flip/uniform selection
  (make-categorical (for/list ([i (in-range p)])
                      (cons i (/ 1 p)))))

;; -----------------------------------------------------------------------------
;; REED-SOLOMON FINGERPRINTING PROTOCOL
;; -----------------------------------------------------------------------------

;; rs-fingerprint-game : (Listof Natural) (Listof Natural) Natural -> Boolean
;; Evaluates whether Bob accepts that Data A and Data B are identical.
;; Returns #t if fingerprints match (accept), #f if they differ (reject).
(define (rs-fingerprint-game data-A data-B prime)
  ;; Bob picks a random evaluation challenge point r in F_p
  (define r (sample-field-element prime))
  
  ;; Alice and Bob compute fingerprints
  (define fp-A (eval-poly data-A r prime))
  (define fp-B (eval-poly data-B r prime))
  
  ;; Verifier accepts if fingerprints match
  (equal? fp-A fp-B))

;; -----------------------------------------------------------------------------
;; VERIFICATION & PROBABILISTIC INFERENCE
;; -----------------------------------------------------------------------------

;; Field prime p = 7
(define p 7)

;; Case 1: Identical Data vectors (Degree d <= 3)
;; P_A(x) = 1 + 2x + 3x^2
(define A1 '(1 2 3))
(define B1 '(1 2 3))

;; Case 2: Distinct Data vectors (Degree d - 1 = 2)
;; P_A(x) = 1 + 2x + 3x^2
;; P_B(x) = 1 + 5x + 3x^2
;; Difference polynomial has degree 1 -> At most 1 root in F_7
(define A2 '(1 2 3))
(define B2 '(1 5 3))

;; Case 3: Distinct Data vectors with degree d - 1 = 2
;; P_A(x) = 1 + 2x + 3x^2
;; P_B(x) = 1 + 2x + 5x^2
;; Difference polynomial 2x^2 = 0 -> Roots at r = 0 in F_7 (1 root)
(define A3 '(1 2 3))
(define B3 '(1 2 5))

;; -----------------------------------------------------------------------------
;; EVALUATION & SCHWARTZ-ZIPPEL BOUNDS
;; -----------------------------------------------------------------------------

;; 1. Completeness: If A = B, Pr[Fingerprints Match] = 1
(rs-fingerprint-game A1 B1 p)
;; Expected Output: #hash((#t . 1))

;; 2. Soundness / False Positive Collision (Case 2):
;; Difference degree = 1, Max roots = 1.
;; Collision probability = 1/7
(rs-fingerprint-game A2 B2 p)
;; Expected Output: #hash((#t . 1/7) (#f . 6/7))

;; 3. Soundness / False Positive Collision (Case 3):
;; Difference degree = 2, Max roots = 2 (r = 0).
;; Collision probability = 1/7
(rs-fingerprint-game A3 B3 p)
;; Expected Output: #hash((#t . 1/7) (#f . 6/7))
