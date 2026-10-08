#lang roulette/example/disrupt

;; Semantic Security Cryptanalysis
;; Based on "A Graduate Course in Applied Cryptography" by Dan Boneh and Victor Shoup

;; -----------------------------------------------------------------------------
;; PRIMITIVES
;; -----------------------------------------------------------------------------

;; bit-xor : Bit Bit -> Bit
;; Computes the bitwise exclusive-OR (XOR) of two binary bits (0 or 1).
(define (bit-xor a b)
  (if (equal? a b) 0 1))

;; bitwise-xor : (Listof Bit) (Listof Bit) -> (Listof Bit)
;; Computes element-wise XOR of two equal-length bit vectors.
(define (bitwise-xor b1 b2)
  (map bit-xor b1 b2))

;; sample-bit : -> Bit
;; Samples a single bit uniformly at random from {0, 1}.
(define (sample-bit)
  (if (flip 1/2) 1 0))

;; sample-bits : Natural -> (Listof Bit)
;; Generates a probabilistic list of n bits sampled uniformly at random.
(define (sample-bits n)
  (for/list ([i (in-range n)])
    (sample-bit)))

;; -----------------------------------------------------------------------------
;; ADVERSARIES
;; -----------------------------------------------------------------------------

;; Adversary 1: Random Guesser
(define adversary-rand-guess
  (hash
   'choose (lambda (l)
             (values (sample-bits l) (sample-bits l)))
   'guess  (lambda (c)
             (sample-bit))))

;; Adversary 2: Breaks insecure ciphers (e.g., identity cipher)
(define adversary-first-bit
  (hash
   'choose (lambda (l)
             (values (make-list l 0) (make-list l 1)))
   'guess  (lambda (c)
             (if (equal? (car c) 0) 0 1))))

;; -----------------------------------------------------------------------------
;; CIPHERS
;; -----------------------------------------------------------------------------

;; Secure Cipher: One-Time Pad
(define cipher-bitwise
  (hash
   'encrypt (lambda (k m) (bitwise-xor k m))
   'decrypt (lambda (k c) (bitwise-xor k c))))

;; Insecure Cipher: Identity Cipher (returns message unencrypted)
(define cipher-identity
  (hash
   'encrypt (lambda (k m) m)
   'decrypt (lambda (k c) c)))

;; -----------------------------------------------------------------------------
;; SECURITY GAME
;; -----------------------------------------------------------------------------

;; attack-game : Cipher Adversary Natural -> Distribution
;; Runs the IND-CPA / Semantic Security game and returns outcome distribution.
(define (attack-game b cipher adversary l)
  (define-values (m0 m1) ((hash-ref adversary 'choose) l))
  (define k (sample-bits l))
  ;; Fixed: used equal? instead of = to avoid symbolic contract errors
  (define c ((hash-ref cipher 'encrypt) k (if (equal? b 0) m0 m1)))
  (define b-guess ((hash-ref adversary 'guess) c))
  (equal? b-guess 1))

;; -----------------------------------------------------------------------------
;; EVALUATION
;; -----------------------------------------------------------------------------

;; 1. One-Time Pad against smart adversary -> #hash((#t . 1/2) (#f . 1/2)) [Advantage = 0]
(attack-game 0 cipher-bitwise adversary-first-bit 10)
(attack-game 1 cipher-bitwise adversary-first-bit 10)
;; Adversary Advantage: |Pr[W_0] - Pr[W_1]| = 0

;; 2. Identity Cipher against smart adversary -> #hash((#t . 1) (#f . 1)) [Advantage = 1]
(attack-game 0 cipher-identity adversary-first-bit 10)
(attack-game 1 cipher-identity adversary-first-bit 10)
;; Adversary Advantage: |Pr[W_0] - Pr[W_1]| = 1
