#lang racket
(require memoize)

;; Based on Professor Steven Holtzen's course on Programming with Probabilities
;; https://sholtzen.dev/fall26-pwp/Syntax_and_semantics.html
;; https://sholtzen.dev/fall26-pwp/Knowledge_Compilers.html

(provide symbolic-execution
         knowledge-compilation
         bdd-wmc
         compiler
         mk-not mk-and mk-or mk-xor
         (struct-out BddNode)
         (struct-out andE)
         (struct-out orE)
         (struct-out xorE)
         (struct-out notE)
         (struct-out letE)
         (struct-out flipE)
         (struct-out ifE)
         (struct-out varE)
         (struct-out andF)
         (struct-out orF)
         (struct-out xorF)
         (struct-out notF)
         (struct-out varF))

;; # TinyPPL DEFINITIONS

(struct andE (e1 e2) #:transparent)
(struct orE (e1 e2) #:transparent)
(struct xorE (e1 e2) #:transparent)
(struct notE (e) #:transparent)
(struct letE (var assgn body) #:transparent)
(struct flipE (p) #:transparent)
(struct varE (id) #:transparent)
(struct ifE (c t e) #:transparent)
;; A TinyPPL is one of:
;; - #t
;; - #f
;; - (flipE Number)
;; - (notE TinyPPL)
;; - (andE TinyPPL TinyPPL)
;; - (orE TinyPPL TinyPPL)
;; - (xorE TinyPPL TinyPPL)
;; - (varE Symbol)
;; - (letE Symbol TinyPPL TinyPPL)
;; - (ifE TinyPPL TinyPPL TinyPPL)
;; Interpretation: A high-level syntax, probablistic program.


;; # SYMBOLIC EXECUTION

;; A Var is a Natural
;; Interpretation: a variable that gets assigned every time flip runs.

(struct andF (e1 e2) #:transparent)
(struct orF (e1 e2) #:transparent)
(struct xorF (e1 e2) #:transparent)
(struct varF (var) #:transparent)
(struct notF (e) #:transparent)
;; A Formula is one of:
;; - #t
;; - #f
;; - (varF Var)
;; - (notF Formula)
;; - (andF Formula Formula)
;; - (orF Formula Formula)
;; - (xorF Formula Formula)
;; Interpretation: a Boolean formula

;; A WeightTable is a (Hash Var Number)
;; Interpretation: maps each variable f to the probability that f is #t.
;; The weight of ¬f is 1 minus that probability.

;; A Weighted Boolean Formula is a pair of
;; - phi, a Formula
;; - w, a WeightTable
;; Interpretation: the probability of a program evaluating to #t
;; is weighted model count of phi under w.

(define (mk-not a)
  (match a
    [#t #f]
    [#f #t]
    [(notF e) e]
    [_ (notF a)]))

(define (mk-and a b)
  (cond [(or (eq? a #f) (eq? b #f)) #f]
        [(eq? a #t) b]
        [(eq? b #t) a]
        [(eq? a b) a]
        [else (andF a b)]))

(define (mk-or a b)
  (cond [(or (eq? a #t) (eq? b #t)) #t]
        [(eq? a #f) b]
        [(eq? b #f) a]
        [(eq? a b) a]
        [else (orF a b)]))

(define (mk-xor a b)
  (cond [(eq? a #f) b]
        [(eq? b #f) a]
        [(eq? a #t) (mk-not b)]
        [(eq? b #t) (mk-not a)]
        [(eq? a b) #f]
        [else (xorF a b)]))

;; symbolic-execution : TinyPPL -> (values Formula WeightTable)
;; Returns a Weighted Boolean Formula given a TinyPPL program.
;; (technically not a WBF pair and instead returns as two sepearte values).
(define (symbolic-execution e)
  ;; weights : (Mutable-Hash Var Number)
  (define weights (make-hash))
  ;; fresh-var! : Number -> Var
  ;; Mutation - New flip variable
  (define (fresh-var! p)
    (let [(v (hash-count weights))]
      (hash-set! weights v p)
      v))
  ;; se-inner : TinyPPL (Hash Symbol Formula) -> Formula
  (define (se-inner e env)
    (match e
      [#t #t]
      [#f #f]
      [(flipE p)
       (varF (fresh-var! p))]
      [(notE e1)
       (mk-not (se-inner e1 env))]
      [(andE e1 e2)
       (mk-and (se-inner e1 env) (se-inner e2 env))]
      [(orE e1 e2)
       (mk-or  (se-inner e1 env) (se-inner e2 env))]
      [(xorE e1 e2)
       (mk-xor (se-inner e1 env) (se-inner e2 env))]
      [(varE x)
       (hash-ref env x)]
      [(letE x assgn body)
       (se-inner body (hash-set env x (se-inner assgn env)))]
      [(ifE c t e)
       (let ([rc (se-inner c env)]
             [rt (se-inner t env)]
             [re (se-inner e env)])
         (mk-or (mk-and rc rt)
              (mk-and (mk-not rc) re)))]))

  ;; Return an immutable copy for the WeightMap (helps with testing, equal?, etc)
  (values (se-inner e (hash))
          (for/hash ([(k v) (in-hash weights)]) (values k v))))


;; # Knowledge Compilation

(struct BddNode (v h l))
;; A BDD is one of
;; - #t
;; - #f
;; - (BddNode Var BDD BDD)
;; Interpretation: #t and #f are nodes
;; if v then h else l
;; Invariants:
;; - Ordered: each variable is encountered in a fixed order starting from the root note
;; (variables of children nodes larger than those of parent nodes)
;; - Reduced: structurally identical BDD childrens are merged into a single BDD
;; - Canonical: exactly one BDD for every Boolean Function (for a particular order)

;; bdd-table : (Hash (List Var BDD BDD) BddNode)
(define bdd-table (make-hash))

;; mk-node : Var BDD BDD -> BDD
;; create a new canonical BddNode
(define (mk-node v h l)
  ;; canonicalize : BddNode -> BddNode
  ;; Returns the existing node with the same fields as bn if there is one;
  ;; otherwise set new BddNode in the bdd-table and returns it.
  (define (canonicalize bn)
    (hash-ref! bdd-table
               (list (BddNode-v bn) (BddNode-h bn) (BddNode-l bn))
               bn))
  (if (eq? h l)
      h
      (canonicalize (BddNode v h l))))

;; bdd-mk-var : Var -> BDD
;; Builds the BDD for the formula consisting of the single variable v.
(define (bdd-mk-var v)
  (mk-node v #t #f))

;; bdd-and : BDD BDD -> BDD
;; Computes the BDD for the conjunction f ∧ g.
(define/memo (bdd-and f g)
  (match (list f g)
    [(list #t x) x]
    [(list x #t) x]
    [(list _ #f) #f]
    [(list #f _) #f]
    [(list x y) #:when (eq? x y) x]
    [(list (BddNode v1 h1 l1) (BddNode v2 h2 l2))
     (if (= v1 v2)
         ; if variables are equal, recurse
         (mk-node v1 (bdd-and h1 h2) (bdd-and l1 l2))
         ; otherwise, find the first essential and recurse
         ; on that one
         (if (< v1 v2)
             (mk-node v1 (bdd-and h1 g) (bdd-and l1 g))
             (mk-node v2 (bdd-and h2 f) (bdd-and l2 f))))]))

;; bdd-or : BDD BDD -> BDD
;; Computes the BDD for the disjunction f ∨ g.
(define/memo (bdd-or f g)
  (match (list f g)
    [(list #t _) #t]
    [(list _ #t) #t]
    [(list #f x) x]
    [(list x #f) x]
    [(list x y) #:when (eq? x y) x]
    [(list (BddNode v1 h1 l1) (BddNode v2 h2 l2))
     (if (= v1 v2)
         ; if variables are equal, recurse
         (mk-node v1 (bdd-or h1 h2) (bdd-or l1 l2))
         ; otherwise, find the first essential and recurse
         ; on that one
         (if (< v1 v2)
             (mk-node v1 (bdd-or h1 g) (bdd-or l1 g))
             (mk-node v2 (bdd-or f h2) (bdd-or f l2))))]))

;; bdd-xor : BDD BDD -> BDD
;; Computes the BDD for the exclusive or f ⊕ g.
(define/memo (bdd-xor f g)
  (match (list f g)
    [(list #f x) x]
    [(list x #f) x]
    [(list #t x) (bdd-not x)]
    [(list x #t) (bdd-not x)]
    [(list x y) #:when (eq? x y) #f]
    [(list (BddNode v1 h1 l1) (BddNode v2 h2 l2))
     (if (= v1 v2)
         (mk-node v1 (bdd-xor h1 h2) (bdd-xor l1 l2))
         (if (< v1 v2)
             (mk-node v1 (bdd-xor h1 g) (bdd-xor l1 g))
             (mk-node v2 (bdd-xor h2 f) (bdd-xor l2 f))))]))

;; bdd-not : BDD -> BDD
;; Computes the BDD for the negation ¬f by swapping the terminal nodes.
(define/memo (bdd-not f)
  (match f
    [#t #f]
    [#f #t]
    [(BddNode v h l)
     (mk-node v (bdd-not h) (bdd-not l))]))

;; knowledge-compilation : Formula -> BDD
(define (knowledge-compilation phi)
  (define cache (make-hasheq))
  (define (kc phi)
    (hash-ref! cache phi
               (λ ()
                 (match phi
                   [#t #t]
                   [#f #f]
                   [(varF v)
                    (bdd-mk-var v)]
                   [(notF e)
                    (bdd-not (kc e))]
                   [(andF e1 e2)
                    (bdd-and (kc e1) (kc e2))]
                   [(orF e1 e2)
                    (bdd-or (kc e1) (kc e2))]
                   [(xorF e1 e2)
                    (bdd-xor (kc e1) (kc e2))]))))
  (kc phi))


;; # Weighted Model Counting

;; bdd-wmc : BDD WeightTable -> Number
;; BDD weighted model counting
;; Returns the probabilty of the BDD resulting in #t
(define (bdd-wmc bdd w)
  (define/memo (bdd-wmc-inner b)
    (match b
      [#t 1]
      [#f 0]
      [(BddNode v h l)
       (+ (* (bdd-wmc-inner h) (hash-ref w v))
          (* (bdd-wmc-inner l) (- 1 (hash-ref w v))))]))
  (bdd-wmc-inner bdd))


;; # Inference Result

;; compiler : TinyPPL -> Number
(define (compiler p)
  (define-values (f w) (symbolic-execution p))
  (bdd-wmc (knowledge-compilation f) w))
