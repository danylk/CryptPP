# CryptPP: Cryptography with Probabilistic Programming

## What is CryptPP?
CryptPP is a project that uses the probabilistic programming language [Roulette](https://docs.racket-lang.org/roulette/index.html) to analyze cryptographic proofs.

## Security Games 
### [Semantic Security](semantic_security.rkt)
Semantic Security based on Dan Boneh and Victor Shoup's "A Graduate Course in Applied Cryptography" (2023)

```mermaid
sequenceDiagram
    autonumber
    actor A as Adversary (A)
    participant G as Attack Game (b)
    participant C as Cipher (E)

    Note over A, C: Phase 1: Message Choice & Setup
    A->>G: choose(l) → (m0, m1)
    Note over G: Sample uniform key: k ← {0,1}^l

    Note over A, C: Phase 2: Challenge Encryption
    alt b = 0
        G->>C: encrypt(k, m0)
    else b = 1
        G->>C: encrypt(k, m1)
    end
    C-->>G: Ciphertext c
    G->>A: Send c

    Note over A, C: Phase 3: Guess & Advantage Evaluation
    A->>A: guess(c) → b_guess
    A->>G: Output b_guess

    Note over G: Evaluates: (equal? b_guess 1)
    Note over G: W_b = Event that A outputs 1 in Experiment b

    rect rgb(240, 248, 255)
        Note over A, G: Outcome Comparison
        Note over G: One-Time Pad (cipher-bitwise):<br/>Pr[W0] = 1/2, Pr[W1] = 1/2  ⟹  Advantage |Pr[W0] - Pr[W1]| = 0
        Note over G: Identity Cipher (cipher-identity):<br/>Pr[W0] = 0,   Pr[W1] = 1    ⟹  Advantage |Pr[W0] - Pr[W1]| = 1
    end
```
    
## Proof Games
### [Reed-Solomon Fingerprint Protocol](reed_solomon_fingerprint.rkt)
Reed-Solomon Fingerprint Protocol based on Justin Thaler's "Proofs, Arguments, and Zero-Knowledge" (2023)
