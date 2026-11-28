# Factoring from one totient on a prime graph with at most three components

A promise theorem in classical integer complexity. Given an odd integer N and its exact numeric Euler totient, consider the directed graph on its distinct prime divisors with p -> q if p divides q-1. For a fixed bound on the number of primes and a fixed bound on their largest/smallest ratio, this note proves deterministic polynomial-bit-time **complete factorization** if the graph has at most three weak components and at least one edge. Prime multiplicities are unknown, positive and unrestricted. No factoring of the totient, no additional oracle queries, no information identifying the primes or graph, and no additive closeness promise.

In particular, any qualifying four-prime input with an edge, or any qualifying five-prime input with at least two distinct edges, works. The three-component step uses three exact integer invariants and a finite-fiber proof, not lattice reduction. An explicit four-component example illustrates the limit of that proof, without suggesting computational hardness.

```
python3 -B verify_invariants.py
python3 -B verify_fibers.py
```

These are self-contained, deterministic finite checks of specified identities and certificates on known fixtures. They do not implement the factorization algorithm or justify the asymptotic claim by timing. See PROOF.md for the mathematical argument and UPSTREAM.md for the classical ingredients. No density, infinite supply of promised inputs, or claim on ordinary factorization is made.
