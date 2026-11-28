# Prior work and scope

1. **Nikhil Gupta, Alan Sikarov, Ilya Volkovich**, *A Computational
   Perspective on Carmichael Numbers*, ECCC TR26-212 (2026):
   https://eccc.weizmann.ac.il/report/2026/212/
   and the fixed report:
   https://eccc.weizmann.ac.il/report/2026/212/download/

   Their exact-lambda polynomial-time theorem is for **simple** C3
   Carmichael numbers.  Their square-decoding identity and normal form
   are used and rederived here.  This package does not relabel that
   theorem as new.  It instead covers every C3 Carmichael radical, with
   a numerical rather than bit-polynomial bound.

2. **François Morain, Guénaël Renault, Benjamin Smith**, *Deterministic
   factoring with oracles*, Applicable Algebra in Engineering,
   Communication and Computing (2023), DOI:
   https://doi.org/10.1007/s00200-021-00521-8

   Their reductions and bounded-root viewpoint are relevant context.
   Their arbitrary-power reduction uses additional oracle access; this
   package uses only the one supplied exact lambda value and handles
   multiplicities by (25).

3. **Don Coppersmith**, *Finding a small root of a univariate modular
   equation*, EUROCRYPT 1996, DOI:
   https://doi.org/10.1007/3-540-68339-9_14
   and **Nick Howgrave-Graham**, *Finding small roots of univariate
   modular equations revisited*, 1997, DOI:
   https://doi.org/10.1007/BFb0024458

   These are the classical LLL/small-root antecedents.  The present
   two-modulus lemma is proved directly from the standard LLL length
   bound; it is not treated as a black-box heuristic theorem.

4. **Keegan Ryan**, *Solving Multivariate Coppersmith Problems with
   Known Moduli*, ePrint 2024/1577:
   https://eprint.iacr.org/2024/1577

   This is a modern framework for shift-polynomial ideals and known
   multiples of moduli.  Some of its full multivariate recovery steps
   are explicitly heuristic.  It is cited only as general technique
   context.  The result in this package is one-variable and its
   determinant/divisibility argument is self-contained.

5. The repository companion
   `factor-c3-exact-lambda-one-thirteenth`, pinned at
   `e721870cbb93ea8b60e034b5386348d04535d0ca`, gives the earlier
   all-C3 exponent (1/13), the complete progression/cubic mechanics,
   and finite arithmetic checkers.  The present proof strictly improves
   that numerical exponent to (3/50); it does not change the frozen
   companion.

No statement here gives ordinary deterministic polynomial-time
factoring, a result for an arbitrary multiple of lambda, or a conclusion
about a deployed cryptographic system.
