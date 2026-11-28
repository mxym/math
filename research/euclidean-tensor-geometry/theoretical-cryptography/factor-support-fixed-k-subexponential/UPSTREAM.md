# Sources, comparison, and search scope

1. **Jacek Pomykała and Maciej Radziejewski**,
   *Integer factoring and compositeness witnesses*:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Lemma 4.2 records the Konyagin--Pomerance lower bound
   \[
     \Psi(x,y)>x^{1-\log\log x/\log y}
   \]
   for \(x\ge4\), \(2\le y\le x\). Their Algorithm 2 is the closest
   consulted small-order / power-difference witness framework.

2. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444:
   https://arxiv.org/abs/1802.08444

   The paper studies exact \(\Phi\), \(\Lambda\), order, and
   sum-of-divisors oracles. In particular, Lemma 5.3 gives a
   polynomial-time two-prime reduction from the exact value
   \(\lambda(N)\). The input here is different and weaker: it is only a
   prime-support superset, with no Carmichael value or exponents.

3. Repository predecessors, pinned:

   * factor-carmichael-support-advice/, commit
     4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc;
   * factor-factored-exponent-smooth-kernel/, commit
     42e70b4c5310678a9c628b82d29238bf9229e40b;
   * factor-support-semiprime-subexponential/, commit
     b91c59cfd04eb83aa85aef7a08a4bba89ad0b905.

   The first constructs a factored exponent multiple from support
   advice. The second proves the subgroup escape. The third is precisely
   the \(K=2\) instance of the theorem here. The current proof repeats
   the needed arguments and adds the bounded-ratio monotone-polynomial
   reconstruction for every fixed \(K\).

4. General deterministic baseline:

   **David Harvey and Markus Hittmeir**,
   *A log-log speedup for exponent one-fifth deterministic integer
   factorisation*, Mathematics of Computation 91 (2022), 1367--1379,
   DOI: https://doi.org/10.1090/mcom/3708

   This is an unconditional general-input power-time result. The theorem
   here is subexponential only because both the fixed-\(K\) promise and
   the support advice are part of the input.

Targeted searches did not locate this exact fixed-\(K\), support-only
hybrid of subgroup escape and rational-ratio reconstruction. No absolute
priority claim is made. The theorem neither obtains its advice nor
extends to unboundedly many prime factors, and it makes no statement
about a concrete cryptographic system.
