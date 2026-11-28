# Sources, comparison, and search scope

1. **Konyagin--Pomerance smooth-number lower bound**, used in the form
   recorded as Lemma 4.2 of:

   **Jacek Pomykała and Maciej Radziejewski**,
   *Integer factoring and compositeness witnesses*,
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   For \(x\ge4\) and \(2\le y\le x\),
   \[
     \Psi(x,y)>x^{1-\log\log x/\log y}.
   \]
   Their Algorithm 2 is also the closest consulted small-prime-order /
   power-difference witness framework.

2. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444:
   https://arxiv.org/abs/1802.08444

   Lemma 5.3 proves that for a distinct-prime semiprime,
   \[
     \varphi(N)=\lambda(N)\gcd(N-1,\lambda(N)).
   \]
   Thus the *exact value* of \(\lambda(N)\) already yields polynomial
   time. The present input is weaker: only a prime-support superset is
   given, with no Carmichael value or exponents.

3. Repository dependencies, pinned:

   * factor-carmichael-support-advice/, commit
     4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc;
   * factor-factored-exponent-smooth-kernel/, commit
     42e70b4c5310678a9c628b82d29238bf9229e40b.

   The first synthesizes a polynomial-size fully factored exponent
   multiple from support advice. The second proves the exact
   smooth-number subgroup escape. The current proof includes the needed
   arguments so that its theorem can be checked without mutable files.

4. General deterministic baseline:

   **David Harvey and Markus Hittmeir**,
   *A log-log speedup for exponent one-fifth deterministic integer
   factorisation*, Mathematics of Computation 91 (2022), 1367--1379,
   DOI: https://doi.org/10.1090/mcom/3708

   It gives a deterministic \(N^{1/5}\) general-input bound up to the
   stated logarithmic improvement. The present subexponential bound is
   only for promised semiprimes with support advice.

Targeted searches for deterministic semiprime factoring from only the
prime support/radical of the Carmichael value did not locate this hybrid
cofactor-enumeration and smooth-subgroup bound. No absolute priority
claim is made. The theorem does not extend to arbitrary numbers, does
not obtain the advice, and makes no claim about a concrete system.
