# Sources, prior art, and scope

1. **Yuk-Kam Lau and Jie Wu**, *On the least quadratic non-residue*,
   International Journal of Number Theory 4 (2008), Theorem 1.
   Author preprint:
   https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

   For a nonprincipal character of cube-free modulus \(q\), the least
   positive \(n\) with character value outside \(\{0,1\}\) is
   \(O_\varepsilon(q^{1/(4\sqrt e)+\varepsilon})\). Prime conductors are
   cube-free, and the theorem applies to the prime-power-order characters
   used in the proof.

2. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444,
   version dated 22 March 2026:
   https://arxiv.org/abs/1802.08444

   Section 5.7 discusses factoring when complete factorizations of
   \(\varphi(N)\) or \(\lambda(N)\) are available, and the conclusion
   keeps general deterministic polynomial-time factorization open.
   The present theorem supplies a precise support-advice reduction and a
   power-time bound; it does not close that general problem.

3. **Jacek Pomykała and Maciej Radziejewski**, *Integer factoring and
   compositeness witnesses*:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Their Algorithm 2 develops the small-prime-order and power-difference
   witness framework closest to the multiradix refinement used here.

4. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   Repeated-power gcd splitting from a supplied exponent is standard.

5. Repository predecessor:
   factor-factored-exponent-max-prime/, pinned at commit
   46afa65c4e8fd9999822dcdd8bfd492522cff0b7.

   That result assumes a fully factored multiple \(E\) of
   \(\lambda(N)\). The new step here is the exact reduction from only a
   promised prime-support superset \(\mathcal S\) to the polynomial-size
   factored multiple \(E_{\mathcal S}(N)\), including false positives and
   arbitrary multiplicities of the prime factors of \(N\).

A search of the sources above and targeted searches for factoring from
the prime support/radical of the Carmichael value did not locate this
exact support-only formulation. No absolute priority claim is made.
The advice may itself be difficult to obtain, and this result is neither
an ordinary polynomial-time factoring algorithm nor a claim about a
concrete cryptographic system.
