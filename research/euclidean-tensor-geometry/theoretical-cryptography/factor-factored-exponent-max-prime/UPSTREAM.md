# Sources and scope

1. **Yuk-Kam Lau and Jie Wu**, *On the least quadratic non-residue*,
   International Journal of Number Theory 4 (2008), Theorem 1.
   Author preprint:
   https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

   The theorem gives
   \[
   n_\chi\ll_\varepsilon q^{1/(4\sqrt e)+\varepsilon}
   \]
   for a nonprincipal Dirichlet character of cube-free modulus \(q\),
   where \(n_\chi\) is the least positive integer at which the value is
   outside \(\{0,1\}\). The statement is for general characters, so it
   applies to the prime-conductor \(r\)-power characters used here.

2. **Jacek Pomykała and Maciej Radziejewski**, *Integer factoring and
   compositeness witnesses*, conference manuscript:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Their Algorithm 2 and Lemma 3.2 study small-prime-order and
   power-difference witnesses after removing small factors. This is the
   closest broad multiradix witness framework consulted.

3. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444,
   version dated 22 March 2026:
   https://arxiv.org/abs/1802.08444

   Section 5.7 discusses using the complete factorization of
   \(\varphi(N)\) or \(\lambda(N)\). It notes that divisor enumeration can
   be large; the paper's conclusion explicitly says that complete
   factorizations of oracle values still do not give a known
   deterministic polynomial-time algorithm for all \(N\). The theorem
   here is consistent with that scope: it avoids divisor enumeration
   but gives a power-time \(P_E(N)^{1/(4\sqrt e)+\varepsilon}\) bound,
   not polynomial time.

4. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   Repeated-power gcd splitting from a supplied exponent is standard.
   The present proof uses every prime divisor in the supplied
   factorization of \(E\).

5. Repository predecessor
   factor-known-exponent-multiradix, pinned at commit
   e26f5a40dbca8113de927a0f2b4ca9cabdc2fe66.

   That theorem uses all primes up to a polynomial-size cutoff and needs
   a quadratic two-prime fallback inside equal-signature classes. Here,
   complete factorization advice for \(E\) allows the algorithm to visit
   all relevant coordinates directly, in only
   \(\operatorname{poly}(\log E)\) overhead. Full signatures are
   injective, so every pair uses a one-prime conductor and the quadratic
   fallback disappears.

The input includes \(E\) and its complete factorization, with
\(\lambda(N)\mid E\) and polynomial bit length. The theorem does not
construct or factor \(E\), does not claim ordinary deterministic
polynomial-time factoring, and does not concern a concrete system or
key. Its ingredients and the broad small-order-witness method are
known; no absolute priority claim is made for this exact
output-sensitive formulation.
