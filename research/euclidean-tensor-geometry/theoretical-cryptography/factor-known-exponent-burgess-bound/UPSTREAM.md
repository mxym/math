# Sources and scope

1. **Yuk-Kam Lau and Jie Wu**, *On the least quadratic non-residue*,
   Theorem 1:
   https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

   They define \(n_\chi\) as the least positive integer at which a
   nonprincipal Dirichlet character takes a value outside
   \(\{0,1\}\), and prove
   \[
     n_\chi\ll_\varepsilon
     q^{1/(4\sqrt e)+\varepsilon}
   \]
   for cube-free \(q\) (with exponent \(1/(3\sqrt e)\) otherwise).
   This is the analytic input used here.

2. **Gary Miller**, *Riemann's hypothesis and tests for primality*
   (JCSS 1976), and the standard Miller/Rabin
   factor-from-an-exponent square chain. Under ERH, a logarithmic
   least-character-witness bound gives deterministic polynomial time.
   The present note instead inserts Lau--Wu's unconditional power
   bound.

3. **Bartosz Źrałek**, *A deterministic version of Pollard's
   \(p-1\) algorithm*, Mathematics of Computation 79 (2010),
   DOI 10.1090/S0025-5718-09-02262-5; preprint:
   https://arxiv.org/abs/0707.4102

   Section 3 uses the characters
   \((\cdot/p)\), \((\cdot/q)\), and \((\cdot/pq)\) in the three cases
   \(v_2(p-1)>v_2(q-1)\), \(<\), and \(=\), with Bach's ERH bound.
   Section 5 discusses deterministic reductions from supplied totient
   information. This is a direct structural predecessor.

4. **François Morain, Guénaël Renault, Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444, current
   text dated 2026-03-22:
   https://arxiv.org/abs/1802.08444

   Their Theorem 1.1 recovers a prime factor larger than \(\sqrt N\)
   in deterministic polynomial time from one exact \(\varphi(N)\) or
   \(\lambda(N)\), for squarefree \(N\) with at least three prime
   factors. It is used only for the smaller first-split corollary.

5. The repository result
   factor-exact-lambda-two-odd-primes, pinned at commit
   203b38b97d245e6b48c2b3695d31f390420b5568, supplies a
   self-contained deterministic exact-\(\lambda\) algorithm for at
   most two distinct odd primes, with arbitrary multiplicities. Only
   its squarefree two-prime candidate search is used here.

6. The repository note factor-known-exponent-grid-obstruction counts
   an infinite-family obstruction to a particular logarithmic
   small-base/smooth-stripping test. It is not a lower bound for all
   algorithms and does not conflict with the present power-size scan.

The complete-factor theorem accepts any short even multiple of
\(\lambda(N)\); the smaller first-split theorem requires the exact
value and a squarefree odd composite input. Neither theorem is an
ordinary deterministic polynomial-time factoring result. No claim is
made about a deployed system, and no absolute priority is claimed for
this synthesis.
