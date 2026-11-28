# Sources and scope

1. **Yuk-Kam Lau and Jie Wu**, *On the least quadratic non-residue*,
   International Journal of Number Theory 4 (2008), Theorem 1.
   Author preprint:
   https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

   Their theorem gives
   \(n_\chi\ll_\varepsilon q^{1/(4\sqrt e)+\varepsilon}\)
   for a nonprincipal Dirichlet character of cube-free modulus \(q\),
   where \(n_\chi\) is the least positive integer at which the value is
   outside \(\{0,1\}\). It applies to both the prime-conductor
   \(r\)-power characters and the two-prime quadratic characters used
   here.

2. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   Repeated-power gcd splitting from a supplied exponent is standard.
   The present proof uses all small prime divisors \(r\le z\), rather
   than only repeated squaring.

3. **Jacek Pomykała and Maciej Radziejewski**, *Integer factoring and
   compositeness witnesses*, conference manuscript:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Algorithm 2 and Lemma 3.2 explicitly study witnesses of small prime
   order \(r\), including \(r\)-adic local-order layers and
   power-difference witnesses. They also first remove small prime
   factors. This is the closest general witness framework consulted.
   The present theorem uses only the simpler unequal-valuation part,
   falls back to a quadratic pair character on equal signature classes,
   allows arbitrary prime multiplicities after small-prime stripping,
   and records the output-sensitive all-pairs bottleneck \(H_z(N)\).

4. **Bartosz Źrałek**, *A deterministic version of Pollard's
   \(p-1\) algorithm*, Mathematics of Computation 79 (2010), 513--533,
   DOI 10.1090/S0025-5718-09-02262-5; preprint:
   https://arxiv.org/abs/0707.4102

   Section 3 supplies the direct prime/two-prime quadratic-character
   predecessor for the equal-\(2\)-adic-layer fallback.

5. Repository predecessor
   factor-known-exponent-all-pairs, pinned at commit
   7a6036e57ce329f3b10ba8b16a284bce4c736245.

   Its \(z=2\) theorem uses only the \(v_2(p-1)\) layer. The present
   result adds every prime \(r\le z\), after stripping those primes from
   the input so that reduction from prime powers preserves each
   \(r\)-part.

The theorem assumes a supplied multiple \(E\) of \(\lambda(N)\), with
polynomial bit length, and a polynomial-size trial parameter \(z\).
It does not construct \(E\), does not claim ordinary deterministic
polynomial-time factoring, and does not concern a concrete system or
key. The ingredients and broad small-order-witness framework are known;
no absolute priority claim is made for the exact signature bottleneck
formulation.
