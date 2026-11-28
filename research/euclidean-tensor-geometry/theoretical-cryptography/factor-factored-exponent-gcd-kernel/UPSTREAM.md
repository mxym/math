# Sources and scope

1. **Jacek Pomykała and Maciej Radziejewski**, *Integer factoring and
   compositeness witnesses*, conference manuscript:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Their Algorithm 2 and Lemma 3.2 develop small-prime-order and
   power-difference witnesses after removing small factors. This is the
   closest broad witness framework consulted. The present proof uses an
   elementary pairwise subgroup count to obtain the explicit
   \(\gcd(p-1,q-1)+1\) stopping scale, then applies all factored-exponent
   chains simultaneously.

2. **François Morain, Guénaël Renault, and Benjamin Smith**,
   *Deterministic factoring with oracles*, arXiv:1802.08444,
   version dated 22 March 2026:
   https://arxiv.org/abs/1802.08444

   Section 5.7 discusses the extra information in complete
   factorizations of \(\varphi(N)\) or \(\lambda(N)\), while emphasizing
   that this still does not give a known deterministic polynomial-time
   algorithm for every input. The present bound is compatible: it is
   polynomial only for inputs whose residual pairwise gcd scale is
   polynomial in the bit length.

3. **Factored-advice prime-conductor theorem**, repository commit
   46afa65c4e8fd9999822dcdd8bfd492522cff0b7,
   directory factor-factored-exponent-max-prime.

   It gives the independent
   \(P_E(N)^{1/(4\sqrt e)+\varepsilon}\) stopping bound used only in the
   hybrid corollary. The elementary \(G_E(N)\) theorem itself does not
   use Lau--Wu or any analytic character estimate.

4. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   Repeated-power gcd splitting from a supplied exponent is standard.

The input includes a completely factored multiple \(E\) of
\(\lambda(N)\). The theorem does not construct or factor \(E\), does
not claim polynomial time for unrestricted inputs, and does not concern
a concrete system or key. Its group-theoretic ingredients are
elementary and the broad witness framework is known; no absolute
priority claim is made for the exact GCD-kernel bottleneck formulation.
