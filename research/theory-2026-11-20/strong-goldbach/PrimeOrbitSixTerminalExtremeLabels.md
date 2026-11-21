# A six-label orbit on smooth centers needs opposite size extremes

Fix a finite prime set F and odd prime p. Consider even F-smooth N coprime to p with an all-composite factor orbit of size six from p. Let q be its least label other than p, M its largest. Uniformly on such orbits as N→∞,

    log q/log N → 0,                         log M/log N → 1.

More precisely, put L=log N, T=L/log q. There is a constant C=C(F,p) for which, at all sufficiently large such centers,

    log(N/M) ≤ C log(2q) log(2T).                                          (1)

Consequently one row contains M to the first power with a cofactor between 3 and exp(C log(2q) log(2T)). Neither an achievable six-label pattern nor the existence of any Goldbach exception is asserted. Nor is q required to diverge by this result.

**Proof.** The [smooth six-label fork exclusion](PrimeOrbitSixSmoothTerminal.md) makes the whole orbit terminal and strongly connected. The [interior Eisenstein and six-label corollary](PrimeOrbitInteriorEisenstein.md) rules out every infinite sequence with q≥N^δ for any fixed δ>0. Hence T→∞. The [one-seed rank and feedback inequalities](PrimeOrbitMovingSeed.md) give nullity(I−A)=2. The six-by-six nonnegative exponent matrix A has diagonal zero and spectral radius ρ≥2. Its rank is at least five: rank ≤4 would give at least two algebraic zeros and two algebraic ones, and the trace would force the last eigenvalue after 0,0,1,1,ρ to equal −ρ−2, an impossibility.

The four columns other than the ones at p,q have entries of size ≤T: every one of their primes is at least q. Let J be t independent columns spanning those four (0≤t≤4). Since rank A≥5, one of the two marked columns increases their rank. From J and this marked column choose t+1 rows giving a nonsingular minor. On those rows use signed maximal minors of the t J-columns as the coordinates of c (for t=0, one coefficient 1); use zero on other rows. Thus c is integral, ||c||∞≤4! max(1,T)^4, it annihilates the four columns on the left, and at least one of u=cᵀA_{*,p} and b=cᵀA_{*,q} is nonzero. We have

    |u|≪_p L T⁴,              |b|≪ T⁵,                 |m|≪ T⁴,   m=Σ c_i.

The prime factorizations give the real logarithmic form

    Λ = u log p + b log q − m log N = Σ_i c_i log(1−x_i/N).

It is not zero: p and q are distinct primes each coprime to N and at least one of u,b is nonzero. Omit from F primes not dividing N (in particular p,q, if listed). Expand −m log N over its prime factors. Every coefficient on a fixed prime (including p) is O_{F,p}(L T⁴). Apply the real logarithm bound with normalized heights [Bugeaud, *B′*, Theorem 1.1, (1.3), pp. 2–3](https://arxiv.org/pdf/2209.00275) (Baker–Feldman; see also Matveev (1.5) there). Writing the marked q base last, each normalized coefficient of a fixed base is O(L T⁴/log q)=O(T⁵), and the q-coefficient is O(T⁵). The product of base heights is O_{F,p}(log(2q)). The theorem yields

    log |Λ| ≥ −C₁ log(2q) log(2T).

Here all bases are positive rationals with their real determinations. In (1.3) the denominators in the marked b_q term are the fixed-base heights (bounded below), and the other term divides by h*(q)≍log(2q). One may retain q as a base with coefficient zero when b=0; alternatively the fixed-base bound with u,mv_l(N)=O(LT⁴) costs O(log L+log(2T)), absorbed since log L=log T+log log q. Zero coefficients on other primes may be omitted; a single nonzero base is elementary.

As every label occurs in a composite row it is ≤(N−3)/3. Thus |log(1−x_i/N)|≤(3/2) x_i/N and |Λ|≤C₂T⁴ M/N. Combining the last two inequalities and absorbing 4 log T and the fixed constant proves (1). Finally log(2q)log(2T)/L→0 since T→∞ and q≥3. This gives the asserted logarithmic upper extreme. For a row with M as a factor, the cofactor is ≤N/M, and it is at least 3 since the complement is an odd composite. As M>√N eventually, it can occur only to exponent one.

This conclusion strengthens the earlier lower bound of [three macroscopic labels](PrimeOrbitMacroscopicRank.md) by quantifying two extremal sizes. It does not exclude the remaining high-label configurations.

**Dated comparison.** [Kelanemer, August 12, revised September 6, 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats related exponent-matrix reductions; the full text was not accessible for comparison. This estimate is conditional on an actual six-label orbit at fixed smooth centers and is not a priority claim or a Goldbach exclusion result in its own right.
