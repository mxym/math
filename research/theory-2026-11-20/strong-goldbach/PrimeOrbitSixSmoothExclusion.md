# A fixed prime's all-composite forward orbit has at least seven labels at large smooth centers

Fix an odd prime p and a finite prime alphabet F. At all sufficiently large even F-smooth N coprime to p, start at p and iteratively adjoin every prime divisor of N−x for each reached prime x. If all reached complements are composite, the resulting orbit has **at least seven distinct primes**. In particular this necessary condition holds at any hypothetical Goldbach failure on these centers. There is no asserted upper bound for N, no assertion that all seven labels belong to one terminal component, and no exclusion of larger orbits or of Goldbach failures. The threshold is not claimed effective.

The [moving-seed lower bound](PrimeOrbitMovingSeed.md) already rules out at most five. If an unbounded sequence had exactly six, the [four-macro exclusion and three-macro parametrization](PrimeOrbitFourMacroExclusion.md) show that its small primes S={p,q,r} (q<r) satisfy q,r→∞ and there is a positive even h such that **every 1+hs, s∈S, factors entirely in S**. Divergence of q uses the [two-seed consequence](PrimeOrbitMultiSeedMinimal.md). This final, moving-alphabet multiplier system itself is impossible, independently of N. The proof follows.

## The multiplier lemma and the right choice of scale

**Lemma.** Fix a prime p. There is no sequence of positive even integers h and triples of distinct odd primes {p,q,r}, with q<r and q→∞, for which every 1+hs factors over {p,q,r}. Unlike a fixed-alphabet S-unit finiteness theorem, both q and r can vary here.

Direct edges from s to factors of 1+hs. There are no loops and no sinks. If a terminal strongly connected component has size two, its two multipliers are 1+hu=v^a, 1+hv=u^b, with a,b≥1. The auxiliary even center u+v^{a+1}=v+u^{b+1} then has a two-label nontrivial strongly connected factor-closed component {u,v} with both rows composite. By [Bożek, Theorem 3.7](https://arxiv.org/abs/1909.09900), the pair is {3,13}; impossible eventually since only one of p,q,r can stay bounded. Hence the three-label multiplier support is strongly connected. In particular q≤1+hp (the multiplier at p has at least one of q,r as factor), and r≤1+hq (r must occur in the multiplier of p or q). Thus h→∞. In this proof the large height parameter is **L=log h**, not log N.

Let s=(p,q,r) and let G_{ij}=v_{s_j}(1+h s_i)−δ_{ij}. With real logarithms the three exact equations are

    (G log s)_i = L+ε_i,           ε_i=log(1+1/(h s_i)).

First, q cannot be subpower in h on any subsequence. Suppose T=L/log q→∞. Because log r=O(L), all entries in the r-column of G are O(1+L/log r). Choose a nonzero integer c annihilating the all-ones and r-columns on the left with |c_i|≪1+L/log r≤O(T): use their 2-by-2 signed minors if independent, or any bounded vector of sum zero otherwise. We have

    U log p + V log q = Σ c_i ε_i = O(T/h),   |U|≪ LT,   |V|≪T².

If the left side is nonzero, the [normalized real logarithm bound, Bugeaud, Theorem 1.1 (1.3)](https://arxiv.org/pdf/2209.00275) gives log absolute value ≥−C_p log q log(2T): the q-exponent is O(T²), while the p-exponent divided by log q is O(T²). This is −o(L), impossible. A single nonzero log term is even simpler. So Σc_i ε_i=0 exactly, in addition to Σc_i=0.

If log r/log h has a positive limit on a further subsequence, c is bounded and can be fixed. Multiplying Σc_i ε_i=0 by h and taking the limit q,r→∞ yields c_p/p=0. Then c_q=−c_r≠0 forces ε_q=ε_r, impossible. In the other case pass to log r/log h→0. All s_i and c_i are h^{o(1)}. Expanding each log to first order gives |Σc_i/s_i|≪max|c_i|/h; its rational denominator divides pqr=h^{o(1)}, so this sum vanishes. Expanding to second order then gives |Σc_i/s_i²|≪max|c_i|/h, which also vanishes since the denominator divides (pqr)². The vectors with entries 1,1/s_i,1/s_i² form an invertible Vandermonde matrix, contrary to c≠0. These alternatives exhaust limiting subsequences. We may therefore work with log q≥ηL for some fixed η>0 along the putative sequence (otherwise there is a subsequence with T→∞).

## Two coordinates recover their leading powers of the fixed seed

Now both the q- and r-columns of G are bounded integers; fix them on a subsequence. Their two row differences (subtract, say, the p-row from the q- and r-rows) form an invertible 2-by-2 matrix. Otherwise there is a fixed nonzero integral c annihilating the ones, q and r columns. Then the integer cᵀG_{*,p} times log p equals Σc_i ε_i=O(1/h), hence is zero. As above the fixed c would have c_p=0 and then ε_q=ε_r. This proves invertibility, not merely independence of each nonseed column individually.

Solving the two row differences, for each y=q,r we obtain

    log y = A_y log p + Σ_i k_{yi} ε_i.                            (1)

Here k_{yi} are fixed rationals, and A_y is rational with a fixed common denominator D (the nonzero determinant's absolute value suffices); the p-column of G can vary. Since ε_i=O(1/h), p^{A_y} grows like y. Pass to a subsequence fixing the fractional parts A_y, so p^{A_y}=α_y p^{m_y} with α_y fixed positive algebraic and m_y a positive integer tending to infinity.

In fact log q/log h→1. The upper limit is at most one because q≤hp+1. If q≤h^{1−δ} on a subsequence, (1) gives |q−α_q p^{m_q}|≪q/h≪h^{−δ}. Apply the [p-adic Subspace Theorem, Evertse's notes, Theorem 1.1](https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf) to (X,Y)=(q,p^{m_q}): use X−α_qY,Y at infinity and the coordinate forms at p. The product is the small archimedean error since Y's real and p-adic factors cancel and q is a p-unit. The vector is primitive of height O(h); a power saving gives finitely many rational ratios, impossible since the prime q→∞ is distinct from p. It follows that both q and r are at least h^{1−o(1)}.

The multiplier 1+hp contains no p. Two factors, even if equal, from q,r would exceed 1+hp. Thus **y=1+hp** is one of the two primes q,r, to the first power. Fix which one, and denote the other by z. Apply (1) specifically to y and let k=k_{yp}, the coefficient on the fixed-input correction ε_p. Since y=1+hp,

    y−p^{A_y}=y(1−exp(−Σε_i k_{yi}))=k+O(h^(−1+o(1))).

Indeed y ε_p=1+O(1/h), y ε_q and y ε_r are O(1/q+1/r), and y(Σε_i k_{yi})²=O(1/h). At both places use the same Subspace Theorem now on (y−k,p^{m_y}), clearing the fixed denominator of k. Its archimedean small form is X−α_yY. The product of the linear forms is O(h^{−1+o(1)}), since |y−k|_p is bounded by a fixed constant. For a primitive-integer formulation multiply by a fixed denominator d, then divide by the gcd: its prime factors outside p divide d to bounded order, and its p-power rescales with exactly cancelling real and p-adic factors. Heights are O(h). Thus there are only finitely many rational projective ratios (bounded primitive vectors also have this property). On an infinite subsequence of fixed ratio, the archimedean error tends to zero while p^{m_y}→∞, forcing that ratio to equal α_y. Consequently α_y is rational, its fractional exponent of the prime p is zero, and

    y=p^a+k,                 a∈Z_{>0},  a→∞,    k∈Z fixed.            (2)

This step uses an extra Taylor term; first-order relative approximation alone would not yield the affine integer identity.

## The two remaining multipliers

We have 1+hy=p^b z^f with f≥1: z must occur by the just-proved strong connectivity, since p's only successor is y and a p-only row at y would close the pair. Now

    p^{b+1} z^f = y²−y+p.

The p-adic valuation of the right side is eventually *fixed*, because at y=p^a+k its constant term in p^a is k²−k+p>0. Thus b is fixed. Since both possible choices of z exceed h^{1−o(1)}, while 1+hy is O(h²), f≤2 eventually.

If f=2, the same Subspace Theorem alone rules it out: z=p^{−(b+1)/2}(p^a+k−1/2)+O(p^{−a}). On (z,p^a,1) take the corresponding error form and the second and third coordinates at infinity, and the coordinate forms at p. Their product is O(p^{−a}), since z is a p-unit. A proper rational plane on an infinite subsequence must express z as an affine rational function of p^a. Substitution would make the nonzero-discriminant quadratic a scalar times a perfect square polynomial, an impossibility.

We are left with f=1, z=(y²−y+p)/p^{b+1}, and

    1+hz = [(y−1)(y²−y+p)+p^{b+2}]/p^{b+2}.

The numerator modulo the growing prime y equals the fixed nonzero p^{b+2}−p. Hence y does not divide this multiplier eventually; z cannot divide its own multiplier either, so it must be a pure power of p. Write Q(T)=(T−1)(T²−T+p)+p^{b+2}. For increasing a, Q(p^a+k) would be a pure p-power. Factor the greatest power T^j from Q(T+k), leaving an integral polynomial R(T) with nonzero constant term. The valuations of R(p^a) are eventually fixed; as these positive integers divide pure p-powers they remain bounded, forcing R constant. Since Q is monic cubic, this means Q(T)=(T−k)³. But its quadratic coefficient is −2, which would give 3k=2, contrary to integer k. This proves the multiplier lemma and the stated exclusion.

**Dated comparison through November 21, 2026.** Bożek's Theorem 3.7 gives the earlier two-label theorem used exactly above, not the moving three-multiplier lemma or the seven-label lower bound. [Kelanemer's September 6 revision](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) concerns neighboring factor-island exponent matrices; the full text could not be accessed at its landing and delivery endpoints, so no priority or comprehensive nonoverlap claim is made. In particular no proof of Goldbach, even on the entire fixed-smooth family, follows from a lower bound on orbit size.
