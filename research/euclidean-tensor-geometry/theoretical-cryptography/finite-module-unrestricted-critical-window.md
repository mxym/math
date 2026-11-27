# Unrestricted integer-ring critical window for sparse random module kernels

Let w→∞, let d be a power of two, q an odd prime, S=Z[Y]/(Y^d+1), and M_1,…,M_B be independent uniform in S_q^t. Put D=dt, and for c∈S^B use integer coefficient energy E(c)=Σ_i||c_i||². A feasible vector is a nonzero integral tuple with Σ c_i M_i=0 in S_q^t. Let µ={±Y^j:0≤j<d}; its action by common multiplication on integral nonzero tuples is free, and preserves energy and feasibility. Count µ-orbits. We study probabilities for this random finite algebra experiment, not finding witnesses.

Assume
    B/w²→∞, log B/log w→b<∞,
    log d/log w→a∈[0,1], log q/log w→c≥1/2, q²/w→∞,
    λ_w=binom(B,w)(2d)^{w−1} q^(−D)→λ∈(0,∞).
In particular b≥2. Then the number of feasible µ-orbits of energy at most w converges in total variation to Pois(λ), and with asymptotic probabilities 1−e^(−λ) and e^(−λ) respectively, the unrestricted minimum energy is w and w+1. No other energies have nonvanishing probability. This holds for any CRT splitting type. It is not asserted for c below 1/2 or the boundary q²/w bounded.

The critical mean condition and elementary binomial estimates imply
    D log q=(b+a−1+o(1))w log w, D/w→K=(b+a−1)/c.
Thus d=O(w) since t≥1. Such parameter sequences are not vacuous: take, for example, d fixed, q=w^{c+o(1)} with c>1/2, and t chosen with dt/w→K>1/c. Choose B as the first integer crossing the desired signed-monomial mean λ. The binomial count gives log B/log w→1+Kc>2, and adjacent-B ratios B/(B−w) tend to 1, so the mean converges to λ.

## Full-CRT-active exceptional vectors: unweighted count suffices

An integral vector of energy ≤w is called fully active if in every CRT field at least one of its entries is nonzero. Its feasibility probability is exactly p=q^(−D). The signed-monomial main shell has exactly w nonzero ring entries, each a signed monomial, and it contains N=binom(B,w)(2d)^{w−1} orbits. Every one is fully active.

Consider all nonzero integer tuples as length C=Bd integer arrays. A grouped support/energy count yields
    2^w binom(C,w) ≤ #arrays(E≤w) ≤ 2^w binom(C,w) (1+H(x))^w/(1−x),
    x=w/[2(C−w+1)], H(x)=Σ_{k≥2}x^{k²−1}.
Indeed moving from support w to w−j loses a binomial/sign factor at most x^j, and for each occupied position magnitude k consumes k²−1 units of excess energy. Extending to w positions and summing those distributions via geometric series proves the upper bound. Since B≫w², x→0 and wH(x)=O(w x³)=o(1). Among the 2^w binom(C,w) signed arrays with exactly w nonzero slots, a uniformly chosen set of w slots has a repeated ring row with probability at most binom(w,2)(d−1)/(Bd−1)=o(1). Thus the count of exceptional raw arrays (energy ≤w but outside the main shell) is o((2d)^w binom(B,w)). Dividing both counts by 2d for the free µ-action and multiplying by p gives an o(1) expected count of fully active exceptional feasible orbits. This step alone does not handle inactive tuples.

## CRT-inactive exceptional vectors: weighted first moment

If an entire CRT component vanishes, no nonzero ring entry can be a signed monomial, since these are units at every factor. Consequently s, the number of nonzero ring entries, is at most w/2 (each such entry has energy ≥2). For any tuple with s occupied rows, select a nonzero coefficient entry of energy at most w/s. The coefficient norm bounds the field norm of this entry by (w/s)^{d/2}, since the average squared canonical embedding value is its coefficient energy. If common dormant CRT factors have total degree g, their ideal norms multiply to q^g dividing that field norm. Thus the feasibility probability is at most
    q^(-D) (w/s)^{D/2}=exp[−(D/2)log(q² s/w)].
We bound the expected number of raw inactive vectors, stronger than the orbit count. For any s choose its row support in binom(B,s) ways, then bound the number of arrays in C_s=s d coefficient slots by
    A(C_s,w)≤2^{min(C_s,w)} binom(C_s+w,w).
This follows by summing 2^j binom(C_s,j) binom(w,j) over j: positive squared magnitudes are at most the count of positive integers of total ≤w, and Vandermonde sums the two binomials. Two useful estimates are log A≤w log(1+C_s/w)+O(w) and log A≤C_s log(1+w/C_s)+O(C_s), with absolute constants.

For s with log s/log w→β, 0<β<1, along any subsequence: the row choices cost o(w log w), and log A/(w log w)≤(β+a−1)_++o(1). After multiplying by the probability bound, the log exponent divided by w log w is at most
    (β+a−1)_+ − K[c−(1−β)/2] + o(1).
For fixed β>0 this is strictly negative. On β≤1−a this follows from c≥1/2. On β≥1−a it is affine; its value at β=1 is a−(b+a−1)=−(b−1)<0, and its value at the other endpoint is nonpositive, strictly negative unless β=0 and c=1/2. At β=1 use the constraint s≤w/2, which bounds log binom(B,s)/(w log w)≤(b−1)/2+o(1); the coefficient array exponent is at most a; the norm penalty beyond the main q^(−D) is o(w log w). Thus the full exponent is ≤−(b−1)/2+o(1). By subsequence compactness these estimates are uniform and exponentially small in w log w for s between w^ε and w/2, for any fixed ε>0.

For smaller s the c=1/2 endpoint requires a finer estimate. If a<1, choose fixed ε<min(1,1−a); for s≤w^ε, the number C_s of coefficient slots has a polynomial gap below w. The second estimate on A gives log A=o(w), and the row-selector log is also o(w). The factor exp[−(D/2)log(q² s/w)] is exp(−ω(w)) because D=Θ(w) and q²/w→∞. If a=1 and c=1/2, then d≤D=O(w) and the first estimate on A gives log A≤w log s+O(w); meanwhile D/(2w)→b≥2, so the negative probability exponent dominates both w log s and all O(w) terms, uniformly for s≤w^ε with ε<1. If a=1 and c>1/2 instead, β=0 in the preceding normalized exponent is already strictly negative, so the compactness argument covers all s. This proves the weighted first moment tends to zero after summing over ≤w/2 supports sizes. We did not assume CRT-inactive events have the usual p probability.

## Poisson and minimum

The signed-monomial shell has Poisson critical orbit count by the sparse factorial-moment theorem in [the sparse-shell note](finite-module-sparse-poisson.md): B/w→∞, log d=o(w log(B/w)), and λ_w→λ. By the two first moments above, with probability 1−o(1) there are no exceptional feasible orbits of energy ≤w, so the unrestricted count has the same Poisson limit. In particular there is no lower-energy feasible vector with high probability. Signed-monomial candidates at w+1 have mean λ_w·2d(B−w)/(w+1)→∞ and are pairwise independent by the exclusive-unit-pivot or unit-minor argument, so at least one exists with high probability. The minimum distribution follows. Below the modulus exponent threshold c<1/2, the unrestricted minimum is always at most q²=o(w) because q times any standard basis vector is a nonzero integral feasible tuple. This simple obstruction explains why the size of q² relative to the critical energy cannot just be ignored.

## Finite check and related primary sources

[The exact toy verifier](verify-finite-module-unrestricted-critical.js) enumerates all integer arrays over d=2, B=6, q=5 with energy ≤4 or ≤5, quotients by the four monomial units, classifies active CRT factors at roots ±2, and checks the norm penalty on each orbit. At cap 5 it finds 1,536 main shell orbits, 7,418 fully active exceptional orbits, and 12 CRT-inactive orbits (all missing one factor); the latter have total expected count 60/25 for t=1, five times their naive p-weight. Thus inactive weighting is necessary even before any finite-to-asymptotic argument. At cap 4 there are no inactive orbits. These are exact small abstract cases only, not tests of the asymptotic regime or samples from a deployment.

Gargava–Serban–Viazovska–Viglino, https://arxiv.org/abs/2510.12893 (§§3–4 and the introduction), study shortest vectors and torsion-orbit Poisson analogues for invariant random module lattices, noting connections via Construction A discretization. The present finite congruence kernel regime is ultra-sparse in an integer coefficient basis, with large ambient B, critical signed-monomial energy, and total-variation Poisson via a weighted exception first moment; it is not an inference from their invariant ensemble. Hao–Huang–Livshyts–Tikhomirov, https://arxiv.org/abs/1912.12833, treat conventional random-code minimal Hamming distance. The closely related factorial moment mechanism for the main shell is acknowledged in the companion proof. No general lattice-Poisson novelty or computational claim is made.
