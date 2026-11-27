# Sharp support–energy law for scalar integer relations in random finite modules

Let q be an odd prime, B independent uniform rows M_i in a finite F_q-vector space of dimension D, and consider nonzero integer coefficients c=(c_i) satisfying Σ c_i M_i=0. One instance is M_i uniform in S_q^t for S_q=F_q[Y]/(Y^d+1), with D=dt. Its CRT components may have any factorization: a nonzero scalar of F_q represents a unit in every component, so the proof also works directly componentwise. Independent uniform rows on the entire space are assumed, not e.g. on differing proper subspaces. The coefficients here are scalar integers, not arbitrary ring-valued coefficients. The term energy means e(c)=Σ c_i². No finding algorithm or general hardness assertion is made.

## Exact finite existence law

Fix an integer 1≤E<q, a support cap w≥1, and let N(B,w,E) be the number of primitive Z-vectors modulo overall sign, with support ≤w and energy ≤E. Here primitive means the coordinate gcd is 1. Any feasible nonprimitive vector of energy ≤E can be divided by its gcd to produce a feasible primitive vector, since that gcd is nonzero mod q. Any nonzero candidate has a nonzero residue coordinate. The map from primitive sign classes to F_q projective lines is injective: if two reduced vectors are proportional, all integral 2×2 minors are divisible by q. Each such determinant has magnitude at most E by Hadamard on the two coordinate subvectors (both lengths ≤sqrt E). Thus all minors vanish over Z as E<q. Rational proportionality plus primitivity forces equality up to sign.

For λ=N(B,w,E) q^(−D),
    λ/(λ+1−q^(−D)) ≤ Pr(existence) ≤ min(1,λ).
Indeed each candidate sign class succeeds with probability p=q^(−D), and for distinct classes the reductions are independent over F_q. A rank-2 map of rows per field coordinate gives pairwise independent events. Equivalently a 2×2 invertible scalar minor solves for two freely uniform rows in any finite F_q-module, including every CRT-splitting type. Thus Var(Z)=λ(1−p) for the count Z; apply second moment and union bounds. For E not below q the injection argument does not apply; no extrapolation to composite q or ring-valued multipliers is made.

## Quantitative support and energy counts

For 2≤w≤min(E,B/2), logarithms are natural and
    log N(B,w,E) = log binom(B,w) + (w/2) log(E/w) + O(w)
with absolute implied constants. For the lower bound, on each support of size w take positive coordinates in [1,floor sqrt(E/w)]. Their energy is ≤E. At least 1/4 are primitive: the gcd can be >1 only if all coordinates are divisible by a common prime, and Σ_{k≥2} k^(−w) ≤ 3/4 for w≥2 (bound k=2 plus integral from 2). The floor loses at most a factor 2^w. For the upper bound, on a support of size j≤w count all lattice points in the energy ball by exponential tilting:
    # ≤ exp(aE) (Σ_{k∈Z} exp(−a k²))^j ≤ (C sqrt(E/j))^j,
using a=j/(2E) and the integral comparison. After multiplying by binom(B,j), use binom(B,j)≤binom(B,w) and j log(E/j)≤w log(E/w)+w/e. Summing over j has log loss O(w). If w=1 the count is exactly B, since primitive scalar entries are ±1; do not use the logarithmic formula there.

A more precise energy-only comparison for E≤B/2 uses N*=2^(E−1) binom(B,E), the exact number of distinct sign classes with exactly E entries all equal to ±1. Put x=E/(2(B−E+1)) and H(x)=Σ_{m≥2}x^(m²−1). Then
    N* ≤ N(B,E,E) ≤ N* (1+H(x))^E/(1−x).
Proof. Support j=E−k has sign-count ratio 2^(−k) binom(B,E−k)/binom(B,E)≤x^k. For a fixed support j, a magnitude m≥1 consumes excess energy m²−1 over unit amplitude, so the admissible magnitude tuples have total excess ≤k and are bounded by the sum of coefficients up to k of (1+H(z))^E (append E−j ones). Sum x^k times these coefficients, exchange sums, and use the geometric series. Counting all vectors, primitive or not, gives a valid upper bound. This also shows only a fraction O(E x³) can have any magnitude >1 whenever E x³=o(1): subtract the zero-excess tuple from each coefficient sum and use H(x)=O(x³).

For B=ceil(n^b), b>1, D/n→δ>0, and log q/log n→c>1, the minimum nonzero relation energy divided by n converges in probability to δ c/(b−1). Indeed at any fixed E=θn, counting only unit signs on E entries and the support-count bound above sandwich log N as (θ(b−1)+o(1)) n log n, while D log q=(δ c+o(1))n log n. Apply the finite existence theorem on both sides. The same leading threshold holds using +1-only vectors by the same first and second moments, so permitting arbitrary integer rather than binary coefficients gives no leading energy improvement in this regime. If b>4/3, the refined count ratio tends to one uniformly for E=Θ(n), from E x³=O(n^{4−3b}). In that case the actual minimum concentrates on two adjacent, deterministic integers. Define J as the least E in [1,floor(B/2)] with λ_E=2^(E−1)binom(B,E)q^(−D)≥ n^{−(b−1)/2}. By the leading count asymptotic J=Θ(n), and λ_{J−1}< n^{−(b−1)/2} while λ_{J+1}≥const·n^{(b−1)/2}, using the exact ratio λ_(E+1)/λ_E=2(B−E)/(E+1). Estimating all candidates at J−1 by the refined count and testing signed-unit candidates at J+1 proves Pr(minimum in {J,J+1})→1. No statement that their probabilities converge separately.

## Reproduction and context

[Exact toy checks](verify-finite-module-scalar-energy.js) enumerate primitive sign classes and all uniform row matrices for two small parameter sets. For random-kernel and SIS context see [Regev, §3](https://cims.nyu.edu/~regev/papers/pqc.pdf) and [Peikert's survey](https://eprint.iacr.org/2015/939.pdf). This note neither supplies an algorithm for finding a relation nor claims that projective pairwise independence is new.
