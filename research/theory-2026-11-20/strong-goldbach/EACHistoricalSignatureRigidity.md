# Exactly one center for each of the six historical weighted signatures

**Theorem.** For each of the six complete weighted component matrices reported by [Bożek, §§4–5, Table 1 and Figs. 2, 4–7](https://arxiv.org/pdf/1909.09900), allowing its distinct prime labels to vary, the only even center of an EAC with that matrix is its original center: respectively **128, 1718, 1862, 1928, 2200, 6142**. Equivalence of matrices here permits simultaneous row/column permutation; the exponents, and the association of each complementary row with its own prime vertex, must be unchanged. We are NOT fixing the prime values in advance. All six centers have Goldbach partitions, so **a Goldbach exception, if it exists, must have an EAC of a different weighted signature**. We do not classify all EACs, exclude another signature sharing the same unweighted graph, or prove Goldbach. The size-two case was already fully classified in Bożek’s Theorem 3.7, using Scott.

We use the historical examples to specify the matrices, not the completeness of a global census above a finite cutoff. Bożek’s §4 reports a computer-aided search covering even N≤10⁸, and §5.2 specifies source strongly connected components after excluding singletons and prime-sum pairs. Reversing his arrows gives our factor-closed SCCs, so his finite classification would suffice below 10⁸. In addition, our **independent signature-specific** enumeration below checks that range directly for the five mixed matrices. It does NOT independently rescan all possible graphs through 10⁸.

### Certified exclusion above the small search range

Retain the exact integer P, dᵢ=D(A⁻¹1)ᵢ, s=N^(−1/D), H, and first coefficient c s^ℓ from [the series theorem and polynomial table](EACPositiveBranchJets.md). Write B=A⁻¹, Δᵢ=D−dᵢ and uᵢ=log(s^{dᵢ}xᵢ). We give sharper exact bounds on the SAME branch, valid everywhere on 0<s≤s₀. All terminating decimals below are exact rationals.

| Signature | s₀ | complex radius R | Taylor order of s^H P | enclosure for P/s^ℓ | necessary N smaller than |
|:---|---:|---:|---:|:---|---:|
|128|.22|.35|52|(−2,−1/2)|77,790,727|
|1718|.27|.296|169|(4,6)|91,391,815|
|1862|.047|.075|47|(2,3)|92,771,132|
|1928|.13|.16|124|(3,5)|94,299,596|
|6142|.715|.82|234|(1/8,3)|73,701,062|

1. **Complex branch.** Use the norm maxᵢ |uᵢ|/rᵢ on the polydisc of radii rᵢ, all 1 except in the 1928 case. For that case, in increasing historical-prime order take r=(27,8,24,11,72,43,18,79,15,24,43,8,28,27)/100. Set zⱼ=R^{Δⱼ}(1−rⱼ/32)^{−32}; the rational bound e^v≤(1−v/32)^{−32} for 0≤v<32 follows by taking logs. The checker verifies max zⱼ<1 and, for each i, both ∑|Bᵢⱼ|zⱼ/(1−zⱼ)<rᵢ and ∑|Bᵢⱼ|zⱼrⱼ/(1−zⱼ)<rᵢ. Power series for log(1−z) and its derivative show respectively that the fixed-point map (1) of the linked theorem maps the closed box strictly into itself and is a strict contraction in that weighted norm. This gives the small complex branch on |s|≤R.

2. **Every actual solution is in that box.** From uᵢ=∑Bᵢⱼ log(1−xⱼ/N), 0<xⱼ/N≤1/3, start with e^{uᵢ}≤vᵢ=(3/2)^{⌈∑ⱼ max(−Bᵢⱼ,0)⌉}. At 0<s≤s₀ take zⱼ=min(1/3,s₀^{Δⱼ}vⱼ). Then |uᵢ|≤gᵢ=∑|Bᵢⱼ|zⱼ/(1−zⱼ). If needed tighten vᵢ to the smaller of its previous value and an outward rational rounding of (1−gᵢ/32)^{−32} (with gᵢ<32 checked). Exact arithmetic verifies gᵢ≤rᵢ on the first pass for four signatures and on the second for 1928. Thus the contraction applies to the actual tuple, not just a candidate local germ.

3. **Series and uniform interval proof.** Compute the coefficients of F=s^H P through the displayed order J by exact rational recurrence, and cross-check each of the original multiplicative equations by literal truncated polynomial products to order J. The leading index is h₀=H+ℓ. The polynomial of degree J−h₀ in s obtained from these coefficients represents F/s^{h₀} with tail bounded, on the WHOLE interval, by
     
       K R^{−h₀}(s₀/R)^{J−h₀+1}/(1−s₀/R),   K=∑|c_ν|3^{|ν|₁} .

   Indeed F is bounded by K on the complex disk since rᵢ≤1; apply Cauchy's coefficient bound. The checker encloses the polynomial on each of 256 closed intervals [s₀i/256,s₀(i+1)/256] by interval Horner evaluation. Every coefficient, endpoint and intermediate product is rounded **outward** on the grid 2^{−100}ℤ; the exact rational tail is added on both sides at the end. This is not sampling points. The five resulting rational enclosures lie strictly within the stated open intervals. They exclude zero, and their maximum absolute endpoints times s₀^ℓ are strictly less than 1. Therefore P would be a nonzero integer of absolute value <1 for every actual tuple with 0<s≤s₀. Hence N<s₀^{−D}; the last column uses the ceilings of these rational numbers and is strictly below 10⁸ in all cases.

### Independent finite check for each signature

For N≤10⁸ and a fixed row naming, each label satisfies xᵢ≤(10⁸)^{wᵢ}(3/2)^{∑ⱼ max(−Bᵢⱼ,0)}. The finite checker takes the ceiling of this bound by binary search on the powers-of-integers inequality (denominators cleared). Take a seed input and list every prime assignment to it and all its distinct output labels. All must be odd and distinct. The resulting N=xᵢ+∏xⱼ^{Aᵢⱼ} is then **determined**, not independently guessed. The following ledger uses increasing historical output labels.

| Signature | historical seed | ceilings on prime values, seed first | distinct seed tuples in range | pass known multiplicities | pass reachable set |
|:---|---:|:---|---:|---:|---:|
|128|3|111, 465|2,464|209|1|
|1718|3|15, 27, 235|1,466|267|1|
|1862|3|30, 532, 532|81,963|13,055|1|
|1928|3|23, 76, 103, 609|364,064|297|1|
|6142|17|1,369, 35, 69|35,856|27|1|

For every assigned pair of input and output labels, test its exact required valuation, including zero, in the complementary row. For a surviving assignment, follow ALL prime factors recursively from its seed row label. In an actual strongly connected factor-closed component, this reachable set is exactly its own vertex set. Thus we can reject a prime complement, a vertex dividing N, a reachable set of the wrong size, or a set missing an assigned vertex. These are only necessary filters but each final pass occurs at its stated original center; the original checker verifies the complete input matrix and actual EAC there. This proves exhaustiveness for the signatures up to permutation, not a claim that arbitrary matrices pass precisely these tests. Square-root trial division suffices: every reachable positive complement is at most 10⁸ and the checker sieves all primes through 10⁴ for exact factorization. Each of the five centers occurs in its row of the table, and no others occur. Together with the analytic exclusions and Bożek's already known two-label theorem this proves the claim.

**Reproduction** (three Python files in the same directory; only the standard library):
    
    python3 -O check_eac_historical_range.py
    python3 -O check_eac_historical_small.py

Both import the previously published `check_eac_historical_jets.py`, which rebuilds the six matrices from the prime-factor graphs and supplies the polynomial table. Its historical graph test agrees with Bożek’s Definition 2.1 and §5.2: all primes from 2 through N−2, maximal valuations as arc weights, reversed orientation, then closed SCC, at least two vertices, no prime-sum pair. The six vertex counts 8,28,21,14,2,10 are all distinct and match Table 1. The other two scripts independently bound large N and check finite seed assignments; neither reads a saved solver result or requires external data.

The earlier [positive-branch note](EACPositiveBranchJets.md) gives the exhibited prime pairs for all six centers. The [related 2026 graph record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats components under global counterexample hypotheses; the full latest text could not be inspected in this check. The assertion here is only the exact recurrence classification of the six listed original matrices, with the finite part reproduced by the two scripts. It does not use an assertion of all-height graph classification from either source.
