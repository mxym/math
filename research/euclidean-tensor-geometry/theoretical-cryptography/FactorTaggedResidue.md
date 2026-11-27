# A sharp residue-state tradeoff for verifying a supplied balanced factor pair

A factor certificate gives two alleged prime factors. Checking their product is an equality problem, not finding a factor. Random modular fingerprints for checking multiplication are classical. This note identifies a sharp minimax soundness curve for one particular verifier family, even when it can choose arbitrary composite modulus tags, using distributions depending on the alleged pair.

## Model

Let X_n be the set of products of two distinct n-bit primes. The prover supplies such a pair, claiming its product x is the actual input y; both x and y belong to X_n. The verifier privately selects one modulus m≥2 from a fixed public finite family M, using any distribution w_x that may depend on the whole alleged pair. It retains the tag m and the residue x mod m. The receiving phase accepts exactly if y mod m agrees with the retained residue. Truthful pairs always pass. The adversarial false-acceptance probability is
```
max_(x,y in X_n, x≠y) Σ_(m in M, m | x−y) w_x(m).
```
The tag is chosen by the verifier, not supplied by the prover. The family must be fixed independently of which pair is submitted; the weights may vary with x. Restricting to an ordered representation of each pair is harmless; the lower bound also holds if multiple encodings are allowed, by analyzing one per x.

The budget is the number D of full **tagged residue slots**: Σ_(m in M) m≤D. For this family there are m reserved slots for the possible residues of each tag, so a fixed-length representation needs at most ceil(log_2 D) bits. The budget is not a lower bound on the number of actually reachable states for an arbitrary implementation, nor a constraint on local computation or witness length. In particular, a representation that omits unreachable residues, untagged messages, a protocol that tests more than one residue, and another acceptance rule are all different models.

Write E_n(D) for the infimum worst false-acceptance probability within this family. Here and below ln is natural logarithm.

## Sharp critical window

If D∼a n²/ln n for a fixed 0<a<∞, then
```
lim E_n(D) = min(1, sqrt(2) ln(2) / sqrt(a)).
```
In particular, for any fixed 0<ε<1, the asymptotic full tagged-slot budget to reach soundness at most ε is
```
D_ε(n) ∼ [2(ln 2)² / ε²] n²/ln n.
```
If a<2(ln 2)² the worst false-acceptance probability is actually one for all sufficiently large n. Composite modulus tags and alleged-product-dependent probability weights do not improve the critical-window limit over uniform prime tags. For any fixed κ>0, a coarser extension uniformly for 2≤D≤n^(3−κ) is
```
E_n(D) = Θ(min(1, n/sqrt(D ln(D+1)))).
```
For prime-only families this order estimate holds with any fixed polynomial upper budget. Constants in the coarser estimates may depend on the polynomial range. The central theorem requires no equidistribution of semiprimes modulo a modulus.

## Counting lemma for input-dependent weights

Suppose a base modulus L covers some tags (each such tag divides L), and each remaining tag is assigned to a group j with auxiliary modulus a_j≥2 such that it divides lcm(L,a_j). Suppose Σ_j a_j≤D, and there are J nonempty groups. For each alleged product x, aggregate its probability by group and choose a set T_x of the k heaviest groups, with a fixed tie-breaker. The number of distinct tuples
```
(T_x, x mod L, (x mod a_j)_(j in T_x))
```
is at most L times e_k(a_1,…,a_J), where e_k is the sum of products over k-element subsets. The elementary inequality e_k(a)≤D^k/k! follows by expanding (Σ_j a_j)^k and retaining ordered products of distinct indices.

If |X_n| exceeds that tuple count, there are distinct x,y matching on every tag covered by L or by a chosen group in T_x. If the total mass of base-covered tags for x is w, the selected group mass is at least (k/J)(1−w). Consequently its false-acceptance probability is at least k/J. The lemma does not presume that y chose its tags independently of x, or that w_x depends on x in any controlled way. If no groups remain, |X_n|>L gives false-acceptance probability one by itself. The same reasoning with k=min(J,k_0) uses the bound L D^(k_0)/k_0! whenever k_0≤D, because D^j/j! is nondecreasing for integers 0≤j≤D.

## Grouping arbitrary composite tags

Let U be a positive integer. Put all tags m>U² into L, together with lcm(1,…,U). For the other tags every maximal prime-power component, except possibly one, is ≤U: two coprime components >U would already give m>U². A tag with no such large component divides L. Group each remaining tag by the prime of its unique large component. For group j let a_j be the largest such prime power occurring in that group. Its witness tag is different from the witness tags of other groups, so Σ_j a_j≤Σ_(m in M)m≤D. Every group-j tag divides lcm(L,a_j). In addition the a_j involve distinct primes, so Σ of the first J primes is at most D.

In the critical window take U=floor(n/(ln n)^(1/4)). For sufficiently large n all tags satisfy m≤D<U², and ln L=ψ(U)=O(U)=o(n), with ψ the Chebyshev function. The ordinary prime number theorem gives
```
|X_n| = binomial(π(2^n)−π(2^(n−1)),2),
ln |X_n| = (2 ln 2)n − O(ln n).
```
The endpoint distinction is immaterial for n≥3. By partial summation of the prime number theorem, the sum of the first J primes is asymptotic to (J² ln J)/2; equivalently the sum of primes up to R is asymptotic to R²/(2 ln R). Hence uniformly for any allowed family
```
J ≤ (sqrt(2a)+o(1)) n/ln n.
```
Fix any 0<β<2 ln 2 and take k_0=floor(β n/ln n). Stirling's formula gives ln(D^(k_0)/k_0!)=(β+o(1))n, less than ln |X_n|−ln L. The counting lemma with k=min(J,k_0) thus lower-bounds the worst error by min(1,k_0/J) (or one if no groups remain), for every weight assignment. Let β approach 2 ln 2. If sqrt(2a)<2 ln 2, choose β strictly between those values; all groups are selected and the error is one, with strict cardinality inequality for all large n.

For a general upper budget n^(3−κ), one can replace κ by min(κ,1) and take U=floor(n^(1−κ/4)). The O(D/U²) tags above U² contribute at most O((D/U²) ln(D+1))=o(n) to ln L; the small-prime-power part of L also contributes o(n). Thus the same finite argument works with k_0 of order n/ln(D+1), with a sufficiently small absolute coefficient. If D≤k_0, simply use every group and bound the tuple count by L D^J/J! with J≤D≤k_0; the same logarithm bound applies. The sum of the first J primes still bounds J by O(sqrt(D/ln(D+1))). This proves the coarser lower bound. For prime-only tags one may dispense with the base and directly take a_j=m_j, so the same lower proof works for any fixed polynomial upper bound on D.

For arbitrary composite tags at larger polynomial budgets, a weaker lower bound still follows. Put every tag at most floor(n/8) in the base, and let each larger tag be its own group. Then ln L≤(1/8+o(1))n and J=O(D/n). The same tuple count with k_0 of order n/ln(D+1) gives E_n(D)=Ω(min(1,n²/(D ln(D+1)))) throughout any fixed polynomial range. This estimate does not settle the exact decay for arbitrary composite tags once the sharper grouping no longer applies.

## Matching prime upper bound

Use every prime m≤R with equal weight, for R slightly smaller than sqrt(2a)n so the sum of the moduli fits the critical budget. For distinct x,y in X_n the nonzero discrepancy |x−y| is less than 2^(2n). If it is divisible by k distinct moduli, it is at least the product of the first k primes, whose logarithm is asymptotic to k ln k by the prime number theorem. Thus k≤(2 ln 2+o(1))n/ln n. Also π(R)∼R/ln R. The false-acceptance probability is bounded by min(1,k/π(R)); letting the constant shortfall of R below sqrt(2a)n approach zero proves the critical matching upper bound. Inverting the monotone error curve with arbitrary constants on either side of the critical value for ε gives the stated budget asymptotic.

For the coarser estimate take R of order sqrt(D ln(D+1)) with a sufficiently small constant and use primes in [R/2,R]. Their sum is O(R²/ln R) and their count is Θ(R/ln R). Each selected prime divisor of the discrepancy costs at least ln(R/2) of its logarithm, so the uniform error is O(n/R), capped at one. For bounded D the coarser estimate is already trivial on the upper side. This construction uses no witness-dependent weighting.

## What this does and does not establish

* If x and y were arbitrary integers of bounded height, the simple source of collisions would be arbitrary bounded discrepancies. Here the lower argument instead finds a collision among **actual distinct balanced semiprimes** by counting even after adaptive-to-x tag weights. It does not find their factors or give a factorization method.
* For a fixed tagged family, if its least common multiple is less than |X_n|, some distinct balanced semiprimes collide for every tag, irrespective of weights. The classical [Landau function](https://www.numdam.org/item/JTNB_2008__20_3_625_0/) bounds this least common multiple by g(D), with ln g(D)∼sqrt(D ln D). This already accounts for the budget below which unit error is forced. The critical-window profile above also gives the error curve *beyond* that basic aliasing threshold.
* [Ablayev–Karpinski, Theorem 1](https://eccc.weizmann.ac.il/eccc-reports/1998/TR98-011/) already uses modular fingerprinting to verify supplied multiplication in small randomized ordered branching programs. The fingerprint upper construction is not new. The contribution here is the matching minimax lower bound under a full tagged-slot budget, with composite tags and witness-dependent selection allowed. Ordinary prime count estimates are classical; see [Rosser–Schoenfeld](https://projecteuclid.org/download/pdf_1/euclid.ijm/1255631807).
* With unrestricted private one-way messages and unlimited local computation this verification problem is exactly Equality on the finite label set X_n. At constant bounded error its communication is log_2 n+O(1) bits by classical Equality bounds (with perfect completeness, the lower bound already follows because the supported state sets of the different x must all be distinct), whereas the stated tagged family needs 2 log_2 n−log_2 ln n+O(1) bits to encode its full state table. See [Lalonde–Mande–de Wolf](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2023.32) and [Alon's rank bound](https://doi.org/10.1017/S0963548307008917) for the general problem. This is a restricted-family separation in communication/storage, not a claim that every efficient actual streaming verifier reaches the general communication upper bound.
* The two supplied factors are a certificate, unlike the search tasks in [the factor-output paper](FactorStreamingBlocks.md). The promised primality can be certified separately if it is not given; [Pratt](https://doi.org/10.1137/0204018) is classical context. There is no lower bound here on certificate length, no lower bound on general factoring time, and no hardness claim for verifying a *single* alleged factor without a cofactor.

[Exact toy checks](verify-factor-tagged-residue.js) audit the grouping, symmetric-product bound, and collisions within actual generated small semiprime pools under input-dependent tag weights. The replay covers 420 toy modulus families, 3,500 covering checks, and 177 input-dependent weighting tables with certified collisions. They do not factor any supplied input.
