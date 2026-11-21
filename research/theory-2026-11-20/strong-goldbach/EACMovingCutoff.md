# A cubic-log escape bound for closed reflected prime factors

Let N be a sufficiently large even integer and let C be a finite set of k≥2 distinct primes, all coprime to N and ≤N−2. Suppose every prime factor of N−p lies in C for every p∈C. Write M=max C, L=log N. There are absolute positive constants such that
$$
 M\gg \frac{L^3}{(\log L)^{10}}.                                      \tag{1}
$$
In the nontrivial range M≤N/2 there is also a size constraint
$$
 k\gg \frac{L^2}{(\log M)^6(\log L)^2}                                \tag{2}
$$
whenever M≤√N, and (2) is vacuous up to choice of absolute constant for √N<M≤N. The estimates are asymptotic, not new numerical cutoffs at the finite verification boundary. Their constants can in principle be made effective from the cited explicit prime and logarithm bounds; no numerical constant or threshold is computed here. Neither the minimality of a missing N nor strong connectivity is assumed.

In particular every exceptional autonomous component in the sense of [Bożek, Theorem 2.6](https://arxiv.org/abs/1909.09900v1) at a hypothetical binary Goldbach exception has a label at least as large as (1). Goldbach pairs need not be removed for (1). Singleton loops p with N=p+p^a are excluded by hypothesis and can make any universal growing label assertion false if allowed. This does not exclude large components or prove existence of a prime pair.

### 1. Mark one row per prime

Set U_i=N−p_i for C={p_1,…,p_k}. We can assume M≤√N; otherwise (1) holds and the right side of (2) tends to zero. For each q∈C mark one row attaining its largest q-adic valuation (arbitrary tie-breaking). If q never occurs its maximal exponent is zero; its dummy mark does not change a factor. Let v_i be the product of all prime powers of U_i **except** powers of primes whose mark is on row i. By closure these factors and the marked ones account for all of U_i. Write E=Σ_i log v_i. For each q and exponent a≥1, set
$$
 r(q,a)=\#\{i:q^a\mid U_i\}.
$$
Then exactly
$$
 E=\sum_{q\in C,a\ge1}(r(q,a)-1)_+\log q,\qquad
 \sum_{q\in C,a\ge1}{r(q,a)\choose2}\log q
 \le\sum_{i<j}\log |p_j-p_i| \le {k\choose2}\log M.                 \tag{3}
$$
At an occupied level one row bears the mark. A pair counted at that level satisfies q^a|(p_i−p_j); summation over all q,a is bounded by the log of the nonzero integer difference. Every shared power q^a with r(q,a)≥2 is <M. Consequently for any T⊂C,
$$
 \sum_{q\in T,\ a:r(q,a)\ge2}\log q\le |T|\log M .
$$
Weighted Cauchy–Schwarz, using (r−1)^2≤2 binom(r,2) for r≥2, gives
$$
 E(T)/k\le\sqrt{|T|}\log M ,                                         \tag{4}
$$
where E(T) is the contribution of q∈T to the first sum in (3). In particular E/k≤√k log M.

### 2. A split at an intermediate prime size

For large M put Q=(M²/log M)^(1/3). Then √M<Q<M/2 and log Q, log(M/Q) are each comparable to log M. By the elementary upper bound π(Q)≪Q/log Q, (4) gives
$$
 E(q\le Q)/k\ll\sqrt{Q\log M}.
$$
For q>Q only its first power may be shared. If q>M/2, two eligible odd labels would have difference divisible by 2q and hence exceeding M, so there is no sharing. For Q<q≤M/2, count primes p≤M in the single reduced residue class N mod q. The [Montgomery–Vaughan Brun–Titchmarsh bound](https://doi.org/10.1112/S0025579300004708) gives at most 2M/((q−1)log(M/q)). On 2≤z≤M/Q the function z/log z is bounded by a constant times (M/Q)/log(M/Q) (it increases after e, and the interval [2,e] is harmless). Thus r(q,1)≪(M/Q)/log(M/Q), and since there are at most k choices for q,
$$
 E(q>Q)/k\ll (M/Q)\log M/\log(M/Q)\ll M/Q .
$$
Combining bounds and enlarging an absolute constant for bounded M yields
$$
 E/k\ll (M\log M)^{1/3}.                                              \tag{5}
$$
This argument counts actual prime input rows for Brun–Titchmarsh; no distribution assumption on C is needed. With mere spacing instead of Brun–Titchmarsh one already gets a cubic-log bound with a worse logarithmic denominator.

### 3. Two rows with controlled residuals

Put e=E/k and l=log(N−M), so l≥L−log 2. A row without a mark has residual of log U_i≥l. The number of unmarked rows is at most E/l; the number of rows with at least two marks is no greater than the number of unmarked rows, since there are k marks in k rows. If e≥l/8, (6) below is immediate. Otherwise fewer than k/4 rows have a number of marks different from one. If E>0, fewer than k/4 rows have log v_i>4e (at most k/4 suffices), and if E=0 none do. Therefore strictly more than k/2 rows have one mark and residual log≤4e, so at least two such rows exist even for k=2 or 3. On a selected row a zero-valued sole mark is impossible because 4e<l. Select two distinct indices i,j. Their marks belong to distinct primes q_i,q_j, and their exponents a_i,a_j satisfy 1≤a_i,a_j≤L/log 2. Then
$$
 0<\left|q_i^{a_i}q_j^{-a_j}(v_i/v_j)-1\right|
 =|U_i/U_j-1|\le M/(N-M).
$$
The strict nonzero follows from the distinct row labels, not from algebraic independence of the three bases. Apply [Matveev, *Izvestiya: Mathematics* 64 (2000), 1217–1269](https://doi.org/10.1070/IM2000v064n06ABEH000314), in its positive rational, at-most-three-logarithm form. For fixed t≤3 it gives −log|∏α_h^{b_h}−1|≪(1+log B)∏ max(1,h(α_h)) for a product different from 1, rational positive bases, B≥max(2,|b_h|); the rational log-height is log max(numerator,denominator) in lowest terms. Drop the third base if v_i/v_j=1. Otherwise its height is ≤max(log v_i,log v_j)≤4e, and each first-base height is ≤log M. Hence
$$
 \log((N-M)/M)\ll (1+e)(\log M)^2\log L .
$$
For M≤√N the left hand side is ≫L, for sufficiently large N. This proves in both mark-count cases
$$
 L\ll(1+E/k)(\log M)^2\log L.                                        \tag{6}
$$
Using E/k≤√k log M from (4) now gives (2). Using (5) in (6) gives
$$
 L^3\ll M(\log M)^7(\log L)^3.
$$
If M≥L³ then (1) is automatic. Otherwise log M≤3 log L and (1) follows. This proof needs no hypothesis on the rank of an exponent matrix, no polynomial Vandermonde limit and no short-interval smooth-number estimate.

### Scope and neighboring prior results

Ramachandra–Shorey–Tijdeman's work on Grimm's problem gives distinct prime representatives in short consecutive integer blocks; that statement alone allows a closed alphabet to saturate its own size. [Shorey, Acta Arith. 30 (1976), Thm. 2, p. 28](https://matwbn.icm.edu.pl/ksiazki/aa/aa30/aa3014.pdf) bounds smooth integers in an interval when its base exceeds exp(length^ε), but is not needed in this proof. [Bożek](https://arxiv.org/abs/1909.09900v1) supplies the factorization graph and the true exception⇒special component implication. These genuine-prime conditions do not promise any universal upper bound for M comparable to (1); the ordinary elementary upper bound M≤(N−3)/3 in the exceptional case is far larger. No global Goldbach exclusion or exhaustive priority claim.

The optional integer checker `check_eac_marking.py` verifies the exact identities behind (3), the weighted Cauchy bound via integer counts per shared level, and selection of two single-mark rows by rational-product comparisons on small true/synthetic samples, not the imported asymptotic Diophantine estimate.

This complements the [all-height finite-alphabet classification](EACCompactSmooth.md) and is a different type of estimate from the exceptional-set bounds of [Althöfer–Chen–Perelli–Pintz (2026)](https://arxiv.org/abs/2611.09386v1). The bound constrains the size of the prime labels at each hypothetical exceptional center, not how many exceptional centers there are.
