# Full F-rich threshold for the six-label bounded-arity obstruction

Fix an odd prime p, a finite set F of primes, an integer D≥2 and ε>0. Let N_F be the full F-part of an even integer N coprime to p. For **all sufficiently large** N with

    N_F ≥ N^(1/2+ε),

if the forward factor orbit from p consists entirely of rows with N−x composite, then it has **at least seven prime labels or at least one row has Ω(N−x)>D**. Equivalently, the largest number of prime factors with multiplicity on six-label all-composite orbits must tend to infinity on any such sequence. No effective rate or unbounded-arity six-orbit exclusion is proved. At a hypothetical Goldbach failure, coprimality and compositeness hold throughout this closure, but no upper bound on its size or arity is supplied, and no Goldbach representation is implied.

This extends the earlier [three-quarters theorem](../PrimeOrbitSixCurveThreeQuarters.md) to the full F-rich hypothesis of [moving-seed independence](../PrimeOrbitMovingSeed.md). The new step bounds the **projected** arity uniformly without bounding p-powers in the finite computation, by comparing Taylor coefficients on both sides of the exponent matrix. The original D is still essential to get one fixed algebraic curve.

## Inputs and notation

Suppose a countersequence exists, with D fixed. Fewer than six labels are already impossible. We use the proven reductions in [the curve theorem](../PrimeOrbitSixCurveThreeQuarters.md), **§§1–4 and 6**, which require only the present 1/2+ε hypothesis:
* We may take a single strongly connected six-label exponent chart A, det A=0, rank A=5, and B=I−A of rank 4. All nonseeds grow beyond p; index input 0 by the fixed p and order the other five prime labels increasingly (allow equal limiting weights). A′, consisting of the five nonseed columns of A, has rank five.
* The physical subsequence is on a rational affine curve with one pole at infinity. In a rational polynomial parameter s the center N(s) has degree d; all five moving primes are nonconstant polynomials x_i(s) of degrees n_i with 0<n_i<d, in nondecreasing order. The primitive weights w_i=n_i/d solve A′w=1, and d is **exactly** their least common denominator (§6, by the meromorphic inverse at infinity). Distinct true primes have no nontrivial constant multiplicative relation.
* N(s) has a rational root α of multiplicity m>d/2; all x_i(α) are nonzero. For each pair of distinct moving labels n_i+n_j≥m. The classes e_0 and e_1 (seed and least moving prime q=x_1) are independent modulo row_Q B.
* Use also [the independent balanced √N theorem](../PrimeOrbitHalfAboveRoot.md) and its fixed-seed corollary: ≥4 of the six labels, including p, are at most √N at large F-rich terminal centers. Thus n_3≤d/2. Only the weaker n_2≤d/2 is needed for the prior curve argument. Here n_3≤d/2 is a genuine input to the new uniform bound and the enumeration.

Let B′ be the five nonseed columns of B, explicitly B′_ij=δ_ij−A′_ij for input i=0,…,5, output j=1,…,5. The p-column of B cannot be independent of B′, since that would give a row combination supported just on p. Thus B′ has rank four, its column space is col B, and ker B′ has a unique direction v′ over Q. Extend it by v_0=0; then Bv=0. We have v_1≠0, by independence of e_0,e_1: if the only kernel vector with v_0=0 also had v_1=0, those two linear functionals would be dependent on ker B. Normalize v_1=1 when convenient. For each i there is a rational coefficient b_i such that e_i−v_i e_1−b_i e_0 lies in the row space. Indeed the quotient is two-dimensional and e_0,e_1 form a basis; evaluation against v reads off the stated coefficient.

## Crossed Taylor constraints at α

Put Z=q(s)/q(α)−1 and e=ord_α Z≤n_1. Using x_i/∏ x_j^{A_ij}=−(1−N/x_i)^{-1}, the logarithmic derivative vector g_i=x_i′/x_i obeys Bg=O((s−α)^(m−1)), with g_0=0. The preceding row relation gives g_i=v_i g_1+O((s−α)^(m−1)). Integrate with the constant terms fixed to get
     
    x_i(s)/x_i(α) ≡ (1+Z)^{v_i}  mod (s−α)^m.                 (1)

This identity uses v_1=1. In particular, among all labels of degree <m (including p of degree zero) the v_i are distinct: equal exponents would give identical normalized polynomials of degree <m, contrary to distinct growing primes, or to growth versus the fixed seed. The four labels of degree ≤d/2 therefore provide at least four distinct v_i.

Now use any integral *left* kernel vector c of B. Exactly
     
    ∏ (1−N/x_i)^{c_i}= (−1)^{Σ c_i}=1,
     
the sign being fixed by evaluation at α. Negative powers are harmless locally. Taking formal logarithms at α and dividing the resulting series by N yields Σ c_i/x_i(s)=O((s−α)^m). With h_i=1/x_i(α)≠0 and (1), this says Σ c_i h_i(1+Z)^(−v_i) vanishes modulo (s−α)^m. A polynomial/series in Z with a first nonzero coefficient at degree j has order exactly je in s−α. Consequently for every integer j≥0 with je<m,

    (h_i v_i^j)_i ∈ col B′.                                    (2)

Indeed first extract binomial coefficients of (1+Z)^(−v_i) in increasing degrees; the j-th coefficient is a polynomial of degree j in v_i with nonzero leading coefficient, allowing triangular passage to powers. Rational left kernel vectors follow by clearing denominators. Rescaling all v_i by one nonzero rational factor preserves (2).

**Uniform bound m≤4e.** Otherwise the five vectors of (2) for j=0,…,4 lie in a space of dimension four. By the usual Vandermonde rank and h_i≠0 there are at most four distinct v_i, hence exactly four. Interpolation on these four values shows for every singleton index (its v_i distinct from all others) that c_i=0 for every left kernel vector. Four groups among six indices give at least two singletons. Delete two of them. The resulting 4×4 nonnegative zero-diagonal principal submatrix T retains a two-dimensional space of left eigenvectors at 1, **each nonzero member mixed-sign**: it is the restriction of a vector zero at the deleted positions, and all nonzero full left eigenvectors at 1 are perpendicular to a strictly positive right Perron vector of A of eigenvalue ρ≥2. If the spectral radius r of T exceeds one, 1,1,r occur among its eigenvalues and the trace forces −r−2, impossible. If r=1, a nonnegative left Perron vector is independent of this two-dimensional mixed-sign space, giving 1,1,1,−3, also impossible. The eigenvalue 1 precludes r<1. This proves the bound, in particular w_1≥m/(4d)>1/8. It is a bound after passing to the fixed-chart polynomial model, not an all-orbit assertion that every nonseed exceeds N^(1/8).

## Exact finite model: nothing about the p-exponents needs to be guessed

Write a=w_1. Every row of A′ is a vector r≥0 with r·w=1. Different rows cannot be equal: their actual complements would differ by a factor p^z, whereas their ratio lies in [2/3,3/2] and the inputs differ. Thus all six must be distinct. We have a>1/8, w_2>1/4, w_1+w_2>1/2, and every other weight is >1/2−a. A row has 2–7 moving factors counting repetitions. Its possible multiset, distinguishing the least moving q and four other moving labels Y,Z,W (not necessarily mutually distinct), is one of **62 templates**:
     
* q^k with 2≤k≤7 (6);
* q^k Y with 1≤k≤4 (16), since (k−1)a<1/2;
* YZ or qYZ (20), since both weights exceed 1/2−a;
* YZW (20). Four non-q factors are impossible since each weight exceeds 1/4. Nor can q accompany three others: if a≤1/4 their weights together with a total strictly more than 3(1/2−a)+a≥1, and if a>1/4 all four weights exceed 1/4.
     
The true five weights solve five linearly independent equations r·w=1 from this template list because rank A′=5. Enumerate all five-row bases, retaining primitive degree vectors (n_1,…,n_5;d) with the ordering, 8n_1>d, n_5<d, 2(n_1+n_2)>d, 2n_3≤d, and at least six different templates of weight one. This gives **348** profiles, largest d=48. This is a superset; it does not assume positivity or primality of any numerical realization beyond the necessary restrictions already proved.

For each profile, choose six distinct projected row vectors r_i of the stated weight in input order. Reject a nonseed self factor. For each moving target j keep at most one distinct input i<j which uses it (a smaller input must equal the least positive residue N mod x_j). Require every moving label reachable from input 0 by projected edges: in the full strongly connected graph, take a path from p, using the part after its last visit to p. The gcd of the seed-row entries is 1: at the rational root −p=∏ x_j(α)^{A′_0j}, since the seed has no self factor; take the rational p-adic valuation to see that this gcd divides 1. At this root there must also exist real signs σ_0=1, σ_j∈{−1,1} with σ_i=−∏_{j>0}σ_j^{A′_ij}. The p-powers do not change these signs.

Require rank A′=5, rank B′=4 with its right null direction satisfying v_1≠0; among the degree <m₀ indices, where m₀=floor(d/2)+1≤m and deg p=0, require distinct v-values by (1). Both signs of v must each have at least two entries. Indeed Af=f for f=v, it must change sign by Perron orthogonality, and every positive (respectively negative) coordinate has such a successor, forming a directed cycle of at least two because there are no self loops. These are all necessary; no sufficiency or hidden bound on the omitted p-column is used.

The exact ledger proceeds as follows:

| Ordered, distinct, no-loop, smaller-parent assignments | p reaches all | after seed-row gcd and both rank/null-direction tests | after distinct local directions, both sign tests |
|---:|---:|---:|---:|
| 1,242,550 | 1,016,924 | 166 | 32 |

The last 32 raw tuples have profiles (1,1,1,1,1;3) [2], (1,1,1,1,2;3) [28], (1,2,2,3,3;5) [1], (1,2,2,3,4;5) [1]. Each entry is a moving degree; all raw row indices and each final equation are given in [the raw list](charts.txt) and [the exact terminal ledger](terminal_certificates.txt).

## Final rejections

On both quintics deg q=1, so e=1 and m≥3. Take an integer/rational two-row basis L for the left nullspace of B′ and Δ=diag(v_i), with v any nonzero integral scaling. By (2), stacking L, LΔ, LΔ² gives a six-by-six matrix that must kill the nonzero h. The following respective bases/diagonals give determinants −8088 and +2952:
     
    L₁ = [0 1 −1 −1 1 0; 1 −1 −1 0 0 1],   v=(0,−1,4,7,−5,2)
    L₂ = [0 1 −1 −1 1 0; 1  0 −1 −1 0 1],   v=(0,−1,4,7,−5,1).

On all 30 cubics deg q=1 and m≥2. Set X=(q/q(α)−1)/v_1 using the (not necessarily unit-normalized) integral direction v. By (1), every degree-one label is exactly x_i(α)(1+v_i X). The ratio of its constant to leading polynomial coefficient in X is b_i=1/v_i. For the possible single degree-two nonseed label allow its next-to-leading/leading coefficient ratio to be an unconstrained rational b. The fixed seed p supplies only a constant factor in the products. For every row with input degree <2 both leading coefficients (powers 3 and 2) of its product equal those of the center, since their difference is its input. All these rows therefore have the same next-to-leading/leading ratio C. For a product such ratios add with multiplicity:
     
    ∑_{j=1}^5 A′_ij b_j = C             (rows with input degree <2).    (3)
     
There is no rational solution to (3) for any of the 30 tuples. The terminal ledger gives every augmented matrix with its two formal variables b,C and right side; when there is no quadratic label the b-column is zero. In each case rank of the augmented matrix is greater than coefficient rank. This eliminates the last charts and proves the theorem.

## Reproducibility

From this directory run `sh replay.sh` with C++17 and Python 3 standard library. The two weight searches use distinct row generators: [ascending exact Bareiss](weights_forward.cpp) solves five linear equations directly; the [reverse search](weights_reverse.cpp) takes four homogeneous differences from a reference row and obtains their kernel vector by exterior products. Both regenerate [the identical 348 primitive profiles](weights.txt).

The [forward chart search](charts_forward.cpp) selects rows ascending, tabulates necessary tests and uses literal integer signed minors; it discards rank-five B′ early only when a nonzero minor is already detected modulo 101. The independent [reverse chart search and terminal verifier](charts_reverse.py) regenerates all row multisets directly, assigns inputs descending and prunes a prefix only when its B′ rows already have rank five modulo 101; it then uses exact rational Gaussian elimination for both true ranks and the terminal equations. A rank-five modular minor certifies a nonzero integer minor, and a modular rank defect is never used to infer a rational rank defect without checking exactly. The forward weight determinants have squared augmented row norm ≤50, so even products of two order-five minors with subtraction fit signed 64-bit comfortably; difference rows in the reverse weight search have Euclidean norm ≤14, giving order-four determinants <40000 by Hadamard. Chart integer permutation expansions have crude upper bound 5!·7^5<2.1×10^6 (and <5!·7^5 for B′ as well since the diagonal is 1). Residual calculations in Python are exact and fail closed, including under `-O`.

Each profile line is the five ordered degrees followed by d. A raw tuple starts with the profile number (1-based in the lexicographically sorted file), followed by six zero-based row IDs indexing all degree-one-weight exponent vectors for that profile in lexicographic order, inputs p,q,then the remaining four increasing primes. The shell compares both full independently reconstructed lists and all exact terminal records, not just totals. The complete forward stage-by-stage table is [here](forward_ledger.txt).

These calculations concern reflected-prime components as in [Bożek](https://arxiv.org/abs/1909.09900). They establish no full solution or priority claim with respect to other proposed Goldbach frameworks.
