# Four polynomial-size nonseeds must all have intermediate size and a growing power of the lone small nonseed

Fix a finite set F of primes and a fixed odd prime p. Take weight-convergent subsequences of even N→∞, (N,p)=1, log(N/N_F)=o(log N), on which a strongly connected, closed, all-composite six-prime factor orbit contains p and has exactly four positive limiting logarithmic weights w_i=lim log x_i/log N. Write q for its remaining subpower nonseed and L=log N. Then:

1. All four positive weights are strictly below one.
2. On such a subsequence, the q-part of at least one complement has polynomial size: liminf max_i v_q(N−x_i) log(q)/L>0.
3. Fix the six-by-four matrix R of multiplicities at the four macroscopic columns (automatically bounded on the subsequence), and let a,b denote the full seed and q exponent columns. Then R has rank four, 1 is not in its column space, and col A=col[R,1] has rank five for the full matrix A=[a,b,R]. Its left null line is fixed independently of the small-prime exponents. The largest physical moving label M has a second, comparably large label ≫_R M carrying a nonzero coefficient on that fixed line.

The first two results extend beyond the fixed-smooth case. These are necessary conditions; they do not rule out this four-intermediate regime or give a prime representation. A nonterminal six-label forward orbit has only three macroscopic labels by the [six-label fork](PrimeOrbitSixLabelFork.md), so does not create another four-positive-weight case. Throughout, “macroscopic” means a positive power in the logarithmic limit, not a positive fraction of N.

## Removing the fixed-smooth premise from the high branch

The [moving seed](PrimeOrbitMovingSeed.md) and [multiple-seed minimum](PrimeOrbitMultiSeedMinimal.md) results apply because N_F≥N^(1/2+ε) eventually. In particular q→∞, the full B=I−A has nullity two and the classes of the p and q coordinates modulo its rational row space are independent, so its four macroscopic columns have rank four. All needed rank and combinatorial hypotheses in the existing [four-macro proof](PrimeOrbitFourMacroExclusion.md) are available. We do **not** take the existence of a weight-one label from the earlier smooth theorem.

Suppose some weight is one. The proof excluding two or more such labels in [the four-macro reduction](PrimeOrbitSixFourMacro.md), from “Eliminate the high-only paths” onward, uses no prime-factor description of N. Specifically, four highs violate the finite first-return rank, three force a macroscopic label to divide a positive subpower integer, and two give the exact reciprocal multipliers 1+hp=q^a, 1+hq=p^b; [Bożek's two-label theorem](https://arxiv.org/abs/1909.09900) then contradicts q→∞. The sole remaining case, a unique weight-one high, obeys the [opposite half-weight proof](PrimeOrbitSixHalfWeights.md) in full: that proof uses return rank and divisibility, subpower cofactors, sizes and the unique smaller predecessor property, not smoothness. The three other weights therefore are 1/2,1/2,γ with 1/2≤γ<1.

Two arithmetic input conditions for the [four-macro chart certificate](PrimeOrbitFourMacroExclusion.md) need new checking:

* The p row contains a macroscopic factor. Otherwise N=q^e+p. As q grows but log q=o(L), we have e∼L/log q→∞. For each ℓ∈F with ℓ|N, necessarily ℓ≠p,q (both are units of N). The nonzero rational number q^(2e)p^(−2)−1 has ℓ-adic valuation at least v_ℓ(N), because its numerator (q^e−p)(q^e+p) is divisible by N. The ordinary, **unnormalized** first upper bound of [Bugeaud, Theorem 1.3, pp. 4–5, after Yu](https://arxiv.org/pdf/2209.00275), applied over Q to the bases q,p with coefficients 2e,−2, gives v_ℓ(N)≪_{F,p}log(2q) log(2e). The degree, number of logarithms, local prime and p-height are fixed, and B=max(3,2e). The bound is uniform over ℓ∈F, including 2. Primes ℓ equal to p or q or not dividing N contribute zero. Because e→∞, this is o(L); the sum over F contradicts log N_F∼L. This input alone only needs log N_F bounded below by a fixed positive fraction of L.
* The q row has total macroscopic weight one. Its only possible missing factor is p. If a_q log p≥c L on an unbounded subsequence, use the primitive pair (N,q) at infinity and at the fixed places in F∪{p}, with coordinate forms except at p, where they are X−Y,Y. Its unnormalized product is at most (N/N_F) q p^(−a_q) = N^(−c+o(1)), since p∤N and p≠q. This formula remains true if p∈F or q∈F: neither divides N, and any extra finite q factor is at most one. The pair has ordinary height N and cannot have constant rational ratio. The [p-adic Subspace Theorem, Evertse, Theorem 1.1](https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf) gives the contradiction. Thus a_q log p=o(L), as required.

With these two inputs the row capacities, gcd bounds, return-DAG and parity/weight tests, and the final exact odd-cofactor obstruction in the cited four-macro certificate are unchanged. The rank tests there require only the p,q independence cited above; the last rational-separation argument handles subpower tails by height and uses no smoothness of N. Its exact replay therefore excludes both γ intervals and proves conclusion 1.

## A fixed left relation without imposing bounded p or q exponents

All four positive weights are now less than one; on the chosen subsequence every x_i/N=O(N^(−η)) for some η>0. For any fixed integral c annihilating both R on the left and 1, prime factorization gives

    u log p + v log q = Σ c_i log(1−x_i/N)=O_c(N^(−η)),
    u=c·a=O_c(L),       v=c·b=O_c(L/log q).

If exactly one marked exponent is zero, the left side cannot be this small unless both vanish. Otherwise apply the real bound [Bugeaud, Theorem 1.1, (1.3)](https://arxiv.org/pdf/2209.00275) for p,q, with q the final marked base. Their multiplicative independence implies a nonzero form, with normalized parameter at most C_c(1+L/log q): the q coefficient is O(L/log q) and the p coefficient is O(L) divided by h*(q). For q→∞, writing U=L/log q→∞, the logarithm of its absolute value is at least −C_{p,c} log(2q) log(2U)=−o(L), impossible. Thus a,b are orthogonal to an integral basis of left-annihilators of [R,1] eventually, hence lie in its column space. Full A has rank ≥5: a rank ≤4 would give two zero eigenvalues, the two eigenvalues 1 from nullity(I−A)=2, its Perron root ρ≥2, and another eigenvalue −ρ−2 by trace zero, impossible. It follows that rank A=rank[R,1]=5 and rank R=4, with 1 outside col R. This argument after establishing that all weights are intermediate invokes no smoothness of N.

Write l for the fixed primitive left null vector of [R,1]. For the unique parent i of the actual largest M=x_j, l_i=0 by the j-th column of lA=0. Also l_j≠0: if it vanished, delete i,j from A. The four remaining coordinates retain a left zero-eigenvector l, and a nonzero mixed row at eigenvalue 1 obtained from dim ker((I−A)^T)=2 by killing i, hence j by the same maximum-column relation. Every such nonzero left vector is mixed by orthogonality to the positive right Perron vector of A. A four-by-four nonnegative zero-diagonal matrix of spectral radius r>1 would then have eigenvalues 0,1,r,−1−r, impossible. For r=1 the nonnegative Perron vector on the left is independent of the mixed eigenvector, giving 0,1,1,−2, again impossible. Radius <1 is ruled out by the eigenvalue 1. Thus l_j≠0. From lA=0 and l·1=0,
    
    ∏_i(1−x_i/N)^(l_i)=1,     Σ_i l_i x_i=O_l(M²/N)=o(M).

The last estimate expands the real logarithms uniformly at x_i/N=o(1). Therefore another index k with l_k of opposite sign must have x_k ≫_l M; otherwise the terms of that sign cannot balance |l_j|M. As p,q are subpower while M is macroscopic, this k is a distinct macro.

## Why the q-power cannot disappear from the leading scale

If all q-factors had logarithmic size o(L) on any further subsequence, take any fixed integer c in a basis of left-annihilators of R (no sum condition). The exact positive rational ratio

    Z=p^(c·a) q^(c·b) N^(−Σc_i)=∏_i(1−x_i/N)^(c_i)=1+O_c(N^(−η))

has log height O_c(L) and both its coprime numerator and denominator have prime-to-(F∪{p}) parts of logarithmic size o(L). Indeed |c·b|log q=o(L) and log(N/N_F)=o(L). For clarity, apply the two-dimensional Subspace Theorem to the coprime numerator,denominator pair at the fixed places F∪{p,∞}: use X−Y,Y at infinity, coordinates elsewhere. The product of the coordinate forms before replacement is exp(o(L)) by the product formula, and replacement adds a factor O(N^(−η)). Thus either the ratio is exactly one or only finitely many rational ratios occur, which is impossible for distinct ratios tending to one. A bounded height case is immediate. Unique factorization at p and q (both prime to N) and N>1 forces c·a=c·b=Σc_i=0. This for a basis of the annihilator of R contradicts 1∉col R. Accordingly max_i b_i log q/L has positive liminf on each fixed four-macro weight-convergent sequence, as claimed. The argument gives no lower bound on an individual unprescribed row nor an explicit universal numerical liminf.

For related terminal exponent-digraph work see [Kelanemer’s 2026 preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460). Its public abstract states broader claims, but the full argument was unavailable for direct comparison; no priority claim is made.
