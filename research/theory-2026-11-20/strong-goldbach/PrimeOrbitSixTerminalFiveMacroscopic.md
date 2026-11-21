# The seed column cannot be a new direction in a six-label terminal with five macroscopic primes

Fix a finite set F of primes, an odd prime p and δ>0. At all sufficiently large even F-smooth N coprime to p, let a six-label strongly connected, factor-closed all-composite orbit contain p and five other primes ≥N^δ. Write A for its prime-exponent matrix. Then **the p-column of A belongs to the rational span of the other five columns**. In particular A cannot be invertible. This rules out the entire invertible-A branch with five macroscopic nonseed primes. Neither singular A nor configurations with fewer than five macroscopic nonseed labels are excluded.

The [one-seed rank theorem](PrimeOrbitMovingSeed.md) and the six-vertex upward-forest feedback bound there give nullity(I−A)=2. All six labels are ≤(N−3)/3 since they occur in a terminal all-composite orbit. The geometric lemma next only needs these structural assumptions and the five polynomial lower bounds; it does not use F-smoothness.

## At most one weight-one label

On any sequence N→∞ with convergent logarithmic weights w_x=lim log x/log N, call y high if w_y=1. All nonseed weights are ≥δ. For every high y, choose a parent x (a row containing y). For all sufficiently large terms, y occurs once and its cofactor in N−x is N^{o(1)}. As all labels other than p have weight ≥δ and every row is composite, we must have N−x=p^a y with a≥1. Its parent cannot be p. In fact the parent is unique: two distinct such rows would have distinct powers of p as cofactors, but their ratio lies in [2/3,3/2], impossible as p≥3. Each parent has at most one high child because a row cannot contain a product of two high primes. Pass to subsequences to fix the finite incidences.

Choose, separately in each graph, a real nonzero f with Af=f and f_p=0; this is possible by nullity two. It changes sign: A is irreducible, nonnegative and has spectral radius at least two. Each sign group contains a directed cycle because every positive (negative) entry has a positive (negative) successor, and hence at least two members since loops are impossible. Therefore at most one nonseed entry can have value zero. On a high-parent row f_x=f_y. This common value cannot be zero since x,y are different nonseed labels. Nor can x,y lie in a two-member sign group: those two would form a mutual pair, forcing xy<N by the mutual formula N=x+y+hxy, h≥2. This contradicts w_x≥δ, w_y=1. Thus if high vertices occur, every high label and its parent belong to the unique group of three of the same sign. The two other nonseed labels have the opposite sign. One may fix the sign partition on a subsequence; the vector f itself need not be fixed.

A cycle entirely among high labels is impossible. Write its successive equations N−y_i=u_i y_{i+1} with u_i=p^{a_i}=N^{o(1)}. Composing the affine maps gives (∏u_i−(−1)^j)y_1 as an integer multiple of N for a cycle of length j. Coprimality gives N|∏u_i−(−1)^j, yet the latter is strictly positive and N^{o(1)}. Thus high chains have a nonhigh parent. If there were at least two high vertices, the three-member sign group, uniqueness of the high parent, and the one-high-child bound would force exactly the chain x→y→z with x nonhigh and y,z high. Indeed disjoint chains would require at least four vertices, and a three-high group would contain a high cycle. The final z must have a successor of its own sign. It cannot point to either of the two high labels (they already have a different unique parent), so it points to x. With N−x=p^a y and N−y=p^b z we obtain
     
    p^{a+b}(N−z)=(p^{a+b}−p^a+1)N−x.

Since x|N−z and (x,N)=1 it follows that x divides p^{a+b}−p^a+1, a positive N^{o(1)} integer. This contradicts x≥N^δ. We have proved: **at most one high label** on every convergent weight subsequence.

## Recovering the fixed seed and the final single correction

Suppose the p-column of A increases the rational rank of the other columns. Those other columns are bounded by a constant depending on δ. By taking finitely many subsequences fix their entries. There is then an integer column c annihilating the five columns on the left, but with D=cᵀ A_{*,p} nonzero. More precisely, a fixed finite integral basis of the left nullspace of the fixed columns is available, and at least one basis element works at each term; pass to a subsequence and choose its sign so D>0. All c_i are fixed, not just O(polylog N); D=O(log N). Put m=Σc_i, L=log N. Taking logarithms of the actual row factorizations yields
     
    D log p = m L + Σ_i c_i log(1−x_i/N).                              (1)

If every w_i<1, the corrections are O(N^{−ε'}) on this subsequence for some fixed ε'>0, impossible: expanding N over F, the nonzero form D log p−m log N has logarithmic absolute value ≥−C(1+log L) by [Matveev's fixed-base lower bound](https://doi.org/10.1070/IM2000v064n06ABEH000314), since p∤N and D>0. Otherwise let y be the unique high label and x its nonhigh parent. All remaining inputs including x are ≤N^{1−ε'} along the subsequence. Write N−x=u y, u=p^a=N^{o(1)}, a≥1. If log u>(log L)^2, then y/N≤1/u and (1) contradicts the same fixed-base lower bound. Otherwise h(1−1/u)≤(log L)^2, with h the naive logarithmic rational height, and
     
    log(1−y/N)=log(1−1/u)+O(N^{−ε'}).

The last identity follows from (1−y/N)/(1−1/u)=1+x/((u−1)N). Hence the corrected form D log p−m log N−c_y log(1−1/u) is O(N^{−ε'}). If nonzero, the rational Matveev estimate, for example [Theorem 2.1 here](https://doi.org/10.1007/s12188-025-00293-9), has log absolute value bounded below by −C(1+log L)^3: only the one extra rational base has variable height, all integer exponents are O(L), and F,p are fixed. Contradiction, so
     
    p^D=N^m(1−p^{−a})^{c_y}.

Taking p-adic valuations gives D=−a c_y, in particular c_y<0. Cancelling powers of p now gives N^m=(p^a−1)^{−c_y}. The right side is strictly greater than one but N^{o(1)} (c_y fixed). This contradicts integer m and N→∞, proving the column-span conclusion. The limiting argument is uniform for fixed δ,p,F: any unbounded countersequence admits all the indicated finite choices and compact weight limits.

**Comparison through November 21, 2026.** The [invertible exponent-matrix count](EACJacobianSquareRoot.md) controls how many centers carry such components but does not give this exclusion or the structural high-label bound. [Kelanemer, August 12, revised September 6](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats the nearby terminal exponent-matrix framework; its full text was unavailable, so no priority or comprehensive nonoverlap claim is made.
