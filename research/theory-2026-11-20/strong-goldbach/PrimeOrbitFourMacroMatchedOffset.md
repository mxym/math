# Three mutual pairs and a nonzero cofactor offset above the square-root threshold

Work in the W>1/2 sector of [the four-macro two-line theorem](PrimeOrbitFourMacroTwoLines.md). Thus a hypothetical unbounded sequence of six-label, strongly connected, all-composite prime-factor orbits has fixed seed p, near-smooth even centers N, a subpower nonseed prime q→∞, and four macros of strictly intermediate limiting weight. An arc x→y means y divides N−x; A_xy is its multiplicity. There are precisely two top primes M>K, both of weight W and larger than sqrt(N), with M/K tending to an odd integer r=p^k, k≥0. All other labels are o(K). The fixed c and positive D from the linked theorem give the exact identity

    (M/(rK))^D = ∏_x (1−x/N)^(c_x).

Pass to subsequences to fix the parent indices. The 1-eigen Gale matrix C has two rows spanning the left eigenspace and fixed columns g_x. As in the spectral argument of [the ramified seed theorem](PrimeOrbitRamifiedSeedList.md), the largest label M and its unique parent have nonzero proportional columns. Indeed, if both columns were zero, deletion would leave a nonnegative, zero-diagonal four-by-four matrix with two independent mixed-sign left eigenvectors at one, contradicting trace zero and the Perron bound on the remaining eigenvalues. Killing this nonzero pair in a nonzero left eigenrow shows every other column is nonzero, for otherwise that same row would vanish on three coordinates. Likewise no three columns are proportional, since a left eigenrow vanishing on three coordinates cannot have both a positive and a negative cycle in the remaining three loopless vertices. Every nonzero left eigenrow has both signs by Perron orthogonality. Each sign support contains a cycle: at each positive coordinate of hA=h at least one incoming term is positive, and likewise for negative. Let l be the fixed left null row of A; its M,K entries are nonzero. These facts and compulsory positive limiting q-power mass in at least one row are from the preceding [four-intermediate theorem](PrimeOrbitFourMacroNearSmoothIntermediate.md).

**Theorem.** The top primes have unique, distinct parents i,j among the four lower labels, respectively; the six vertices split into three mutual pairs, i↔M, j↔K, and U↔V for the two remaining labels. Put v=(N−i)/M and w=(N−j)/K. On a fixed chart, for all sufficiently late terms,

    w = rv + d,       d = −(r c_M+c_K)/D ∈ 2ℤ \ {0}.

In particular no growing prime can divide both cofactors: their gcd divides |d|. The result permits a fixed p-divisor of both. This is a necessary condition, not exclusion of the case d≠0.

**Matching.** M has only one incoming parent because all others are smaller and distinct smaller parents would differ by a nonzero multiple of M of smaller absolute value. Its multiplicity is one since M>sqrt(N). Hence lA=0 forces the parent to have l-coordinate zero, excluding K. Suppose M points to K. If M is its only parent, l_M=0, impossible. If K has another parent s, it is smaller, and K divides M−s. The integer (M−s)/K is even (M,s,K all odd), yet tends to the odd integer r. Thus neither top is parent of the other. Each top now has a unique lower parent, again with multiplicity one, and these parents cannot coincide because MK>N. CA=C gives g_i=g_M and g_j=g_K. These two directions are different, with no third column on either. A nonzero eigenrow killing the first direction has support exactly j,K,U,V; its entries at j,K coincide. Both sign supports need at least two vertices, so U,V are both of opposite sign. Each two-vertex sign support must form a mutual pair. Killing the second direction in turn gives i↔M.

**Constant offset.** A mutual pair t↔X has N=t+X+h t X: write N−t=v_X X; divisibility of N−X by t gives v_X≡1 mod t. Since v_X>1 is odd, h=(v_X−1)/t is positive and even. In particular i≤(v−1)/2, j≤(w−1)/2, and v,w grow with limiting weight 1−W. Taking logs of the exact identity and re-exponentiating gives

    M/(rK) = 1 − (c_M M+c_K K)/(DN) + o(K/N).

Indeed every other label is o(K), and the sum of the quadratic errors is O(M²/N²)=o(K/N). Therefore

    w−rv = (N/M)(M/K−r) + r i/M−j/K → −(r c_M+c_K)/D.

Here the first term equals (rN/M)(M/(rK)−1); using M/K→r gives the displayed limit. The difference is an even integer, so it is eventually a fixed even d equal to that limit.

**Why the offset cannot vanish.** Suppose w=rv; then e=M−rK=(j−i)/v is a bounded even integer, since i≤(v−1)/2 and j≤(rv−1)/2. It cannot be negative, as j−i>−v/2, nor zero since the parents differ. Fix e>0 on a subsequence. Since j=i+ev, h=(rv−1)/j is a bounded positive even integer; fix h. Rearrangement gives (r−he)v=hi+1, so r−he≥1 and i grows proportionally to v. Also v≡1 mod i, giving i|(r−he−1). Thus r−he=1, v=hi+1 and j=ri+e. Since i,j are of weight 1−W>0, they are the two remaining macros, and U,V are p,q. In particular p↔q and N≡p mod q. Set u=1+hK, so 1+hM=r u. The four rows are exactly

    N−i=Mv,     N−j=Krv,     N−M=riu,     N−K=ju.

If q divides v, then i,j≡N≡p mod q, so q divides (r−1)p+e. If q divides u, then M,K≡N≡p mod q, giving the same conclusion. This fixed integer is positive, while q→∞. Hence q eventually divides none of the four products (all other primes displayed are distinct from q and r is a p-power). Nor can it occur in its own row. Its exponent column b is therefore supported at the single p row. Since Cb=g_q, we get b_p g_p=g_q; both nonzero columns are fixed so b_p is bounded. This contradicts the positive limiting q-power mass as log q=o(log N). The offset cannot vanish.

For a related exponent-digraph approach see [Kelanemer (2026)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460); the full argument was not available to compare, and no priority claim is made.
