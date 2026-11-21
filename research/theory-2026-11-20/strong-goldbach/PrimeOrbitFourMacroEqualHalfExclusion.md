# Four equal half-weight nonseeds cannot occur

Assume the [four-intermediate fixed-seed hypotheses](PrimeOrbitFourMacroNearSmoothIntermediate.md): along a weight-convergent unbounded near-smooth sequence of even centers N there is a closed strongly connected all-composite six-prime orbit, with fixed seed p, subpower nonseed q→∞, and four nonseeds of positive logarithmic weights. Order those four physical primes M>K>U>V. They **cannot all have weight 1/2**. Consequently [the physical square-root result](PrimeOrbitFourMacroSquareRoot.md) leaves precisely three nonseeds of weight 1/2 and one with weight strictly between 0 and 1/2, besides p,q. This remains a necessary shape, not an exclusion or construction of a full six-label orbit, and not Goldbach.

**Finite input.** The row index order throughout is p,q,M,K,U,V (so the physical order is M>K>U>V>q>p eventually). A row of the 6×4 nonnegative integer matrix R lists the exponents of M,K,U,V in N minus that row's input. The following are all necessary for four equal weights 1/2.

1. Each projected row total is at most two, by the limiting factor size. At p it is positive; at q it is exactly two. These last statements are the two general arithmetic lemmas proved in the [four-intermediate theorem](PrimeOrbitFourMacroNearSmoothIntermediate.md): a macro-free p row would violate the fixed-F p-adic logarithm bound, and the possible fixed-prime factor in the q row has subpower size by the Subspace Theorem for the pair (N,q). The lemmas require near-smoothness and q→∞, not a weight-one macro.
2. A macro never appears in its own row; each macro can appear in at most one row whose input is smaller than that macro, since two smaller parents would differ by a nonzero multiple of the larger prime of smaller absolute size. No two projected rows are identical. Otherwise (N−x)/(N−y)=p^a q^b=1+O(M/N) for |a|≪log N, |b|≪log N/log q. The normalized Bugeaud bound (fixed p and sole moving base q) in the four-intermediate theorem forces this rational to equal one, since M/N is power-small; then x=y, impossible.
3. Write E for the four macroscopic coordinate columns of the six-dimensional identity. For each actual chart the left nullspace of R−E has dimension two, with a 2×6 rational basis C; it equals the left 1-eigenspace of the complete exponent matrix. C's columns at p and q are independent, by the independent seed-coordinate classes in the cited theorem. For every index, the nonzero row of that eigenspace vanishing there has at least two positive and two negative entries: each sign's support contains a cycle, hence two vertices (no loops). Equivalently the signed determinants of its Gale column with the other columns have these sign counts. The left nullspace of [R,1] is a line with generator l whose M coordinate is nonzero; it satisfies lA=0 and l·1=0.
4. There is an additional exact weight condition C·(2,2,1,1,1,1)^T=0, with no integrality assumption on limiting small-prime masses. Indeed let a,b be the exponent columns for p,q; Ca=C e_p and Cb=C e_q, fixed vectors. Multiplying C into the row logarithms divided by log N, the small-prime terms vanish because log p,log q=o(log N). The left side tends to C1, while macro terms give (1/2)CR·1_4=(1/2)CE·1_4. This proves the stated necessary equality.
5. Since ∑l_x log(N−x)=0 exactly, the running sums of l in decreasing physical-prime order (M,K,U,V,q,p), excluding the automatic zero total, have both signs. Otherwise summation by parts against the strictly increasing log(N−x) produces a strict nonzero sum; not all partial sums vanish as l_M≠0.

**Exact census and completeness.** The row-first [Node.js checker](four_half_rows.js) generates every allowed four-entry vector and fills each row in turn, rejecting forbidden duplicate rows and smaller parents. It computes signed maximal minors (Bareiss) of R−E and [R,1], tests 3–5 above and prints terminal charts. All determinants involve integer matrices of order ≤5 with entries in [−1,2]; their minors and the small products in Bareiss are exact in binary64 integer arithmetic (even the coarse 5!·2^5 bound is ample). A separate [column-first Python checker](four_half_columns.py) generates arbitrary capped six-entry columns, enforces total capacity recursively, then computes both nullspaces by primitive integer elimination, not by maximal-minor determinants. Both enumerate labeled charts with physical macro order fixed; there is no isomorphism reduction. Run node four_half_rows.js and python3 -O four_half_columns.py. The SHA-256 column below hashes the lexicographically sorted newline-terminated list of 24-digit row-major codes at each stage (one digit per entry).

    row/column local tests  16609  4ada98bb881f0a69aba8954f59d892f8e3d12d226425ebd85b6f63c231c2dc03
    both rank/Gale tests      902  437c68cb327280661851b6b944b2d38b672becb0bc7ca1eea2834b59cfd37fed
    exact equal-weight law     20  496198b394f416d1c061160ec34a91515f9c416f92d4e5c2f4935eb42dafa879
    log monotonicity            4  ac3b9c72d5945abadc8a0088a110210f4c231edc8e631d8129aed9ad7de0ca1c

The final four are shown grouped by rows:

    0100 0002 0020 0011 1000 0010     l up to sign: (0,1,1,−2,0,0)
    0100 0020 0002 0011 0001 1000     l up to sign: (0,1,1,−2,0,0)
    0200 1001 0000 0010 0001 0020     l up to sign: (0,0,1,−2,0,1)
    1001 0200 0000 0010 0001 0020     l up to sign: (0,0,1,−2,0,1)

**Terminal contradictions.** In the first two, the first-moment estimate ∑l_x x=O(M²/N) gives M/K=2+O((q+M²/N)/K)=2+O(N^(−η)) for fixed η>0: q=N^o(1), M²/N=N^o(1), K=N^(1/2+o(1)). By the [fixed algebraic ratio lift](PrimeOrbitFourMacroThirdThreshold.md), 2 must be a rational power of the fixed odd prime p, impossible by the 2-adic valuation after clearing the exponent's denominator.

In the last two, l gives the *exact* geometric progression (N−K)²=(N−M)(N−V). The exponent 2 in the K column of the p row (third chart) or the q row (fourth chart) implies K²<N. Expanding the geometric progression gives the positive integer

    2K−M−V = (K−V)²/(N−V).

But (K−V)²=K²−V(2K−V)<K²−V<N−V because V<K and the inputs are odd primes. Thus the integer lies strictly between zero and one, impossible. This closes all 20 equal-weight charts without requiring realizability of any earlier sieve survivor.

[Kelanemer (2026)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) works in a related terminal exponent-digraph framework. Its full argument was unavailable for direct comparison; no priority claim is made.
