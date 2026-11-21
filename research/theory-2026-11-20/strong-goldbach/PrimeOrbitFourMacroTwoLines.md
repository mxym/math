# Two top intermediates force two genuine exponent lines in the four-macro branch

Use the hypotheses and notation of [the four-intermediate theorem](PrimeOrbitFourMacroNearSmoothIntermediate.md): a strongly connected six-label fixed-p orbit at an unbounded near-smooth sequence, with other small prime q→∞, log q=o(L), L=log N; four macroscopic labels of weights strictly below one; and a fixed six-by-four macro exponent chart R. Write a,b for the p,q columns of the full A. The square-root retention theorem [here](PrimeOrbitHalfAboveRoot.md) gives at most two labels strictly above sqrt N. Thus if the largest limiting weight W exceeds 1/2, exactly two macros attain it: one more by the fixed opposite-sign large-label balance, and no third. Write M>K for the two top physical primes, after fixing their indices; the remaining two macros are eventually at most sqrt N.

**Conclusion in this case.** There is an integer k≥0 depending only on the fixed chart, ordering and fixed p with
     
    |M−p^k K| ≪ M²/N .

More importantly a and b each lie in an affine rational line determined by that chart, ordering and p (after the subselections described below). These are genuine dimension-one restrictions for the ambient linear equations, not an assertion that every integer point on either line is realizable. Thus each column has at most one independent integer parameter. Its nonnegative unbounded direction, if any, can be oriented nonnegative; the q column must have an unbounded direction carrying polynomial q-power mass. This is a dimension reduction; neither the resulting pair of lines nor the whole four-macro branch is excluded.

When exactly two macros attain W<1/2, that sector is impossible. For exactly two attaining W=1/2, the displayed estimate still holds and yields a subpower integer difference; we do not apply the two-line proof, which uses two actual labels larger than sqrt N, to this boundary.

## The integral ratio and initial planes

Let l be a fixed primitive generator of the left null line of [R,1], hence also of A. It has nonzero coefficient at M and forces another comparable macro of the opposite sign. With exactly two macros of maximal weight, the only candidate is K. From Σl_i x_i=O(M²/N) and the fixed weight gap to all other labels,
     
    M/K=r(1+O(N^(−η))),         r=−l_K/l_M>0,

for some fixed η>0, reduced if necessary in what follows. Since [R,1] has rank five, choose a fixed integer row c and positive integer D with cR=D(e_M−e_K) on the four macro coordinates and c·1=0. Prime factorization gives
     
    (M/K)^D p^(c·a) q^(c·b)=∏(1−x_i/N)^(c_i)=1+O(M/N).

Consequently the positive rational p^(c·a) q^(c·b) r^D differs from 1 by O(N^(−η)). A nonzero log of this rational has magnitude ≥exp(−o(L)) by [Bugeaud, Theorem 1.1 (1.3)](https://arxiv.org/pdf/2209.00275): use the fixed primes dividing pr, with coefficients O_c(L), and q as the sole moving base with coefficient O_c(L/log q). The normalized parameter is O(1+L/log q). Omit absent bases; when q has zero net coefficient use the usual fixed-base estimate (or elementary discreteness for p^u r^D). q→∞ is eventually coprime to pr. It follows exactly that c·b=0 and p^(c·a)r^D=1. Rationality of r and M/K≥1 give r=p^k with k≥0 integral, c·a=−kD. Substituting back into the exact ratio identity now yields |M−p^k K|≪M²/N. For W<1/2 this nonzero integer has absolute value o(1), a contradiction (distinct primes also exclude equality for k=0). The W=1/2 statement follows similarly without forcing vanishing.

Fix a two-by-six left eigenbasis C at 1, independent of the terms because it is the left null space of the four columns E_M−R of I−A, of rank four. For each marked column x=a,b with its matching own input s=p,q respectively, the equations
    
    Cx=C e_s,      l·x=0,      x_s=0

cut out an affine two-plane, given actual consistency. In this notation C e_s means the s-th column of C. C and l give three independent linear equations since l is a left eigenvector at 0. No coordinate row e_s belongs to their span: multiplication by A would give the nonzero nonnegative row A_s in the left eigenspace at 1, whereas every nonzero member of that eigenspace is mixed by Perron orthogonality. The additional chart equation is c·a=−kD or c·b=0. Proving each new equation independent reduces each plane to a line. We now assume W>1/2.

## A redundant equation would force a mutual p,K pair

Suppose the extra equation is dependent for the marked column with input s. Then c=h+αl+t e_s, h in row span C. Multiplying by A, using the known c·a,c·b,cR, gives (now with full six-coordinate unit rows)
    
    h=D(e_M−e_K−k e_p)−t A_s,      t=−kD/(κ_s−1),       κ_s=Σ_j A_sj≥2.

The formula for t follows by summing coordinates and using c·1=l·1=0, so h·1=−t. If k=0, then t=0, and the nonzero h has at most two supported coordinates, impossible. Indeed both sign supports of a nonzero left eigenvector at 1 contain directed cycles, hence at least two vertices apiece. For k>0 one has t<0. The row h can have negative coordinates only at p,K and is not zero (h_M≥D). Consequently both p and K are negative and form a directed two-cycle. In particular the K column can only have the lower parent p and possibly the unique larger vertex M: two different smaller parents would give a nonzero difference of absolute value below K divisible by K. All occurrences of K,M have multiplicity one because both exceed sqrt N. Write ε=A_MK∈{0,1}. The K-column equation reads
     
    h_K=h_p+ε h_M.

If s=p, the p row contains K and cannot also contain M, hence h_p=−kD, h_M=D and h_K=−D+kD/(κ_p−1). Thus ε=k−1+k/(κ_p−1). For k≥2 this is greater than one; k=1 requires κ_p=2, which makes h_K=0 against strict negativity. The p-column equation is independent.

## Eliminate the possible q-column degeneracy

Suppose instead s=q. The coordinate h_q=0 by looplessness. The largest M has a unique smaller parent; this parent cannot be p (already using K), K (negative whereas h_M>0), or q (zero h_q). It must be a lower macro U; call the other lower macro V. The q row thus uses neither M nor K (K has p as its unique smaller parent). We obtain h_M=D, h_U=D from the M-column relation, and h_K=−D. Set m=(κ_q−1)/k. Then A_qU=m by the formula for h_U, so m is a positive integer. Write a_*=A_qp and n=A_qV. The K-column relation and the q-row total give
    
    a_*=(k−1−ε)m,       n=εm+1 .

In particular h_p/D=−1−ε, h_V/D=ε+1/m, and every other h-coordinate divided by D is an integer. The V column of hA=h involves no V-loop, so h_V/D is an integer as well. Thus m=1; the q row is exactly

    N−q=p^(k−1−ε) U V^(1+ε).

In particular q is a smaller parent of both U,V, so p cannot use either in its own row; nor can p use M. The p row must be N−p=K q^B for some B≥1. If ε=1, K divides both N−M and N−p. The integer (M−p)/K tends to p^k, hence eventually equals p^k; this would make M=p^k K+p divisible by p since k>0, impossible.

If ε=0, the fixed q row gives w_U+w_V=1. Both U,V are at most sqrt N eventually by the established four-retained theorem since M,K are already strictly above it. Therefore w_U=w_V=1/2. The unique parent U of M satisfies N−U=uM where the cofactor u has weight 1−W<1/2. It can contain no macro, hence u=p^A q^E with nonnegative A,E. Comparing with N−p=K q^B gives
     
    q^B/u=(M/K)(N−p)/(N−U)=p^k(1+O(N^(−η))).

By the same normalized two-log bound (exponents B−E=O(L/log q), A+k=O(L)), this ratio equals p^k exactly after discarding finitely many terms. Then q^B=p^k p^A q^E contradicts k>0. This rules out the last redundancy. Both additional equations are independent, proving the two affine-line claim.

Each line is rational and contains integer points; its integer points are a translate of a rank-one integer lattice. If its physical column is unbounded choose one of its two ray orientations and then all directional entries must be nonnegative (each exponent stays nonnegative). The previous compulsory mass theorem guarantees the q column is unbounded. No independence between its parameter and that of the p column is asserted.

For neighboring terminal exponent-digraph work, see [Kelanemer (2026)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460). The full argument was not available for comparison; no priority claim is made.
