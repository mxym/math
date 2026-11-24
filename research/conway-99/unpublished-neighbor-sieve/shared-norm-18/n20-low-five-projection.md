# Five low-angle norm-twenty markings cannot share one seed

In a hypothetical SRG(99,14,1,2), let \(P=(3I-A+J/9)/7\) be the real orthogonal projector onto the \(-4\) eigenspace. A signed-unit norm-twenty marking is a vector \(t\) in this eigenspace of squared norm 20 with ten sites of each sign. Assume its two signs induce independent sets, as is automatic when the actual signed-unit \((2,28)\) shell is absent: if two same-sign sites \(x,y\) are adjacent, switch the orientation to make them negative and add \(d_x+d_y\), where \(d_i=(3I-A)e_i\). This gives a charge-two cost-28 label, necessarily unit because a positive doubled entry gives charge one cost at most 15, below 21, and a negative doubled entry gives charge three cost at most 31, below the absolute charge bound 33. Such a norm-twenty marking has four opposite neighbors at every marked site.

Fix a positive rooted seed \((o,Q)\): \(t_o=1\), \(Q\) is its four negative neighbors, and all other neighbors of \(o\) have value zero. The vertices of \(Q\) lie in four different mate pairs of \(N(o)\). For each parent pair in \(Q\), its other common neighbor apart from \(o\) is one of six distinct far centers. A far vertex has two neighbors in \(N(o)\), so both parents of a center are in \(Q\). The center is never negative, since the signs are independent. Write \(A_C\) for adjacency on the six centers.

**Claim.** There do not exist five actual distinct markings at one seed with all ten pairwise dots at most six. In particular, if all possible dots between distinct markings at a seed belong to \(\{5,6,9,10\}\), then any fourteen markings contain a triangle of dots 9 or 10, by \(R(3,5)=14\). This is not by itself an upper bound of thirteen on seed multiplicity.

## Projection onto the near set

Set \(T=N[o]\). For any vector \(t\) in the eigenspace, the projection onto the span of \(Pe_i\) for \(i\in T\) is \(t_0=P c\), where \(c\) is supported on \(T\) and solves \(P_{TT}c=t_T\). This is the ordinary normal equation: agreement of the coordinates on \(T\) is precisely orthogonality to that span. We may set \(c_o=0\); below the formula constructs a solution with that gauge. Let \(s=\sum_T c_i/9\). In the equation \((3I-A_T+J/9)c=7t_T\), the root equation is \(-8s=7\). For a mate pair \(i,i'\) in \(N(o)\), the equations give
\[
c_i=7/16+(21t_i+7t_{i'})/8 .
\]
Indeed \(3c_i-c_{i'}=7t_i+7/8\), and these values sum to \(9s=-63/8\). In particular the four parents have \(c_q=-35/16\), so \(\|t_0\|^2=t_T^Tc=35/4\). Every center \(x\) has near evaluation \(t_0(x)=(s-2(-35/16))/7=1/2\). The projection is the same for every marking at this seed; every residual marking \(t-t_0\) takes value \(1/2\) or \(-1/2\) at each of the six centers.

## Six-center residual Gram

Project the six \(Pe_x\) orthogonally off the same near span. Their Gram is
\[
 S=S_0-A_C/7,\qquad S_0=(3/8)I-J/56+3R/56,
\]
where \(R\) is the permutation matrix pairing each parent pair with its complementary pair in \(Q\).

To check, use the same near equations for the right-hand side \(P_{Ty}\) of a center \(y\). If \(g_i=1\) on its two parents and zero on the other near sites, then \((3I-A_T+J/9)c\) has right-hand side \(1/9-g_i\) at each \(i\), root included. With \(c_o=0\), these give \(s=-1/72\) and \(c_i=1/16-(3g_i+g_{i'})/8\). Thus the near contribution to the inner product of \(Pe_x,Pe_y\), for \(x,y\) having \(k\) common parents, is \((-5/36+3k/8)/7\). This supplies \(S_{xx}=5/14\), \(S_{xy}=-1/56-A_{xy}/7\) for shared-parent centers, and \(S_{xy}=1/28-A_{xy}/7\) for disjoint parents.

The involution \(R\) has a \(+1\) space of dimension 3 containing the constants. The eigenvalue of \(S_0\) on constants and the \(-1\) space is \(9/28\); on the remaining \(+1\) space it is \(3/7\). Every center has at most three center neighbors: its far neighbors have exactly six total incidences into \(Q\), since two parents give one common neighbor each and the two nonparents give two each. All such common neighbors are far because its only near neighbors are its two parents, which are independent from all of \(Q\). Any neighboring center uses two of the six incidences. Consequently \(\|A_C\|\le3\), and \(S\preceq(6/7)I\). This part covers centers with arbitrary physical label edges, not just independent centers.

## Contradiction

For five markings \(t_i\) whose pairwise dots are at most six, put \(z=\sum(t_i-t_0)\). The projected energy gives
\[
 \|z\|^2\le5(20-35/4)+20(6-35/4)=5/4 .
\]
But each of its six center values is a half-odd-integer. The matrix of the six corresponding projected evaluation vectors has Gram \(S\) and hence the squared norm of its evaluation map is at most \(6/7\). Therefore \(3/2\le\sum_{x\in C}z_x^2\le(6/7)\|z\|^2\), giving \(\|z\|^2\ge7/4\), contradiction.

No rank or seven-residue assumption enters. We assumed independent sign shores and the common 15-site seed pattern, not any absence of shells beyond what is needed to supply those premises and the stated angle alphabet. The high triangles themselves are not excluded by this argument.
