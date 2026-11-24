# Six separated low triangles cannot occupy a norm-twenty seed

This proves a scoped obstruction, not a general upper on seed occupancy. In a hypothetical SRG(99,14,1,2) suppose true neutral minimum is 20 and the relevant norm-22 fields are signed units (indeed all norm 22 fields are units under the minimum). Suppose every selected norm-20 source has independent sign shores, as follows when actual unit charge-two cost 28 is absent. At a common positive four-parent seed \((o,Q)\), there do not exist **six disjoint triples** of norm-20 markings such that within each triple the pairwise dot is 6, and between every two different triples the pairwise dot is 9.

Use the earlier [full far-coordinate theorem](n20-full-far-floor.md) and its notation \(Q\) for the four chosen parents, \(R\) for their four mates, \(B\) for the six positions on the three remaining axes. The six centers are the \(QQ\) far labels. For every source \(t\) let \(v=t-t_0\), where \(t_0\) is the orthogonal projection onto the common near span and has squared norm \(35/4\). A within-group dot-six triangle has every center selected in one or two of its three sources, and the sum on every zero-parent far site is \(-1\) or zero.

## Exact Schur restrictions at the six centers

The residual Gram for the 18 sources, in the six blocks of three, is
\[
 H=14I-3\,\operatorname{diag}(J_3,\ldots,J_3)+J_{18}/4 .
\]
Its eigenvalues on the within-block contrasts, block constants with total sum zero, and overall constants are respectively \(14,5,19/2\). These are all positive. Let \(X_x=(v_i(x))_{i=1}^{18}\) be the vector of residual field values at a far site \(x\), and \(S_{xy}\) the Gram of the corresponding far evaluation vectors projected off the near span. The Gram of the evaluation vectors after also removing the span of the residual fields is \(S_{xy}-X_x^TH^{-1}X_y\), hence positive semidefinite.

For any far label \(x\), \(S_{xx}=5/14\). More generally, if two distinct vertices \(x,y\) have \(k\) actual parents in common and \(\ell\) parent-mate coincidences, then
\[
 S_{xy}=(1/4-(3k+\ell)/8-A_{xy})/7 .
\]
To see this, the near coefficient vector of \(Pe_y\) is \(c_o=0\), \(c_i=1/16-(3g_i+g_{i'})/8\), where \(g_i\) is the indicator of the two parents of \(y\) and \(i'\) is the mate of \(i\). Its total coefficient sum is \(-1/8\). Substitute the two parents of \(x\) in the near evaluation formula and subtract the result from \(P_{xy}\). This works for arbitrary far labels, including parent-mate coincidences.

At a center \(c\), the column \(X_c\) has entries \(\pm1/2\), with block sums \(\sigma_g/2\), \(\sigma_g\in\{-1,1\}\). Its squared components have within-block mass \(4\), total block-constant mass \(1/2\), and overall constant mass \((\sum_g\sigma_g)^2/72\). If not all \(\sigma_g\) agree, the resulting Schur cost is at least
\[
 2/7+1/10-(16/72)(1/5-2/19)>5/14,
\]
contradiction. Thus each center has the same majority sign \(\sigma_c\) in all six groups. Its residual diagonal after subtracting the field-span contribution is
\[
 \Delta_c=5/14-(2/7+1/19)=5/266 .
\]
For a pair of centers \(c,c'\), let \(n\) count groups in which their unique minority indices agree. The removed field-span inner product is
\[
 \sigma_c\sigma_{c'}((n-2)/14+1/19).
\]
By the \(2\times2\) Schur inequality its difference from \(S_{cc'}\) has magnitude at most \(5/266\). Multiplying by 1064, the tolerance becomes 20 and the unsigned field-span possibilities are \(-96,-20,56,132,208,284,360\) for \(n=0,\ldots,6\). For centers sharing a parent, the physical values are \(-19\) if nonadjacent or \(-171\) if adjacent. Only positive sign product, no adjacency, and \(n=1\) pass. The shared-parent graph of the six centers is connected, so all \(\sigma_c\) agree, and they must all be positive because each source selects at least three centers. For complementary parent pairs the physical values are 38 or \(-114\); the two possibilities are \(n=2\) for a nonedge or \(n=0\) for an edge.

In each group six minority indices distributed over three sources give at least three coincident pairs (minimized at multiplicities \(2,2,2\)). Across all six groups there must be at least 18 coincidences. But the twelve shared-parent pairs give exactly 12 and the three complementary pairs give at most six. Equality therefore holds, each minority index occurs exactly twice in every group, and the complementary pairs are nonadjacent. Most importantly, every source selects exactly four centers and consequently has exactly one positive site missing all four \(Q\) parents.

## Conflict sites and the contradiction

Each of those positive zero-parent sites must be negative in at least one other source of its own group, since the low group's sum on such sites is nonpositive. Two sources of a group cannot use the same positive zero-parent site, since two positives and at most one negative would leave a positive sum. And a site with opposite signs within a group cannot be occupied at all by a source of another group, because their cross dot is 9 and their difference is a signed-unit norm-22 field. Thus the 18 sources require 18 distinct physical zero-parent conflict sites.

We next show that none of these conflict sites can be of type \(RB\) or \(BB\), using only binary Schur minors and requiring no adjacency hypothesis beyond sign-independent shores. At a conflict site \(y\), its nonzero source pattern is in one triple, either \((1,-1,0)\) or \((1,-1,-1)\) up to permutations. Write \(s\) for its sum (zero or \(-1\)), \(n_2\) for its squared norm (two or three), and \(f=t_0(y)\). The field-span cost at \(y\) is
\[
 D_y=(n_2-s^2/3)/14+s^2/18+(s-18f)^2/171 .
\]
For a center \(c\), let \(v=t_i(y)\) in the one source \(i\) omitting \(c\) in the conflict triple. The removed field-span inner product is
\[
 C_{cy}=(s/3-v)/14+(s-18f)/57 .
\]
These formulas follow by projecting onto the same three eigenspaces of \(H\): a center has no block-contrast component and its within-block fluctuations are \(1/3-\mathbf1_{\{i\text{ omits }c\}}\) in each block. The necessary minor inequality is
\[
 (S_{cy}-C_{cy})^2\le(5/266)(5/14-D_y).
\]

On an \(RB\) single conflict choose any of the two centers omitted by the negative source, so \(v=-1\). Then \(f=-1/8\), \(C_{cy}=1/14+3/76\), and \(S_{cy}\le1/28\), because the parents of \(y\) are not in \(Q\). The inequality fails. On \(BB\), the same negative-source choice with \(f=-1/4\) fails for both single and double conflicts. Finally, for an \(RB\) double conflict, take any center containing the mate of its one \(R\) parent. The parent-mate count is \(\ell=1\), so \(S_{cy}=1/56\) or \(-1/8\). Regardless of whether its omitted source has \(v=1\) or \(-1\), both alternatives fail. The following exact arithmetic suffices to replay these four tests.

~~~python
from fractions import Fraction as Q
D = Q(5,14)
gap = Q(5,266)
for f, s, n2, v, possible in [
    (Q(-1,8), 0, 2, -1, (Q(1,28),)),
    (Q(-1,4), 0, 2, -1, (Q(1,28),)),
    (Q(-1,4), -1, 3, -1, (Q(1,28),)),
    (Q(-1,8), -1, 3, -1, (Q(1,56), Q(-1,8))),
    (Q(-1,8), -1, 3, 1, (Q(1,56), Q(-1,8))),
]:
    h = (n2-Q(s*s,3))/14 + Q(s*s,18) + (s-18*f)**2/171
    ip = (Q(s,3)-v)/14 + (s-18*f)/57
    if len(possible) == 1:
        assert ip > possible[0]  # the listed value is an upper bound
    assert all((x-ip)**2 > gap*(D-h) for x in possible)
~~~

Thus all 18 distinct conflict sites would have to be \(RR\) labels. There are only \(\binom42=6\) such graph vertices. This proves the stated specific obstruction, not an upper of 17 (or any other bound) on unrestricted marking multiplicity at the seed. It does not eliminate a rank-36 palette.
