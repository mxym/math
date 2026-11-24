# Top-height norm-twenty markings

In a hypothetical SRG(99,14,1,2), let \(t\) be a signed-unit neutral norm-20 field with independent sign shores \(P,N\), ten sites each. The sign-independence premise holds when the actual unit \((2,28)\) type is absent, by the [standard edge switch](n20-low-five-projection.md). There is no rank assumption.

Every marked site has four opposite neighbors. For an exterior site \(x\), the equal numbers of its \(P\) and \(N\) neighbors define its height \(h_x\); extend \(h\) by zero on \(P\cup N\). Then
\[
 h=A1_P-4\,1_N=\tfrac12(A-4I)|t|,\qquad
 Ah=20\mathbf1-5h-4|t|.
\]
Indeed the expressions for \(h\) agree by sign independence and the eigen-equation. Substitute \(A^2=12I-A+2J\) in \(Ah=A^21_P-4A1_N\), using the symmetric expression for \(A1_N\). Because \(h\ge0\), every exterior height is at most four. On the 79 exterior sites, \(\sum h=100\). The common-neighbor budget on the independent \(P\) has \(2\binom{10}{2}\) slots, ten of its \(N\)-sites using six each, so \(\sum\binom h2=30\) outside. Writing \(n_i\) for the exterior counts, these identities imply
\[
 n_0=79-100+30-n_3-3n_4=9-n_3-3n_4.
\]

If \(h_x=4\), all six unmarked neighbors of \(x\) have height zero, since \((Ah)_x=0\). Thus \(n_0\ge6\), and the moment identity forces \(n_4=1,n_3=0,n_0=6\). The six zero-height neighbors cannot be mated to a marked vertex since they have no contact to the support at all. Hence the seven mate pairs in \(N(x)\) split as four full pairs with one site of each sign (the shores are independent), and three pairs entirely unmarked.

## Exact signed support

On the usual 15 near sites \(N[x]\), the near-space coefficients for the real projection onto the span of their \(-4\) marks are \(c_x=0\), \(c_v=(7/4)t_v\) for each first-layer vertex; their sum is zero and they solve the normal equation for \(P_-=(3I-A+J/9)/7\). The projected near energy is \(\sum t_vc_v=14\). For a far vertex labelled by the parents \(p,q\) on distinct mate axes, the projected value is
\[
 f(p,q)=-\frac{t_p+t_q}{4}.
\]
Among the 84 labels, twelve have \(|f|=1/2\) (same signed parents on two selected axes), forty-eight have \(|f|=1/4\) (one marked parent, one unmarked), and twenty-four have \(f=0\). Any integral \(t\) with these near data has squared far distance at least \(12/4+48/16=6\) from \(f\). For norm twenty equality holds, so every far value is a nearest integer. Exactly twelve support sites remain after the eight near support sites. Consequently all twelve half-integral labels are occupied: the six pairs of positive parents have value \(-1\), the six pairs of negative parents have value \(+1\), and all other far sites are zero. Every occupied far site has its two opposite-signed parents and two further opposite contacts; these further contacts are precisely a 2-regular bipartite graph on the six plus and six minus far sites. This is a necessary support description, not a converse guaranteeing a marking for assigned axes.

## At most one antipodal orientation for four given axes

At fixed \(x\) and fixed four selected axes, the necessary marking depends linearly on four signs \(\epsilon_i\in\{-1,1\}\) orienting the mate pairs. In fact it is \(\sum_i\epsilon_i b_i\), where \(b_i\) has its two near values \(+1,-1\) on axis \(i\), value minus half the signed coordinate of the \(i\)-parent at each far label between \(i\) and another selected axis, and zero elsewhere. The \(b_i\) have squared norms five and are pairwise orthogonal (products on a shared four-site cell cancel).

For two distinct antipodal orientation lines we may select signs differing on one or two axes. If one, their difference has norm twenty and doubled near sites, impossible because every raw neutral norm-twenty field is unit. The latter elementary fact follows by a \(d_v=(3I-A)e_v\) shift at an exceptional entry and the charge-one minimum 21: a positive double in a neutral field of cost twenty would give cost at most fifteen; reverse the field for a negative double.

If two axes differ, the difference \(w\) has norm forty. It has two positive doubles at near sites on the changed axes, and a third positive double at the far vertex whose parents are their two negative mates. These three are independent: the near sites lie on distinct axes, and the far site's two parents are not the two positive sites. Let \(D_S=\sum_{v\in S}d_v\) on the three positive doubles. Its norm is \(3\cdot23+2\cdot3\cdot2=81\), and \(w\cdot D_S=42\). Thus \(w-D_S\) has charge \(-3\) and cost 37. All three chosen coordinates become \(-1\) and its coordinate sum is \(+33\), which requires cost at least \(33+6=39\). This is impossible.

Therefore each root and each four-axis selection give at most one antipodal marking, and the root is uniquely recovered as the height-four site. The oriented count of this subtype is at most
\[
 2\cdot99\binom74=6,930.
\]
This bounds only the height-four subtype, not the whole norm-twenty shell. If two top fields at the same root use different quartets sharing \(k\) axes, their dot is \((k+1)\sum_{i\ {\rm shared}}\delta_i\), where \(\delta_i\) is \(+1\) for equal orientations and \(-1\) for opposite. At each shared axis the near contribution is \(2\delta_i\), and at a common two-axis far cell the contribution is \(\delta_i+\delta_j\). In particular uniformly agreeing orientations on three shared axes would give norm-sixteen difference and cannot occur when the neutral minimum is twenty.

## Related height-three rounding

At a height-three root there are six marked first-layer vertices (three of each sign) and \(m\) opposite-signed full mate pairs. The other \(6-2m\) marked vertices have a zero mate. The near projected energy is \((63-7m)/4\), leaving residual energy \((17+7m)/4\). This follows directly from the near system with \(c_x=0\), \(c_i=(21t_i+7t_{i'})/8\) on each mate pair: an opposite full pair contributes \(7/2\), and a single signed site \(21/8\).

Here \(m\ge1\) even before rounding: at the height-three root \(Ah=5\), but if \(m=0\) its six zero mates of marked neighbors would each have positive height, contributing at least six. For \(m=1\) the far projection is \(f(p,q)=-(v_p+v_q)/8\) with the seven mate-pair coefficient types
\[
 (2,-2),\ (3,1),\ (3,1),\ (-3,-1),\ (-3,-1),\ (0,0),\ (0,0).
\]
Across distinct axes the multiplicities of \(|v_p+v_q|=0,1,\ldots,6\) are \(12,24,18,20,4,4,2\). In particular the nearest-integer squared floor is
\[
 (24+18\cdot4+20\cdot9+4\cdot16+4\cdot9+2\cdot4)/64=6,
\]
exactly exhausting the residual energy. Only the last three magnitude classes can carry a nonzero nearest integer, a total of ten sites, but fourteen far sites must be marked. So \(m=1\) is also excluded. In every actual height-three rooted marking at least two of the three sign contacts on each shore are mated to the opposite sign in the rooted neighborhood.
