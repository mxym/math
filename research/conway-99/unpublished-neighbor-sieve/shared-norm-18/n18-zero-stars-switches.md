# Zero-star induced subgraphs and exact 33-set switches

Let \(t=1_P-1_N\) be an actual oriented integral norm-18 field in a hypothetical Conway graph, with the independent nine-sites \(P,N\) inducing degree four across. Let \(h(x)\) for an exterior site be its equal number of neighbors in \(P,N\), and let \(Z=\{x:h(x)=0\}\) be the zero-stars. Use the [height census](height-three.md): there are either nine zeros and no height three, or eight zeros and one height-three site. In the latter case the height-three site has exactly five zero neighbors. An assertion below explicitly using absence of \(G(3,37)\), the two-type residue circle, or the Hoffman coclique is conditional on that face; other statements work in any rank.

Write \(U_X=\sum_{i\in X}u_i\) for the true physical graph marks, and \(D_X=(3I-A)1_X\). Write \(t^\sharp\) for the physical vector whose mark evaluations are \(t_i\), with squared length \(18/7\). Its equivalent centered coordinate model is the ordinary graph vector \(t/\sqrt7\).

## One norm calculation for each subset of the zero-stars

For \(R\subseteq Z\), set \(r=|R|\) and \(e=e(R)\). The marked vector
\[
v_R=U_P-U_R-4t^\sharp
\]
has ordinary physical squared norm \(36/7+r+r^2/9-2e\). Indeed \(U_P^2=36\) by independence, \(U_P\cdot U_R=r\) because the two sets are anticomplete, \(U_R^2=3r+r^2/9-2e\), and \(U_P\cdot t^\sharp=9,\ U_R\cdot t^\sharp=0\). Its evaluations have integer part \(D_P-D_R-4t\) and uniform offset \((9-r)/9\). Folding by integers gives the charge representative \(a\equiv-r\pmod9\), \(-4\le a\le4\); the raw integer cost is \(7v_R^2+11a^2/9\). In particular:
\[
\begin{array}{c|rrrrrr}
 r&3&4&5&6&7&8\\
 a&-3&-4&4&3&2&1\\
 \text{raw cost}&75-14e&96-14e&110-14e&117-14e&128-14e&143-14e .
\end{array}
\]
The mass floors imply \(e(R)\le3,4,6\) at \(r=4,5,6\), respectively. Thus the whole graph induced on \(Z\) contains neither a four-cycle nor a five-cycle. Below we prove the exact stronger bounds \(e(R)\le6,7\) at \(r=7,8\), unconditionally by pair counting.

For the nine-zero case \(e(Z)\le9\), and equality has a useful vector meaning. (Below the eight-zero case has the sharper bound \(e(Z)\le7\).) In fact the evaluations of \(U_P+U_N\) are 1 on the 18 support sites and \(2-2h\) outside. The height census gives squared physical norm 18 in either case. Its pairing with \(U_Z\) is \(2|Z|\). Therefore
\[
3|Z|+|Z|^2/9-2 e(Z)=U_Z^2\ge(2|Z|)^2/18.
\]
At \(|Z|=9,\ e(Z)=9\) equality holds and \(U_Z=U_P+U_N\). Evaluating on \(Z\) gives \(4-\deg_{G[Z]}=2\), so \(G[Z]\) is 2-regular.

## Zero-star triangles give canonical true switches

If \(R=T\) is a triangle in \(Z\), the cost is 33 and the charge \(-3\), so the integer field
\[
1+D_P-D_T-4t
\]
is all nonnegative units. It has value one on \(N\), zero on \(P\) and \(T\). At an exterior point not in \(T\) it has value \(1-h+\#(N(x)\cap T)\); at most one site of a triangle can neighbor an exterior point. Thus there is no height-three site, every height-two site sees one point of \(T\), and \(T\) is anticomplete to the other zero-stars (otherwise an entry would be at least two). Put \(H_T=\{x:h(x)=1,\ x\text{ sees }T\}\). The all-nonnegative support is \(N\cup(Z\setminus T)\cup H_T\); by complementation of the signs of \(t\) there is the other support \(P\cup(Z\setminus T)\cup H_T\). Both are genuine 33-sets, so \(|H_T|=18\); they intersect in 24 sites. This recovers the previously known [triangle-residual construction](../triangle-wing-short-field.md#what-happens-at-the-first-possible-norm) and gives the exact canonical support dictionary.

Distinct zero-star triangles are isolated and give distinct canonical switches, since the triangle is exactly the omitted zero-stars. Conversely, any switch of this \(t\) for which the shared 24-set omits a zero-star triangle and has no height-two site is this canonical switch: the shared shore must consist of the other six zeros and eighteen height-one points; the three outside triangle vertices each see six shared sites, and no vertex outside a triangle can see two of its sites. Hence its eighteen height-one points are exactly \(H_T\).

On the two-type face a \(t\) with any zero-star triangle cannot have an absolute-dot-seven \(N_{18}\) partner. Its canonical switch supplies an actual 33-set at signed angle 9. The partner residue would be perpendicular to the switch residue line and hence perpendicular to that 33-set in the ordinary metric; adding/subtracting it gives an actual \(N_{22}\) at forbidden angle 9 against the 33-set, as in the [mixed Johnson geometry](33set-rank11-and-switches.md#coupling-to-actual-norm-22-decompositions).

## Exact classification of all-gap-three switches

A switch has all gaps three if, in each cycle of a 33-set meeting the selected \(P\), consecutive selected sites are three steps apart. Such switches of a fixed oriented \(t\) are in **bijection with induced 2-regular six-subsets \(R\subseteq Z\)**. No enumeration of graphs is involved.

Forwards, take any six zero-stars inducing six edges. The cost of \(v_R\) is 33 and charge \(+3\), so the raw field \(b=D_P-D_R-4t\) is all nonpositive units. At each site of \(R\), \(b=\deg_R-3\), forcing \(\deg_R\ge2\), and its average is two. Thus \(R\) is 2-regular (one six-cycle or two triangles) and is contained in its 33-set \(S\). Every other zero-star has \(b=\#(N(x)\cap R)\), so it is outside \(S\) and has no edge to \(R\). The \(P\) sites are in \(S\), the \(N\) sites outside. Adding \(t\) replaces \(P\) by \(N\) and gives the other 33-set: \(v_R\cdot t^\sharp=-9/7\), so its centered cost stays the same. Both 33-sets contain \(R\) as complete cycle components. Each shared site outside \(R\) has precisely height one, because there are no \(R\)-edges to the rest of \(S\), and \(b=r_R-h=-1\) there. Thus the remaining cycle sites are marked every third along each active cycle. This applies on both shores.

Conversely suppose one shore \(S\) has all nine gaps three. Its active cycles have total length 27; the other six sites \(R\) comprise entire cycles. On the 33 marks of \(S\), put \(F=3I-A_S\), \(G=F+J/9\), \(z=1_P\). Then \(G^{-1}=F^{-1}-J/42\). Directly \(F^{-1}z\) equals \(1/2\) on \(P\), \(1/4\) on the rest of the active cycles, and zero on \(R\), as verified in the cycle recurrence. In particular \(z^tG^{-1}z=9/2-81/42=18/7\), the full norm of \(t^\sharp\). Therefore \(t^\sharp\) belongs to the span of the \(S\)-marks with coefficients \(G^{-1}z\). Rearranging them gives
\[
-\frac{U_S}{7}=U_P-U_R-4t^\sharp.
\]
In a 33-set switch the unused sites \(R\) have no \(P\)-contacts, hence no \(N\)-contacts either (the equal exterior heights), so \(R\subseteq Z\). This recovers the same construction and proves uniqueness for the fixed \(t,R\).

It follows that the number for fixed \(t\) is at most one except when \(G[Z]\) is exactly three disjoint triangles; then it is exactly three. Indeed each eligible \(R\) is a union of isolated cycle components in \(G[Z]\), and with at most nine zero-stars the only way to have two distinct such 6-subsets is to choose pairs from three disjoint triangles. When \(|Z|=8\) and an all-gap-three switch occurs, \(R\) must be one six-cycle: the actual height-three vertex has three shared-shore neighbors, all zero-stars, and it cannot meet two disjoint triangles in three sites.

For the last assertion, and more generally, in any switch let \(d_2\) be the number of height-two sites on the shared 24-set. It equals the number of gaps two on either shore. Exactly \(6+d_2\) zero-stars belong to the shared shore, since its heights sum to 18. A height-three vertex lies outside both 33-sets and sees exactly three sites on the shared shore. If it exists, there are only eight zero-stars total, so the height-three vertex can see at most \(3+(8-6-d_2)=5-d_2\) of them. It needs five, hence \(d_2=0\). Its exactly three shared neighbors and both omitted zero-stars are then all zero-stars.

## Actual Hoffman incidences

On the unique-coclique two-type face put \(c=-1_C\) and \(\kappa=|P\cap C|=|N\cap C|\). The canonical triangle switch from omitted \(T\) has raw angle \(\delta=7(\kappa-|T\cap C|)-2\). The all-gap-three switch from retained \(R\) has \(\delta=12+7(|R\cap C|-\kappa)\). For example the latter follows by pairing \(U_P-U_R-4t^\sharp\) with the physical \(c\)-mark (whose evaluations are \(c_i+2/9\)); add the centering correction \(22/3\) to seven times this pairing. The former follows identically after negating the physical field of charge \(-3\). Both angles must be in \(\{5,12\}\).

In the triple-triangle case \(e(Z)=9\), so \(U_Z=U_P+U_N\). Pairing this equality with the actual \(c\)-mark gives exactly \(|Z\cap C|=2\kappa-2\). The three triangles can meet \(C\) in at most three points, so \(\kappa\le2\); if \(\kappa=2\), exactly two of the three triangles meet \(C\), and if \(\kappa=1\), none do.


## Universal pair proof of stronger large-subset caps and the zero-star graph types

For any \(R\subseteq Z\) with \(r\) vertices and \(e\) induced edges, write \(w=\sum_{z\in R}\binom{\deg_R(z)}2\). The available common-neighbor incidences for pairs in \(R\) witnessed outside \(R\) are exactly
\[
2\binom r2-e-w,\qquad w\ge 2e-r.
\]
The edge term is one fewer common neighbor for an adjacent pair; the wedge term subtracts all witnesses inside \(R\). The wedge inequality is \(\binom{k}{2}\ge k-1\) summed over \(R\).

For each zero-star \(z\), the sum of the exterior neighbor heights is 18 and all 14 neighbors are exterior. Thus its number of height-two neighbors is
\[
4+\deg_Z(z)-2\,\mathbf1_{\{z\sim x_3\}},
\]
where \(x_3\) denotes the unique height-three vertex if present and the indicator is zero otherwise. Consequently the number of \(R\)-to-height-two incidences is at least \(4r+2e-2m\), with \(m=|R\cap N(x_3)|\) or zero if there is no \(x_3\). Height-two vertices number 18 or 15 respectively, and \(x_3\) itself contributes \(\binom m2\) pair witnesses. For \(s\) incidences among \(k\) integer contact numbers, the pair sum is at least \(2s-3k\) by \(\binom{a}{2}\ge2a-3\); similarly it is at least \(s-k\).

For \(r=7,e\ge7\) the pair capacity is at most 28. With no \(x_3\), at least 42 incidences among 18 height-two sites require at least \(84-54=30\) pairs. If \(x_3\) exists, \(m\) is 4 or 5 since there are eight zeros and \(x_3\) sees five. Then at least 34 or 32 incidences among 15, together with \(\binom m2\), require \(68-45+6=29\) or \(64-45+10=29\) pairs. This contradiction is **unconditional**: any seven zero-stars have at most six edges, without an affine-shell hypothesis.

For \(r=8,e\ge8\) the pair capacity is at most 40. Without \(x_3\), at least 48 incidences among 18 require at least 42 pairs. With \(x_3\), \(R=Z\), \(m=5\), at least 38 incidences among 15 require 31 pairs, plus ten from \(x_3\). This also is unconditional: **any eight zero-stars have at most seven edges**.

If \(r=6,e=6\) the capacity is at most 18. Without \(x_3\), the height-two incidence bound is 36 and these 18 sites already need at least 18 pair witnesses. With \(x_3\), \(m\in\{3,4,5\}\), use \(\binom{a}{2}\ge a-1\) for the 15 height-two sites: the pair floors including \(x_3\) are 18, 19, 21 respectively. In either case all inequalities are equalities: \(R\) is 2-regular, no zero-star outside \(R\) attaches to it, every height-two site has exactly two \(R\)-neighbors, and if \(x_3\) exists then \(m=3\). This gives an independent direct graph proof of the isolation assertion in the switch theorem.

It follows that \(G[Z]\) is a disjoint union of trees and isolated cycles of lengths 3, 6 or 9. Triangles are isolated by the canonical triangle calculation. Four and five cycles are excluded by the earlier size-four/five caps, and seven/eight cycles by the unconditional caps just proved. A six-cycle is isolated by the equality argument; a nine-cycle exhausts \(Z\), with no additional edge since \(e(Z)\le9\). This exhausts all possible cycle lengths and excludes every component containing more than one cycle. With a height-three site there are no triangular components and at most one isolated six-cycle, otherwise only trees.
