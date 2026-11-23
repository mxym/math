# Actual 33-sets: cycle switches, mixed residues, and the rank-11 section

Work on the no-Fano norm-18/norm-24 two-type face in one terminal anisotropic seven-plane. In the latter half the seven-rank is 42, so all actual graph labels are eligible relative to the same (terminal) original lattice. The recently proved scalar/Johnson bounds force at least 80, 76, 74, 72 actual positive-charge \(G(3,33)\) labels in the four surviving tuples. Here we use their geometry, without claiming a new tuple exclusion.

If \(b\in G(3,33)\), the equality between its cost and absolute mass forces \(b=-1_S\) for a literal 33-set \(S\). Its equation is \(A1_S=6\mathbf1-4 1_S\). Consequently \(S\) is a union of induced cycles, every outside vertex has exactly six neighbors in \(S\), and the graph induced on the 66 outside vertices is 8-regular. Put \(y=b^\circ=b+\mathbf1/3\); then \(y^2=22\).

## Cycle and pair switches

There is no length-four cycle component. Indeed, if \(X\) is such a four-site set, \(b+\sum_{i\in X}d_i+\mathbf1\) has charge \(-2\) and squared norm \(30\): \(b\cdot d_i=-1\), \(\|\sum d_i\|^2=21|X|+2|X|^2-14e(X)\), and the addition of \(\mathbf1\) folds charge seven to \(-2\). Raw \(G(2,30)\) is absent on this face. This does not force a triangle.

If \(T\subset S\) is an actual triangle, it is an entire cycle component. In the usual decomposition at \(T\), every one of its 36 wing sites \(W\) meets exactly one triangle site. The other 60 sites form \(F\), anticomplete to \(T\). The label \(D_T=\sum_{i\in T}d_i\) is \(+1\) on \(T\), \(-1\) on \(W\) and zero on \(F\). The flip
\[
-b-D_T-\mathbf1=-1_{S'},\qquad S'=T\cup (F\setminus S)
\]
is another \(G(3,33)\) label, with opposite seven-residue, and \(S\cap S'=T\). It is involutive. In particular \(F\) is split into two 30-site shores, each of within-degree two and cross-degree six. If \(C\) is an eligible actual Hoffman coclique, put \(c=-1_C\). The only \(b\cdot c=|S\cap C|\) possibilities are 5 and 12, because the angle is \(12\bmod7\) and 19 would give a charge-one norm17 by subtracting \(c\). If \(r=|T\cap C|\in\{0,1\}\), then \(|F\cap C|=10+5r\) and the two flips' intersections with \(C\) sum to \(10+7r\): either both 5 or a 5/12 pair.

For two distinct 33-sets let \(k=|S\cap S'|\). Their centered ordinary dot is \(k-11\). Both residual norms are \(22\equiv1\bmod7\); the anisotropic plane of square discriminant permits mutual residues only \(0,\pm1,\pm2\), by the determinant of the \(2\times2\) Gram. This forbids \(k=0,1,21,22\), while \(k=2\) is ruled out by \(b+b'+\mathbf1\) of charge \(-3\) and squared norm 37. Values 20,23,25,26 give the missing neutral difference norms 26,20,16,14, and larger \(k\) falls below the neutral minimum. Thus distinct overlaps are either 24 or at most 19, and at least three.

Overlap 24 occurs only for opposite seven-residues (the centered pairing has residue \(-1\)). Here their difference is exactly a genuine \(N_{18}\) label: the exclusive nine-sites of each shore are independent and each sees four across and exactly two into the shared 24-site shore. Conversely if \(t\in N_{18}\), \(|y\cdot t|=9\) gives another literal 33-set by one signed translation. The norm floor gives \(|y\cdot t|\le9\); absolute value 7 gives the missing \(G(3,37)\), and absolute value 8 gives finite Gram determinant \(18\cdot22-8^2\equiv3\), a nonsquare. In particular \(y\) is perpendicular in the ordinary graph metric to every \(N_{18}\) in the perpendicular seven-residue line. For such a \(t\), \(S\) meets its two sign supports in equal size \(k\le6\): each inside sign site needs at least two of its four opposite neighbors outside \(S\), giving \(2k\le4(9-k)\). If equality holds, the 12 selected sites in \(S\) have both \(S\)-neighbors selected, alternating signs. With no length-four component they consist of one 12-cycle or two 6-cycles.

At fixed triangle \(T\), two distinct 33-sets of the same residue containing \(T\) intersect in 12 or 19 points. Indeed a same-residue overlap is 5 modulo seven and its complementary triangle flip would turn overlap 5 into 31. Overlap 12 with one complementary flip gives a rooted \(N_{18}\) field zero on \(T\cup W\). This is impossible when \(T\) meets \(C\) and the original two sets both have the same \(C\)-intersection angle, since a flip changes it between 5 and 12, whereas \(N_{18}\) is perpendicular to \(C\).

## Coupling to actual norm-22 decompositions

For any neutral \(q\in N_{22}\), one has \(|y\cdot q|\le8\). The charge-three mass floor bounds it by 11; 9 is forbidden by \(G(3,37)\), and 10,11 give impossible mutual residues for a pair of centered norm-one-class vectors. Therefore a 33-set switch \(t\in N_{18}\) with \(|y\cdot t|=9\) cannot have an exceptional absolute-dot-seven neighbor \(u\in N_{18}\). Such a neighbor is in its perpendicular residue line, also perpendicular to \(y\), and then one of \(t\pm u\) has norm 22 and forbidden angle 9 against \(y\).

A double norm-28 difference \(d\) in the [Johnson geometry](norm22-johnson-double-graph.md) is a difference in each of two perpendicular \(N_{18}\) residue lines. It is thus perpendicular to every 33-set center whose residue lies in either corresponding line. Local angles are stronger: write an actual \(q=a_i+b_i\) with the two signed source residues perpendicular and with \(i=1,\ldots,\mu(q)\). For a \(G(3,33)\) center \(y\) in the same residue as \(q\), both \(y\cdot a_i,y\cdot b_i\) are \(-3\) or 4, by the finite residues and the absence of \(G(3,37)\). If \(y\cdot q=-6,8\), respectively they are both \(-3\) or both 4, so \(y\) annihilates all Johnson neighbors \(s_{ij}=a_i+a_j-q\). If \(y\cdot q=1\), color each \(i\) by which of \(-3,4\) occurs against \(a_i\); its dot with \(s_{ij}\) is \(-7,0,7\) according as both lower, mixed, or both higher.

For a fixed 33-set, all its switches may be oriented with \(t\)'s positive support in \(S\) and negative support off \(S\). Then they are in one signed residue because \([y]=3[t]\); their distinct mutual dot is 4 (same-class alternatives 4 and \(-3\), latter impossible without conflicts). Their flipped partners, oriented in the same seven-class as \(y\), have mutual dot 8 and dot \(-13\) against \(y\). Hence \(y\) and its partners are linearly independent: project the partners off \(y\) and their Gram has diagonal \(315/22\), off-diagonal \(7/22\). This gives degree at most \(43-\operatorname{rank} X_\perp\) for that switch star, where \(X_\perp\) is the span of the full perpendicular signed \(N_{18}\) class. No sufficiently strong lower bound on the switch incidence is currently known.

## The common zero-section has rank eleven

Put \(L=A_S\), \(B=A_{V\setminus S}\), and let \(D\) be the 33-by-66 cross-adjacency matrix. Directly from \(A^2=12I-A+2J\),
\[
DD^t=12I-L-L^2+2J,\quad LD+DB=-D+2J,
\quad B^2+D^tD=12I-B+2J.
\]
The first matrix is positive definite: \(L\) is 2-regular, with spectrum in \([-2,2]\), and \(12-\lambda-\lambda^2\ge6\) in that interval. Thus \(D\) has rank 33. On \(\operatorname{im}D^t\), \(B\) has eigenvalue 8 on the constant line and eigenvalue \(-1-\lambda\) corresponding to each of the 32 remaining eigenvalues of \(L\). Its trace on that image is \(8-32+2=-22\), since \(\operatorname{tr}L=0\) and the removed eigenvalue was 2. On \(\ker D\), which is perpendicular to constants, the third relation implies only \(3,-4\) can occur. The dimensions sum to 33 and their trace is 22; thus their multiplicities are respectively 22 and 11. Therefore the integral neutral \(-4\) fields vanishing on every site of \(S\) span an actual rank-eleven real eigenspace. In the original Euclidean mark space this is precisely the perpendicular section to the 33 independent marks on \(S\).

At prime seven, take the ambient even graph mark lattice of determinant 49, whose 7-adic span is generated by the \(u_i\). The constant mark \(m=\sum_{i\in S}u_i\) pairs by \(14/3\) on \(S\) and by \(-7/3\) off \(S\); \(m^2=154\) has valuation one. Thus \(m\) is primitive and its rank-one lattice splits off orthogonally over \(\mathbb Z_7\). Its class \(m/7\) gives the residue line of the 33-set, with quadratic value \(11/7\). On the coefficient sum-zero space on \(S\), the remaining Gram matrix is the restriction of \(3I-L\). The recurrence for a seven-radical vector on a cycle has characteristic roots of order eight: \(r+r^{-1}=3\), \(r^2+r^{-2}=0\) over \(\mathbb F_7\), so \(r^4=-1\). Hence it has dimension two exactly when that cycle length is divisible by eight and otherwise no kernel. All these radical vectors already have coordinate sum zero, since \(3I-L\) has row sum one. If no cycle length is divisible by eight, the rank-32 difference span is unimodular at seven and splits off; the rank-11 primitive zero-section then has exactly one elementary seven-discriminant line, the orthogonal complement of the marked 33-set residue in the terminal plane.

A further exact lattice datum is the unsaturated \(S\)-mark Gram determinant
\[
\det(3I-L+J/9)=\frac{14}{3}\prod_{C_\ell\subset S}
 \begin{cases}
 L_\ell^2,&\ell\ \mathrm{odd},\\
 5F_\ell^2,&\ell\ \mathrm{even},
 \end{cases}
\]
where \(L_\ell,F_\ell\) are the Lucas and Fibonacci numbers. Indeed the constant eigenvalue changes from 1 to \(14/3\); the cycle factor is \(\lambda_+^\ell+\lambda_-^\ell-2=L_{2\ell}-2\) for \(\lambda_\pm=(3\pm\sqrt5)/2\). The primitive saturation at primes other than seven is not determined by this formula; this is not a determinant assertion for the integral rank-11 residual outside seven.

[The primitive perpendicular to the whole 33-set mark](33set-det154-gluings.md) instead has rank 43 and determinant 154. Two explicit even unimodular rank-48 parents give exact harmonic equations for that mark.

## Two-gap restriction on a switched shore

At an overlap-24 switch let $P=S\setminus S'$ be the nine positive points of $t=\mathbf1_S-\mathbf1_{S'}$. These points are independent. **There are at most two length-two gaps between consecutive points of P around the cycles of S.** The same holds for the negative shore in $S'$. In particular the 24 shared sites contain at most two points of height two and at most eight zero-star roots for this switch.

Put $F=3I-A_S$ and $G=F+J/9$, the Gram of the 33 marks. Because $F\mathbf1=\mathbf1$, one has $G^{-1}=F^{-1}-J/42$. The physical vector $t/\sqrt7$ has squared norm $18/7$ and evaluates to $z=\mathbf1_P$ on these marks. Orthogonal projection therefore gives
$$
z^TF^{-1}z\le 18/7+81/42=9/2.
$$
Let $\rho=(3-\sqrt5)/2$. On a cycle of length $\ell$ the inverse kernel is
$$
(F^{-1})_{ij}=\frac{1}{\sqrt5}\sum_{m\in\mathbb Z}\rho^{|i-j+m\ell|},
$$
as follows by substituting in the three-term recurrence for $F$. On each visited cycle take the cyclic gaps between successive marked points, including the full cycle as one gap if it has just one mark. There are nine gaps of length at least two and their total is at most 33. Keep the nine diagonal zero-length terms and both directions of each arc crossing one or two consecutive gaps in the periodic kernel sum. These terms are distinct because the number of steps and the signed lifted distance determine each walk from its starting point. This remains valid when a walk makes a full turn, or two turns for the two-gap walk on a one-point cycle. Therefore
$$
\sum_{g}\rho^g+\sum_{g,g'\ \text{consecutive}}\rho^{g+g'}
\le (9\sqrt5-18)/4=:B,
$$
where the second sum counts each cyclic starting gap once.

Four gaps of length two already exceed $B$ from their one-gap terms. With precisely three, the other six have total length at most 27. The affine line through $(4,\rho^4),(5,\rho^5)$ is a lower bound on $\rho^g$ at integer $g\ge3$, with equality only at 4 and 5. Every other integer has defect at least $\rho^6-2\rho^5+\rho^4>0.0081$; decreasing the total below 27 adds at least $\rho^4-\rho^5>0.0131$. The minimum total from the one-gap terms is $M=3\rho^2+3\rho^4+3\rho^5$, with $0.00520<B-M<0.00522$. Thus the remaining six lengths must be $4,4,4,5,5,5$. If two length-two gaps are adjacent, they contribute $\rho^4$ to the two-gap sum. Otherwise the three short gaps touch six distinct consecutive windows with total length at most seven each. Either way the contribution is at least $\min(\rho^4,6\rho^7)>0.0071$, more than $B-M$. The strict comparisons can be checked with $2.2360679<\sqrt5<2.2360680$. This proves the gap bound.

The height of a shared vertex equals its number of P-neighbors within S. Each height-two vertex is the midpoint of one length-two gap. There are 18 P-to-shared contacts in all, so the zero count in the 24 shared sites is six plus the height-two count. If the switch has nine zero-star roots, at least one is outside the shared shore.

There is also a rigid equality case: if all nine gaps have length three, the full Green contribution in gap units is $9\rho^3/(1-\rho^3)=B$, so the projection saturates. The six unused sites of S are entire cycles. The vector $v=F^{-1}z$ equals $1/2$ at P, $1/4$ at other sites in the visited cycles, and zero on the unused six, by direct substitution. The vector $t/\sqrt7$ is in the S mark span with coefficients $v-(3/14)\mathbf1$. For any support-zero site outside S, evaluation at that site gives $\sum_{i\in N(x)\cap S}v_i=3/2$, since x has six S-neighbors. If its height is h and it has k neighbors in the unused six, the left side is $(6+h-k)/4$; hence $k=h$. This is an equality-case dictionary, not a switch existence assertion.

In this equality case the unused six sites are shared and are zero-star roots: on the S side they have no P contact, so by the eigen-equation they cannot have any negative support contact either. Their cycle components are thus the same in $S'$. The shared sites have no height-two points (no length-two gap on S), so the negative shore has no length-two gap either. Its nine gaps have total at most 27 after omitting those same six sites, forcing all nine lengths to equal three on that side as well. The common unused cycles are consequently either a six-cycle or two triangles. If they contain a triangle, applying the triangle-component flip to both sets gives another overlap-24 switch with the same antipodal norm-18 direction: on the far part the two memberships are both complemented. It is a different switch edge, since the flip across a triangle intersects the original set in just those three sites.
