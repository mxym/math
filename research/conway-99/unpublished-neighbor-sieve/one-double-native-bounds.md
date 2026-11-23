# Native bounds for the one-double complementary shell

Use the [complementary rank-56 convention](../complementary-rank56/README.md): \(F^+(a,t)\) counts actual integral \(+3\) affine fields \(Ab=3b+a\mathbf1\) of positive charge \(a\), mass \(9a\), cost \(t=b\cdot b\). The neutral \(N_t^+\) is oriented (each of \(b,-b\) is counted). Let \(G\) count true rook grids, \(n_1\) unordered pairs of distinct grids meeting in one vertex, and \(D_8\) unordered pairs of disjoint anticomplete cubic eight-sets. Then
\[
 F^+(2,20)\le \min\bigl(10395-90G+2n_1,\ 3465+D_8\bigr).
\]
The decomposable population is exactly \(n_1\). In particular the first bound gives an indecomposable cap \(10395-90G+n_1\); the second is already \(3465\) when the neutral complementary norm-sixteen shell vanishes.

## Literal one-double geometry and the clean-cell count

The cost excess \(20-18=2\) allows either one negative unit or one double; a lone negative needs neighbor coefficient sum \(-1\), impossible. Thus any such field is
\[
 b=2e_x+1_U+1_F,
\]
where \(U\) consists of eight neighbors of \(x\) and \(F\) of eight nonneighbors. All six zero neighbors of \(x\) see no support site other than the double. As each selected neighbor of \(x\) has its unique cap with \(x\) among selected positives (no zero neighbor of \(x\) can also touch it), \(U\) comprises four entire mate pairs, i.e. a quartet \(Q\) of the seven signed axes at \(x\). Every vertex of \(F\) sees exactly two sites in \(U\), by the common-neighbor rule with \(x\), and induces degree three in \(F\), by its coefficient equation. Each selected signed root has exactly two \(F\)-neighbors (its coefficient sum is 5, of which 2 come from \(x\) and 1 from its mate).

Consider the 24 distance-two sites with both parents on axes in \(Q\); they are the six four-site cells of this quartet. \(F\) is contained there, and anticomplete to all other sites of those cells, since a zero site with two selected parents already sees its required total 2. A simple induced cubic component cannot have order smaller than six (order four requires a forbidden \(K_4\), order five is odd). Thus \(F\), of order eight, is connected and is an entire induced component of the selected 24. Distinct fields for fixed \((x,Q)\) consequently have disjoint eight-sets.

If \(F\) meets a clean cell, its connected square is wholly in \(F\). The four remaining vertices of \(F\) cannot use either of that cell's axes, as each of those four signed parents already has two \(F\)-neighbors. They are therefore the entire opposite cell. Each of those four sites sees exactly one site of the clean square by one-domination of the clean rook grid. Their induced degree within \(F\) is three, so each has degree two within the opposite cell. Adding that cell to its two parent axes and the root gives an 18-edge nine-set, hence a rook grid by the [density equality](../../conway-99-involution/grid-density-gap/README.md). The field is exactly the sum of those two grid indicators, whose sole common site is \(x\). Conversely every unordered pair of grids sharing one vertex gives one such field with that vertex doubled; the two opposite squares are recoverable because each clean cell determines its grid and the field contains exactly those two cells outside the root neighborhood.

Independently, the cell occupancies of \(F\) satisfy equal counts on opposite cells: each axis contributes four parent incidences (two per signed site), and the four equal sums of incident edge counts in a weighted \(K_4\) give equality on opposite edges by subtraction. Therefore an indecomposable field avoids both cells of any opposite pairing containing even one clean cell. If \(b_Q\) of the three opposite pairings have at least one clean cell and \(d_Q\) have both cells clean, at most \(3-b_Q\) disjoint indecomposable eight-components fit in the remaining \(8(3-b_Q)\) sites, and there are exactly \(d_Q\) decomposable fields. In particular a selected clean star or triangle meets all three opposite pairings, so any field from such a quartet must decompose.

Summing over the 35 quartets at each root gives the count \(99\cdot105=10395\) minus the mixed opposite pairs (one clean cell and one dirty cell). A clean cell has ten opposite possible axis pairs over all quartets, so at root \(x\) the mixed count is \(10g_x-2M_2(\Gamma_x)\), with \(\Gamma_x\) the seven-axis clean graph and \(M_2\) its count of unordered disjoint edge pairs. Summing gives \(90G-2n_1\), since \(\sum_x g_x=9G\) and \(M_2\) counts the grid pairs meeting at that root alone.

For a numerical bound, use the [maximum of thirteen grids at a root](https://github.com/mxym/math/commit/8efd6ad). If \(g=|E(\Gamma_x)|\) and \(d_i\) are the seven degrees, then \(M_2=\binom g2-\sum_i\binom{d_i}{2}\). Integer convexity of the degree sum \(2g\) gives the upper sequence
\[
 (0,0,1,3,5,7,10,14,17,21,26,31,36,42)
\]
for \(g=0,\ldots,13\); each entry is at most \(42g/13\). Thus \(n_1\le378G/13\) and \(F^+(2,20)\le10395-414G/13\), in particular \(\le10395\). At rank 36 the [thirteen-grid large-wing theorem](https://github.com/mxym/math/commit/f53ab6f) supplies some incident triangle with a wing component of order at least 24 whenever \(g=13\). That triangle has at most two grids, so its axis degree is at most two. The other six degrees then give \(\sum\binom{d_i}2\ge37\) (degree two and six fours minimize), lowering \(42\) to \(41\) for \(g=13\). For \(g\le12\) the ratio is at most 3. Thus at rank 36 one may use \(n_1\le369G/13\) and \(F^+(2,20)\le10395-432G/13\).

## The cubic shadow collision cap

Two fields at the same \((x,Q)\) differ by their disjoint anticomplete cubic eight-sets \(F,F'\), making one antipodal original neutral complementary norm-sixteen line \(1_F-1_{F'}\) up to sign. Fix such an unoriented line; its two literal eight-sets are recovered from its signs. Their common shadow is
\[
 h=(A-3I)1_F=(A-3I)1_{F'}=2\mathbf1-(A-3I)(2e_x+1_U).
\]
For any actual lift write \(Z_x=N(x)\setminus U\); partition the 84 exterior sites into \(UU,UZ_x,Z_xZ_x\) by their two parents. Then \(h=2\) on \(U\cup Z_xZ_x\) (20 sites), \(h=1\) on \(UZ_x\) (48 sites), and \(h=0\) on all other sites (31 sites).

The [previous cubic-tail theorem](../complementary-rank56/tail-budget.md#the-forced-cubic-tail) gives the stronger, exact root rule: any lift root of the same shadow lies among the zero sites and must have eight height-two neighbors inducing four mate pairs. A vertex of \(Z_x\) has only four height-two neighbors, its four distance-two pair labels in \(Z_xZ_x\). A site of \(UU\) has its two selected signed parents in \(U\), nonmates, and neither can meet any of its other height-two neighbors in \(Z_xZ_x\) (those sites have both parents unselected). Thus these two parents are isolated in its height-two neighbor set, so it cannot be a lift root. Only \(x\) remains, and its quartet follows from \(U=N(x)\cap\{h=2\}\).

Consequently each eligible antipodal line charges at most **one** unordered field pair at a common root and quartet. With \(f_{xQ}\) the population at a given root and quartet, the exact count gives
\[
 \sum_{x,Q}\binom{f_{xQ}}{2}\le D_8,\qquad
 \sum_{x,Q}f_{xQ}\le99\cdot35+D_8.
\]
This is not a count of arbitrary norm-sixteen pairs: the charged supports are actual anticomplete cubic eight-sets. In fact, once a shadow is realized, every cubic eight-set with that shadow gives a field at the same \((x,Q)\): substituting it for \(F\) preserves the affine equation. It is disjoint from \(U\) (its own shadow is zero), and it cannot contain \(x\), since the resulting nonnegative mass-18 field would have a coefficient three, already ruled out.

By the published [exact plus norm-sixteen split](plus16-cross-shadow-shell.md), writing \(R=\sum_bm_b(m_b-1)\) for its original minus-four charge-one cost-37 bucket term, one has \(N_{16}^+=2D_8+2n_1+R\) and \(x_8^+=N_{16}^++2F^+(2,18)\). Thus the second bound uses \(3465+(N_{16}^+-2n_1-R)/2\), with the neutral population **oriented**. Adding twice this collision bound to the clean-cell bound cancels \(n_1\) and gives the native estimate
\[
 F^+(2,20)\le5775-30G+\frac{N_{16}^+-R}{3}
 =5775-30G+\frac{x_8^+-2F^+(2,18)-R}{3}.
\]
The factor \(3465\) is just the upper bound on occupied root-quartets. In the same argument it can be replaced by the smaller of \(3465\) and the number \(C_-(1,51)-105336\) of available cubic-tail classes, using the [earlier old-sector separation](../complementary-rank56/tail-budget.md#the-common-budget-in-the-old-sector). Also, any quartet whose clean edges form exactly a star or a triangle is empty: it has three mixed opposite pairings, thus \(b_Q=3,d_Q=0\). Such quartets can be subtracted from \(3465\) with no additional cost-layer hypothesis.

## Exact lifted coefficient and the nearby double profiles

Put \(d_i^+=(A+4I)e_i\), charge two and cost 30. A nonunit neutral cost-18 field cannot have an entry of magnitude at least three, since translating by \(d_i^+\) in the appropriate sign gives charge magnitude two and cost at most 6, below its absolute mass. Orient it with entry \(+2\) at \(i\). Then \(d_i^+-b\) has charge two, cost 20 and its unique double at \(i\). Conversely every one-double field gives a uniquely oriented \(+2\) neutral field in this way, because all other coordinates of both \(d_i^+\) and the one-double field are 0 or 1. Hence
\[
 N_{18,\mathrm{nonunit}}^+=2F^+(2,20).
\]
The factor two is orientation, not reuse of a mark.

Reusing the published [native one-double lift](../complementary-rank56/tail-budget.md#grid-injections-and-shell-arithmetic), for \(x_9^+\) the [binary glue dictionary](../complementary-rank56/README.md#2-dual-label-dictionary) gives neutral \(t=18\), charge \(|a|=1\) with \(t=15\), and \(|a|=2\) with \(t=20\), with multiplicities \(1,4,2\) respectively. Indeed write \(M=6p^2-2pq+2q^2\); the conditions are \(-p+2q\equiv a\pmod{11}\) and \(t=18-(7M-9a^2)/11\ge9|a|\). For nonnegative \(a=0,1,2\) the retained binary pairs are respectively \((0,0)\), \((-1,0),(1,1)\), \((0,1)\); neutral \((\pm2,\pm1)\) with the same sign would require neutral \(t=4\), absent. Larger charges are below absolute mass. Thus exactly
\[
 x_9^+=N_{18,\mathrm{unit}}^++4F^+(1,15)+4F^+(2,20).
\]
The last term is the actual one-double population bounded above, counted simultaneously in two parts of the rooted lattice gluing. It is not the whole coefficient: no bound on its other two terms is presumed.

Finally let \(B=F_{\ge0}^+(2,24)\). By [the nonnegative mass-eighteen classification](shared-norm-18/nonnegative-mass18.md), these are exactly the triangle plus order-twelve wing unions. For \(g_T\) actual grids through a triangle and \(c_{12}(T)\) its number of connected wing components of order twelve,
\[
 B=\sum_T\left(c_{12}(T)+\binom{g_T}2\right)=n_{3,\mathrm{grid}}+\sum_T c_{12}(T)
 \le n_{3,\mathrm{grid}}+693-3G-\tfrac12\#\{T:g_T\text{ odd}\}.
\]
Here \(n_{3,\mathrm{grid}}\) counts unordered pairs of grids meeting in a line, not disjoint triangle pairs. The binomial records two prism components, while \(c_{12}(T)\) records a single connected component. Every grid uses six wing sites at \(T\), so \(c_{12}(T)\le\lfloor(6-g_T)/2\rfloor\) and \(\sum g_T=6G\), giving the odd correction. This does not count any signed charge-two cost-24 labels.


For completeness the adjacent native coefficients can now be split by actual shape. With cost \(t=22\) and charge two, excess four allows two anomalies, each either a double or a negative unit. The nonnegative case is excluded by the mass-eighteen theorem, and a lone negative is impossible. The two negatives must be adjacent and anticomplete to the twenty positive units, since their required neighbor sum is \(-1\). In particular this shell has no +2, so the same neutral translation proves **all neutral \(N_{20}^+\) fields are unit**: a +2 would translate to this very shell with position +2, and a larger entry gives cost below absolute mass.

For cost 24, excess six allows one coefficient 3, one coefficient \(-2\), or three anomalies chosen as doubles or negative units. A lone \(-2\) would need neighbor sum \(-4\), and the nonnegative coefficient 3 is excluded. A lone negative unit cannot occur. Write \(E\) for fields with one double and two negative units (their two negatives are adjacent and anticomplete to the positive support), \(D\) for fields with three negative units, and \(B\) for the nonnegative triangle-double population above. Thus \(F^+(2,24)=B+E+D\). Every nonunit neutral cost-22 field has a \(+2\) after suitable orientation and translates to one of these \(B\) or \(E\) fields with a double at its pivot. Conversely the translation \(d_i^+-b\) at each doubled site gives a neutral cost-22 field with a unique \(+2\) and no negative doubles. For \(B\), the other two double sites are its triangle mates and translate to \(-1\); for \(E\), the two negatives miss the double and translate to \(+1\). Thus \(N_{22,\mathrm{nonunit}}^+=6B+2E\), with orientation included.

The same binary bound applied at \(x_{10}^+\) and \(x_{11}^+\) leaves the identical binary pairs, with each raw cost raised by two or four from \(x_9^+\); the neutral exceptional lifts could only have norm six/eight and vanish. At \(x_{11}^+\), \(|a|=3\) would require \(M\le3\), below the congruence possibilities \(-p+2q\equiv\pm3\); at \(x_{10}^+\), charge magnitude three would similarly need \(M=0\), which also fails the congruence. Magnitudes at least four fail the absolute mass bound at both coefficients. In particular
\[
 x_{11}^+ =N_{22,\mathrm{unit}}^+ +4F^+(1,19)+8B+4E+2D.
\]
Only \(B\) is bounded by the triangle-component expression here. No signed contribution was silently replaced by a nonnegative population.