# Two sharp restricted cases of complex Littlewood's \(4/3\) inequality

Write
\[
 B(A)=\sup_{|x_j|,|y_i|\leq 1}\left|\sum_{ij} a_{ij} y_i x_j\right|,\qquad
 L(A)=\left(\sum_{ij}|a_{ij}|^{4/3}\right)^{3/4}
\]
for a finite complex matrix \(A\). This note proves \(L(A)\leq B(A)\) under either of two conditions:

1. The phases can be put in a common closed sector of width \(\pi/2\) by multiplying rows and columns by unit scalars. The note gives an exact cycle test and structural examples. In particular, every choice of complex coefficients works for arbitrary bipartite cactus support, and for a wider support class including all one-subdivisions of 2-degenerate graphs.
2. There are at most two active rows, with **arbitrary complex entries and any number of columns**. The same holds by transpose for two active columns. This includes matrices that provably do not satisfy condition 1. The proof combines an exact planar polygon inequality with a one-variable convexity estimate for ellipse support functions.

Among nonzero matrices in either class, equality holds only for a one-entry matrix, or a full \(2\times 2\) matrix on the active rows and columns whose four moduli are equal and whose alternating cycle phase is \(\pi\). These are precisely the active matrices gauge-equivalent to a scalar entry or a scaled \(2\times2\) Hadamard matrix. The constant 1 is sharp. For a particular nonempty support pattern on which the statement holds for all coefficients, its allowed matrices with exactly that pattern still have supremal ratio 1 by tending to a one-entry matrix (though the supremum need not be attained).

## 1. Acute phases and exact equality

Put \(\rho_i=(\sum_j|a_{ij}|^2)^{1/2}\) and \(\kappa_j=(\sum_i|a_{ij}|^2)^{1/2}\), omitting zero rows and columns. Let \(E=\{ij:a_{ij}\ne0\}\). Hölder's inequality gives
\[
 \sum_{ij}|a_{ij}|^{4/3}
 =\sum_{ij\in E}\left(\frac{|a_{ij}|^2}{\rho_i}\frac{|a_{ij}|^2}{\kappa_j}\rho_i\kappa_j\right)^{1/3}
 \le \left[(\sum_i\rho_i)(\sum_j\kappa_j)\sum_{ij\in E}\rho_i\kappa_j\right]^{1/3}
 \le [(\sum_i\rho_i)(\sum_j\kappa_j)]^{2/3}.
\]
Thus \(L(A)\le[(\sum_i\rho_i)(\sum_j\kappa_j)]^{1/2}\). If the transformed matrix has all arguments in \([-\pi/4,\pi/4]\), all pairwise inner products of the numbers within each row or column are nonnegative as real 2D vectors. Consequently the absolute value of the sum of any row or column is at least its Euclidean norm. Maximizing row phases with the column phases held fixed shows \(B\ge\sum_i\rho_i\), and the transpose argument shows \(B\ge\sum_j\kappa_j\), giving the result. A common original sector not centered at zero is harmless because a global scalar phase is another gauge.

If \(L=B\ne0\), both sums of Euclidean norms equal \(B\). Every pair of nonzero entries in a row or column of the transformed matrix must have zero inner product. Three phases in \([-\pi/4,\pi/4]\) cannot be pairwise \(\pi/2\) apart. Equality in the final Hölder bound also demands complete support on the active rows and columns, since \(\rho_i\kappa_j>0\) for all their pairs. Hence the only remaining dimensions are \(1\times1\), \(1\times2\), \(2\times1\), or \(2\times2\). A nontrivial single row or column has \(B=\ell_1>\ell_{4/3}\). In the full \(2\times2\) case, equality in Hölder requires the three positive arrays \(|a_{ij}|^2/\rho_i,|a_{ij}|^2/\kappa_j,\rho_i\kappa_j\) to be pairwise proportional. Comparing the first two forces the \(\rho_i\) constant across rows and \(\kappa_j\) constant across columns; comparing with the last forces equal moduli. Orthogonality then gives the checkerboard phases \(\pm\pi/4\) and alternating cycle phase \(\pi\) modulo \(2\pi\). Conversely the scaled standard Hadamard has \(B=\max_{|t|=1} (|1+t|+|1-t|)=2\sqrt2\) times the entry modulus, by Cauchy–Schwarz and \(t=i\). It admits the required checkerboard gauge.

## 2. Cycle test, support classes and exact barrier

Orient every support edge from its row vertex to its column vertex. Row and column phase multiplication adds an arbitrary vertex potential difference to each edge argument, because the row and column phase choices are independent and one signed convention can be negated. Choose a spanning forest and let \(F\) be its fundamental cycle matrix, with the chord columns equal to the identity. Write \(r=|E|-|V|+\#\text{components}\) and \(h=F\theta\bmod 2\pi\), with \(\theta\) the edge arguments. The following is an exact certificate for the existence of a gauge with all edge angles in \([-\alpha,\alpha]\):
\[
 \exists k\in\mathbb Z^r:\quad
 |u_C\cdot(h+2\pi k)|\le \alpha |C|\quad
 \text{for every simple oriented cycle }C.
\]
The vector \(u_C\in\{-1,0,1\}^r\) records the signed chord coordinates of \(C\) in the basis. The cycle inequalities are necessary by summing edge angles. For sufficiency take a real edge lift with tree coordinates zero and chord coordinates \(h+2\pi k\). Regard each edge in both directions and impose the two constraints that adding a vertex-potential difference puts its real lift in \([-\alpha,\alpha]\). The ordinary difference-constraint criterion is that the directed constraint graph has no negative cycle, equivalent to the displayed inequalities on oriented simple cycles. A two-step directed backtrack has nonnegative length \(2\alpha\); every other elementary directed cycle is a simple cycle of the graph, and any closed walk decomposes into these. The difference-constraint criterion follows by adding a zero-weight super-source and taking shortest-path distances when there is no negative cycle. The resulting edge lift has the same cycle holonomies as the original, so is genuinely gauge-equivalent mod \(2\pi\): integrating their difference along the spanning forest makes it vanish, and fundamental cycles then force it to vanish on chords. The search over \(k\) is finite because the inequality on an individual fundamental cycle bounds \(|h_i+2\pi k_i|\). Equivalently the cographic cycle-offset zonotope \(F[-\alpha,\alpha]^E\) contains a representative of \(h\) modulo \(2\pi\mathbb Z^r\).

For a bipartite cactus, simple cycles are edge-disjoint, each with length ≥4. Allocate each cycle's principal total phase evenly among its edges in the oriented signs and set all bridge phases to zero. Then every edge has magnitude of argument at most \(\pi/4\) and all cycle holonomies match. No assumption on the magnitudes was used.

For a broader sufficient class, form the support graph by replacing each edge \(e\) of a base multigraph by a path of length \(\ell_e\), with distinct internal vertices, requiring that the resulting support graph is simple bipartite. Suppose the base vertices can be ordered so that at each vertex the sum, over paths to earlier vertices, of their excluded angular arc lengths
\[
 \sum_{e\ \mathrm{earlier}}\max(0,2\pi-2\ell_e\alpha)
\]
is at most \(2\pi\). Assign the phases greedily to base vertices in this order. A path \(e\) from an already assigned vertex imposes a closed arc of allowed phases at its new endpoint: its principal residual path phase must have magnitude at most \(\ell_e\alpha\), and this restriction is vacuous if \(\ell_e\alpha\ge\pi\). The complement is an open arc of the displayed length. A finite union of such open arcs of total length at most \(2\pi\) cannot cover the circle. For equality in the sum this follows because any cover by at least two of these nonempty proper open arcs must entail a positive-length overlap (a circle is connected); a single proper open arc cannot cover. After choosing all base phases, distribute the residual path phase evenly along each path; choose internal potentials by integration. Components glued at a single vertex preserve this construction, because adding a common constant to a component's potentials does not change edge phases.

In particular \(\alpha=\pi/4\) works for any once-subdivided 2-degenerate graph (each path length 2, at most two earlier neighbors), e.g. the one-subdivision of \(K_{2,3}\), which has overlapping cycles. The same works for subdivisions of any graph with every path length at least 4 when the subdivision is bipartite. Strict noncactus examples include theta graphs with three lengths \(3,3,3\) or \(2,2,4\).

For a block consisting of internally disjoint parallel paths of lengths \(\ell_i\) between two vertices, the least universally sufficient half-width \(\alpha\) is exactly the least satisfying \(\sum_i\max(0,2\pi-2\ell_i\alpha)\le2\pi\). The sufficiency was just proved; if the sum exceeds \(2\pi\), position the excluded open arcs to cover the circle. To see this directly, shrink the positive lengths by a common factor to sum \(2\pi\), tile the circle by their closed subarcs, and use the original open arcs with the same midpoints; each closed subarc is then contained in its larger open arc. Independent offsets are obtained from freely choosing edge arguments on the internally disjoint paths. This gives sharp \(\alpha=2\pi/9\) for lengths \(3,3,3\), \(\pi/4\) for \(2,2,4\), and \((\pi/2)(1-1/k)\) for \(K_{2,k}\). In particular \(K_{2,3}\) with a pair of unit coefficients per column and relative phases \(0,\pm 2\pi/3\) cannot be put into the acute gauge (needs half-width \(\pi/3\)). This is an obstruction to the gauge, not to Littlewood's inequality itself.

More generally a necessary condition for a graph to permit acute gauges for every choice of coefficients is \(\tau(G)\ge 4^r\), where \(\tau\) counts choices of spanning trees in all components. Indeed the cographic zonotope \(F[-\alpha,\alpha]^E\) has Euclidean volume \((2\alpha)^r\tau(G)\). Its maximal minors are 0 or \(\pm1\), nonzero precisely when the complement of the chosen \(r\) columns is a spanning forest: cutting coordinates of a real cycle flow restricts to that chosen set and is invertible exactly if the remaining edges have no cycles; in the forest case the replacement fundamental cycle basis gives an integer inverse. The zonotope volume formula sums the absolute maximal minors. If its image modulo \(2\pi\mathbb Z^r\) covers the torus, the volume is at least \((2\pi)^r\), giving the claim when \(\alpha=\pi/4\). This bound is necessary, not asserted sufficient.

## 3. Balanced two-row matrices (arbitrary phases and weights)

For a \(2\times n\) matrix with \(|a_{1j}|=|a_{2j}|=w_j\), choose the common relative phase variable between the rows as \(e^{2it}\). Maximizing the column phases for fixed row phases gives
\[
 B(A)=2\max_t\sum_j w_j|\cos(t+\phi_j/2)| = 2R,
\]
where \(\phi_j\) are the relative column phases and \(R\) is the circumradius about zero of the planar zonotope \(\sum_j[-w_jv_j,w_jv_j]\), with \(v_j\) the planar unit vector of argument \(\phi_j/2\). This uses that the sum of absolute cosines is the support function of this zonotope, and the maximum support function is its circumradius. Coefficients of modulus zero are omitted. Merge parallel generators, which preserves the zonotope and weakly increases the sum of weights to the power \(4/3\), strictly if more than one nonzero generator lies in a group. The resulting positive generator weights are precisely half the side lengths, with one side from each antipodal pair, of the convex zone polygon. This is immediate from the exposed face in a direction perpendicular to a generator: only its sign is undetermined, and all other segment endpoints are fixed. If the zonotope is a segment, the desired sharp inequality below is immediate since \(\sum_j w_j^p\le(\sum_j w_j)^p=R^p<2^{1/3}R^p\) for \(p=4/3\) and \(R>0\).

We prove that any centrally symmetric convex polygon in the closed unit disk has
\[
 \sum_{\text{one side from each opposite pair}}(\mathrm{side}/2)^{4/3}\le2^{1/3},
\]
with equality only for the square inscribed in the disk (among nondegenerate polygons). For rigor fix an upper bound \(2n\) on the number of vertices. Over a maximizing sequence of polygons there is a subsequence with constant even vertex count and convergent cyclically listed vertices, after choosing labels \(v_{j+n'}=-v_j\) if they have \(2n'\) vertices. A nondegenerate limit is a symmetric convex polygon with a weakly ordered boundary list. Removing repeated vertices changes no edge-power sum; merging collinear consecutive sides increases it strictly when both lengths are positive, using \(p>1\). Convexity and the consistent orientation pass continuously to the limit by the supporting-line inequalities for all ordered edges; for a nondegenerate limit, the cyclic boundary lists pass in order too, as seen by the nondecreasing lifted polar angles (the origin is interior in all nondegenerate symmetric polygons). If the limit collapses to a segment, the limiting half-perimeter is at most 2, so the half-side power sum is at most 1: the total perimeter of a polygon contained in the unit disk and converging to a segment is at most 4 in the limit, e.g. by the Cauchy perimeter formula (equivalently, projections onto the line of the limit segment have monotone chains on the two arcs joining a minimum to a maximum projection). For a direct estimate via the monotone chains, the total absolute horizontal projection increments equal twice the horizontal range; vertical increments ≤ twice the vertical range by convexity. Thus the perimeter is at most twice the sum of these ranges, which tends to at most 4. Since the square provides value \(2^{1/3}>1\) whenever \(n\ge2\), a nondegenerate maximizer exists after removing degeneracies. (For \(n=1\) only the segment case is needed.)

A strictly convex polygon means here a convex polygon whose vertices all have interior angle less than \(\pi\), as after pruning collinear boundary vertices. If a vertex lies strictly inside the disk, its antipode does also. Displace the two by \(\pm\varepsilon h\) respectively, and also consider the opposite displacement. When \(\varepsilon\) is sufficiently small, both perturbed polygons remain convex, centrally symmetric, in the disk, and retain the same cyclic vertex order: the finitely many strict inequalities putting each nonincident vertex on the interior side of every edge are open. The full edge-power sum is strictly convex along this perturbation, because a displacement changes at least one edge vector and \(u\mapsto|u|^p\) is strictly convex on \(\mathbb R^2\). Its original value cannot be maximal. Hence every extremal vertex is on the circle.

On a cyclic symmetric polygon the central half-angles \(x_i\) corresponding to one side from each antipodal pair sum to \(\pi/2\), and the normalized half-side lengths are \(\sin x_i\). Let \(f(x)=\sin^{4/3}x\). For \(x+y=s\), \(x\le y\), the sign of \(f'(x)-f'(y)\) equals that of the difference of their nonnegative cubes. Since \((f'(x)/(4/3))^3=\sin x\cos^3x=(\sin2x)/4+(\sin4x)/8\), that sign is the sign of
\[
 \sin(x-y)[\cos s+\cos(2s)\cos(x-y)].
\]
If \(s\le\pi/3\), the bracket is nonnegative: this is immediate for \(\cos(2s)\ge0\), and otherwise it is bounded below by \(\cos s+\cos 2s\ge0\). It is strictly positive when \(0<x<y\) in this range. Thus \(f(x)+f(y)\) decreases as \(x\) increases from \(0\) to \(s/2\), strictly on its interior if \(s>0\). Whenever at least three positive angles remain, the two smallest sum to at most \(\pi/3\) (at most twice the average) and can be merged with a strict increase. With two positive angles totaling \(\pi/2\), the bracket is \(-\cos(x-y)<0\), so the sum increases strictly toward \(x=y=\pi/4\). The optimum is \(2\sin^{4/3}(\pi/4)=2^{1/3}\). This proves the polygon claim and its equality form.

Scaling to radius \(R\) now gives \(\sum_j w_j^{4/3}\le 2^{1/3}R^{4/3}\). Hence
\[
 L(A)=(2\sum_j w_j^{4/3})^{3/4}\le2R=B(A).
\]
Equality is restricted by the two steps: no merge of nonzero parallel generators, and precisely the two nonzero perpendicular equal generators of a square. Perpendicularity of their half phase differences says the two relative phases differ by \(\pi\bmod 2\pi\). Conversely the full equal-modulus \(2\times2\) Hadamard gauge achieves equality. This also proves the inequality for the obstructed phase example on \(K_{2,3}\) above, though not by the acute angular argument.

## 4. Full two-row theorem: supporting ellipses by a disk-plus-segment lower bound

For a two-row matrix, put \(a_j=|a_{1j}|\), \(b_j=|a_{2j}|\), \(s_j=a_j+b_j\), and \(d_j=|a_j-b_j|\), and discard columns with \(s_j=0\). Use the same angles \(t,\phi_j\) as in §3; if one entry vanishes its relative phase can be arbitrary. For fixed row phases, optimizing the column phases shows
\[
 B(A)=\max_t\sum_j\sqrt{d_j^2+(s_j^2-d_j^2)\cos^2(t+\phi_j/2)}.
\]
Each term is the support function of a rotated centered ellipse of major and minor semiaxes \(s_j,d_j\). Define
\[
 B_j=d_j^2/s_j,\quad A_j=s_j-B_j,\quad k=2^{-1/4},\quad p=4/3.
\]
Here \(A_j,B_j\) are nonnegative scalar contributions, not the matrix or its norm. The map \(c\mapsto\sqrt{d_j^2+(s_j^2-d_j^2)c^2}\), \(0\le c\le1\), is convex. Its tangent at \(c=1\) is \(B_j+A_jc\), giving a uniform lower bound by the support function of a disk of radius \(B_j\) plus a segment of half-length \(A_j\). The sharp polygon estimate in §3 applied to the zonotope from these segments implies
\[
 B(A)\ \ge\ \sum_j B_j + \max_t\sum_j A_j|\cos(t+\phi_j/2)|
 \ \ge\ \sum_j B_j+k\left(\sum_j A_j^p\right)^{1/p}.
\tag{1}
\]
For a pure degenerate ellipse (\(d_j=0\)) or a disk (\(d_j=s_j\)) the tangent identity is exact.

The pointwise coefficient estimate needed to match (1) is
\[
 (a_j^p+b_j^p)^{1/p}\ \le\ B_j+kA_j,
\tag{2}
\]
strict whenever \(0<d_j<s_j\). To prove this, put \(z=(d_j/s_j)^2\in[0,1]\) and
\[
 h(z)=\frac{(1+\sqrt z)^{4/3}+(1-\sqrt z)^{4/3}}{2}.
\]
The left side of (2) is \(s_jk h(z)^{3/4}\), and the right side is \(s_j[k+(1-k)z]\). Thus the estimate is the secant bound for \(g=h^{3/4}\) between \(z=0\) and \(z=1\), at which \(g\) equals \(1\) and \(2^{1/4}\), respectively. Its strict convexity on the open unit interval follows from a short coefficient argument. The even-binomial power series of \(h\) has every coefficient nonnegative, and its first four coefficients are \(1,2/9,5/243,44/6561\). Consequently \(h\ge1\), \(h'\) is convex, and
\[
 h'(0)=2/9,\qquad h'(1-)=2^{1/3}/3<4/9.
\]
Indeed differentiating the defining expression gives \(h'(z)=\frac{(1+\sqrt z)^{1/3}-(1-\sqrt z)^{1/3}}{3\sqrt z}\). By the convexity of \(h'\) and its finite endpoint limits, \(0\le h'(z)\le (2/9)(1+z)\). Hence \((h')^2/4\le (1+3z)/81\), using \(z^2\le z\). On the other hand,
\[
 h''(z)\ \ge\ 10/243+(264/6561)z\ >\ (1+3z)/81.
\]
Thus \(hh''-(h')^2/4>0\) and
\(
 g''=(3/4)h^{-5/4}\big(hh''-(h')^2/4\big)>0
\)
on \((0,1)\). Since \(g\) is continuous at both endpoints, this proves (2) with its strictness assertion.

Finally take the \(\ell_p\) norm over columns and use Minkowski followed by the \(\ell_p\)-to-\(\ell_1\) inequality on nonnegative \(B_j\):
\[
 L(A)\le\|(B_j+kA_j)_j\|_p\le\|(B_j)_j\|_p+k\|(A_j)_j\|_p
 \le\sum_jB_j+k\|(A_j)_j\|_p\le B(A).
\]
For equality, (2) requires each nonzero column to be balanced (\(B_j=0\)) or a singleton (\(A_j=0\)); the two types have disjoint supports in these scalar sequences. If both types occur, the \(\ell_p\) triangle inequality is strict, because neither nonzero sequence is proportional to the other. If only singleton columns occur, \(\ell_p=\ell_1\) is possible only for one nonzero coefficient. If only balanced columns occur, §3 gives exactly the equal-modulus nonzero \(2\times2\) Hadamard case. Thus the equality statement is complete.

For every \(2\times n\) complex matrix and every coefficient exponent \(q\ge4/3\), it follows that \(\|(|a_{ij}|)_{ij}\|_q\le B(A)\) with sharp constant 1, by monotonicity of finite sequence norms and the one-entry test. At \(q>4/3\) the sequence inequality is strict when more than one coefficient is nonzero, so only the one-entry case remains.

## 5. Attribution and scope

The unrestricted complex optimum is not determined. The classical upper bound \(2/\sqrt\pi\), and an explicit statement that it is not proved optimal, are in Núñez-Alarcón, Pellegrino and Seoane-Sepúlveda, [On the Bohnenblust-Hille inequality and a variant of Littlewood's \(4/3\) inequality](https://arxiv.org/abs/1203.3043), §§1 and 3.2. The distinction between exact mixed Littlewood bounds and the unmixed \(4/3\) inequality matters: Cavalcante, Núñez-Alarcón, Pellegrino and Rueda, [Optimal constants of the mixed Littlewood inequalities: the complex case](https://files.ele-math.com/articles/mia-25-13.pdf), settle relevant mixed constants, not the unrestricted unmixed constant. The 2024 primary paper [The sharp constants in the real anisotropic Littlewood's \(4/3\) inequality and applications](https://arxiv.org/abs/2407.06804) still distinguishes unresolved complex sharp constants. No direct closure or identical restricted theorem surfaced in the primary-source searches; this is not an exhaustive priority assertion. The analytic point here is the exact support/gauge transfer and the separate chord-power argument, not the usual mixed-norm inequality or the known cographic-zonotope setup. For the latter compare [The Tropical and Zonotopal Geometry of Periodic Timetables](https://doi.org/10.1007/s00454-024-00686-2), §§4.2–4.3 (cycle-offset zonotope, network matrix minors, torus geometry).

The full two-row theorem comes from the planar support-function reduction. It does not extend by the displayed argument to three independent row phases, where there is no single planar angle parametrizing all column costs.

## 6. Arbitrarily many rows with two nonzero entries per column

**Theorem.** Let \(A=(a_{ij})\) be any finite complex matrix with at most two nonzero entries in each column. With the same \(p=4/3\) and norms \(B(A),L(A)\) as above, \(L(A)\le B(A)\) with best constant 1. Transposition gives the corresponding row-sparse theorem. Apart from the zero matrix, equality again consists of a singleton or a scaled \(2\times2\) Hadamard block after row and column phase changes and permutations.

Partition the nonempty columns by their exact row supports \(S\); let \(L_S\) denote the coefficient \(p\)-norm of that group, and choose \(S_*\) with largest \(L_{S_*}=M\). Fix the row phases on \(S_*\) to maximize that group's contribution to
\[
B(A)=\max_{|y_i|=1}\sum_j\Big|\sum_i a_{ij}y_i\Big|.
\]
Its maximized contribution is at least \(M\), by the two-row theorem (also valid for a single row). Randomize all remaining row phases independently and uniformly on the unit circle. A different two-row support \(S\) meets \(S_*\) in at most one row, so its relative phase is uniform, even if some of the other columns share that phase. Linearity of expectation does not require independence between columns. Singletons have deterministic absolute value.

For \(a,b\ge0\), the mean of \(|a+b e^{it}|\) over uniform \(t\) is at least \((2\sqrt2/\pi)(a^2+b^2)^{1/2}\). Indeed, after factoring out \((a^2+b^2)^{1/2}\), the remaining mean is that of \(\sqrt{1+u\cos t}\) for \(u=2ab/(a^2+b^2)\in[0,1]\). This mean is even and concave as a function of \(u\) on \([-1,1]\); at \(u=1\) it equals \(2\sqrt2/\pi\). Norm comparison in dimension 2 therefore bounds each column mean below by \(c(a^p+b^p)^{1/p}\), for \(c=2^{5/4}/\pi\). This also holds for a singleton. Since the sum of column norms in a group dominates their \(p\)-norm \(L_S\), taking expectations yields
\[
B(A)\ge M+c\sum_{S\ne S_*} L_S .
\]

For \(x\ge y\ge0\), convexity of \(t\mapsto(1+t^p)^{1/p}\) (it is a norm restricted to a line) gives
\[
(x^p+y^p)^{1/p}\le x+\beta y,\qquad \beta=2^{3/4}-1.
\]
Start at \(x=M\), add the remaining group norms one at a time, and update \(x\) by the left hand side, which is always at least \(M\). This proves
\[
L(A)\le M+\beta\sum_{S\ne S_*}L_S,\qquad
B(A)-L(A)\ge(c-\beta)\sum_{S\ne S_*}L_S.
\]
The gap coefficient is positive: \(\beta<3/4\) since \(8<(7/4)^4\), and \(c>3/4\) follows from \(\pi<22/7\) and \(2^{1/4}>33/28\). Thus equality requires a single support group, after which the two-row equality classification applies. A singleton gives sharpness.

This argument also gives a general *block gluing* criterion. Partition the columns into groups whose sets of active rows meet pairwise in at most one row. Suppose each group independently satisfies \(B_S\ge L_S\), and its Haar-averaged absolute-sum contribution is at least \(\beta L_S\). Optimizing the largest group and randomizing the rest gives \(B(A)\ge L(A)\). Fixing a single row phase in any other group does not change its absolute-sum distribution, by rotating all its row phases by a common factor.

For an example not covered by the acute gauge or a global two-row hypothesis, take three columns on rows 1 and 2 with entries \((1,1)\), \((1,e^{2\pi i/3})\), and \((1,e^{-2\pi i/3})\), and a fourth column \((1,1)\) on rows 2 and 3. Its first three columns already require gauge half-width \(\pi/3\) by the parallel-path computation in §2. There are three active rows, but every column has support of size two.

The unrestricted complex constant remains open. Targeted searches found no directly matching sharp per-column sparsity statement; the neighboring mixed-inequality results cited above do not imply the theorem.
