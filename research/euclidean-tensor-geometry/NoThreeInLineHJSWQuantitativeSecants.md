# Effective low-secant bounds in classical lifted hyperbola frames

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

**Scope.** Let \(p\) run over odd primes, \(Q_p=[0,2p)^2\cap\mathbb Z^2\), and take a canonical clean HJSW seed \(S_{p,\gamma}\) for the carrier \((X-h)Y=\gamma\bmod p\), \(h=(p-1)/2,\ \gamma\ne0\), which differs by \(O(1)\) sites from the carrier restricted to the rescaled frame \(M=[0,2]^2\setminus(1/2,3/2)^2\) (the alternative translated/rotated conventions have the same proof). For \(D\subset S\), let \(W_{D,k}\) be the sites of \(Q_p\setminus S\) on at most \(k\) lines containing two points of \(S\setminus D\). There are absolute positive \(c,C\) such that, for each fixed \(k\ge0\) and all sufficiently large \(p\) (depending on \(k\)), uniformly in \(D,\gamma\),
\[
 |W_{D,k}|\le C\left(p^2\exp[-c\sqrt{\log p}]+p|D|\right).
\]
In fact one can allow \(k\le c\sqrt{\log p}\) after reducing \(c\). The same estimate, including the deletion term, holds with constants depending on \(M\) for any fixed positive-area finite rectangle-union mask, without assuming the mask carrier is itself no-three-in-line. This is quantitative board-area suppression, **not** \(o(p)\) and not a barrier against arbitrary linear augmentation.

Sections 1–4 first prove a cube-root logarithmic exponent by a mesh. Section 5 upgrades it to the displayed square-root exponent and gives the deletion statement for general masks.

Prior art: [paper 31](https://rstation.ai/problems/no_three_in_line/papers/31), Sections 3–6 and discussion of rates, develops the same negative-weight kernels for fixed weights, with iterated limits explicitly giving no decay rate. Section 8.2's square-root bound is for the expected intersection with a specified random source at a fixed positive deletion fraction, not a growing-weight quantitative population estimate. [Paper 32](https://rstation.ai/problems/no_three_in_line/papers/32), Theorem 2 and Section 8, studies a specified alternate conic and fixed finite directions, explicitly without a quantitative rate. [Paper 47](https://rstation.ai/problems/no_three_in_line/papers/47), Section 8, gives verified finite positive insertions up to \(p=32003\). The new ingredients here are integer free coordinates eliminating all carry-frequency relations, effective moments with growing degree, and an auxiliary Bernoulli reduction requiring only distinct weights. Standard Hasse–Weil curve point count and [Weil's Kloosterman bound](https://doi.org/10.1073/pnas.34.5.204) are imported.

## 1. Integer free coordinates and uniform finite-field Fourier

Fix a large constant \(L_0\ge 5\) below and take distinct reduced negative rationals \(t_i=a_i/b_i\in[-2L_0,-L_0]\), \(1\le b_i\le R\), so \(a_i<0\). The physical incidence
\(b_i z=(b_i-a_i)A_i+a_i B_i\)
is equivalent, over the integers, to
\[
 A_i=z+a_iv_i,\qquad B_i=z-(b_i-a_i)v_i,\qquad v_i\in\mathbb Z^2.
\]
Indeed the reduced relation gives coordinatewise \(a_i\mid(A_i-z)\); the converse is immediate. Let \(F_t(z)\) count these incidences with \(A_i,B_i\) in the frame carrier. After scaling by \(p\), \(z\) is in the board square and every \(v_i\) has coordinates of absolute value at most \(2/|a_i|\); thus all free coordinates lie in a fixed bounded cube, and each \(v_i\) modulo \(p\) has at most one physical lift for each fixed physical \(z\) (its coordinate interval has length at most \(4p/|a_i|<p\)). We count only away from the root conic and axes. Then \(v_i\ne0\) and no \(A_i=B_i\) terms occur.

For \(j\) weights, the free residue coordinates \((z,v_1,\ldots,v_j)\) form an ambient vector space of dimension \(d_j=2+2j\). In centered field coordinates take \(z=(u,\gamma c/u)\) with \(u,c\ne0\). As in paper 31, writing the first coordinate of \(A_i\) as \(ur_i\), both endpoints lie on the carrier exactly when
\[
 (1-t_i)c r_i^2-(c+1-2t_i)r_i+1-t_i=0,\quad
 \eta_i^2=(c-1)(c-\alpha_i),\quad \alpha_i=(1-2t_i)^2,
\]
where \(r_i=(c+1-2t_i+\eta_i)/(2(1-t_i)c)\). The second endpoint is uniquely determined by the relation. Assume \(p>C_{L_0}R^2\). Then all \(a_i,b_i,b_i-a_i\) are nonzero in the field, and \(\alpha_i\) are nonzero, distinct and different from 1. In fact the differences and sums of the rational numbers \(1-2t_i\) have nonzero integer numerators of absolute size \(O_{L_0}(R^2)\), as do the comparisons with \(0,\pm1\).

Remove \(c=0,1,\alpha_1,\ldots,\alpha_j\). The normalization of the field extension adjoining the \(j\) radicals is geometrically connected of degree \(2^j\): any nonempty product has odd valuation at the distinct \(\alpha_i\) belonging to one chosen factor. It has independent sign flips and genus \(O((j+1)2^j)\) by Riemann–Hurwitz, since all ramification is tame and lies above at most \(j+2\) places (including infinity). Each removed base point costs at most \(2^j\) points. Thus Hasse–Weil gives \(p+O((j+1)2^j\sqrt p)\) usable points on the curve, whose affine radical solutions are in bijection with the allowed \((c,r_1,\ldots,r_j)\). There are no singular affine ambiguities off the branch and pole levels since each chosen radical is nonzero there.

For every *nonzero finite-field frequency* in the free coordinates, the complete sum over these residue incidences is \(O((j+1)2^j p^{3/2})\). To see why no nonzero relation frequencies remain, change coordinates linearly over \(\mathbb F_p\) from \((z,v_i)\) to \((z,A_i)\). This is invertible, with nonzero diagonal multipliers \(a_i\), so the new coefficient vectors in the \(x\)- and \(y\)-coordinates are not both zero. The Fourier phase becomes
\[
 u f(c,\boldsymbol\eta)+\gamma u^{-1} g(c,\boldsymbol\eta),
\]
where \(f\) is a constant linear combination of \(1,r_i\), and \(g\) of \(c,1/r_i\). Both families are linearly independent over the constant field: flipping \(\eta_i\) independently makes exactly its own \(r_i\) or \(1/r_i\) summand change nontrivially. Thus \(f,g\) cannot both vanish identically. On its quadratic subfield each \(r_i\) and inverse is a fixed-degree rational function with pole degree bounded by an absolute constant, as follows from the explicit formula and the nonzero product of the two roots. Pullback to the cover multiplies pole degrees by at most \(2^{j-1}\); the common-zero set of \(f,g\) has at most \(O((j+1)2^j)\) points by the pole-degree bound on one nonzero function. Away from that set, summing over \(u\ne0\) is bounded by \(2\sqrt p\) (or by 1 if just one coefficient vanishes), by Weil. The common zeros contribute at most \(O((j+1)2^j p)\). The zero-frequency count is \(p^2+O((j+1)2^j p^{3/2})\) by the curve point count. The same estimates are invariant under using an affine translated carrier, since centered coordinates only introduce constant phase factors in \((z,v_i)\).

## 2. Effective transfer to physical boxes and moments

For a residue interval \(I\) represented by a consecutive integer interval of length \(\le p\), the normalized Fourier coefficients of its indicator have \(\ell^1\)-sum \(O(\log p)\) by the finite geometric series bound. Hence on each axis-aligned physical box, with coordinates of \((z,v_1,\ldots,v_j)/p\) in a fixed bounded cube, Fourier completion gives
\[
 \frac{\#\{\text{residue solutions in the physical box}\}}{p^2}
 =\operatorname{vol}(\text{box})+
 O\left(C^{j}(j+1)(\log p)^{d_j}/\sqrt p\right).
\]
For boxes crossing integer-period boundaries, split each coordinate at the bounded number of such boundaries; this costs a factor \(C^{d_j}\), absorbed by \(C^j\). Half-open boxes ensure no lift counted twice. The volume formula also absorbs floor errors \(O(C^{d_j}d_j/p)\) from replacing the physical lattice interval length divided by \(p\) by its real length. Counting the box means each physical lift of a residue is counted separately. Above, without the mask restrictions, an arbitrary \(v_i\)-box may admit several lifts; period splitting treats this correctly.

Let \(G\subset Q_p\) be the common good set after removing the axes and the conic-level exceptional sets for all weights in \(\mathcal T_R=\{a/b:1\le b\le R,\ (a,b)=1,\ t\in[-2L_0,-L_0]\}\). Its complement has \(O_{L_0}(R^2p)\) sites. For the \(j\) selected weights the frame restrictions are exactly
\[
 z/p\in[0,2)^2,\qquad (z+a_i v_i)/p,\ (z-(b_i-a_i)v_i)/p\in M .
\]
The region's boundary lies in \(O_M(j+1)\) hyperplanes even when \(M\) is a finite union of rectangles. On a mesh of size \(\le 1/L\) each such hyperplane meets at most \(C^{d_j}d_j L^{d_j-1}\) mesh boxes: solve it for a coordinate where the absolute coefficient is largest, and for each choice of the other coordinate intervals its range in the solved coordinate has length at most \(d_j/L\). This is uniform in the integer coefficients, no lower bound on their magnitudes required. Take inner/outer mesh box approximations; their volume difference is at most \(C_M^j(j+1)^2/L\). Sum the per-box discrepancy over \(O(C^{d_j}L^{d_j})\) boxes. A bounded Lipschitz test \(f_0(z/p)\) is approximated by a constant per box at error \(O(\operatorname{Lip}(f_0)/L)\) times the total solution mass in the bounded cube; this is bounded by \(C^j\) for the ambient box Fourier estimate (for the parameters used below). Removing additional common exceptional roots costs \(O(C^j R^2/p)\) because each selected weight has at most two physical incidences at each root outside its own exceptions. At \(j=0\) use the ordinary Riemann sum, and remove these roots at the same cost.

It follows, writing \(E_j=C_M^{j+1}(j+1)^2[ L^{-1} + (CL\log p)^{d_j}/\sqrt p + R^2/p]\), that
\[
 \left|p^{-2}\sum_{z\in G} f_0(z/p)\prod_{i=1}^j F_{t_i}(z)
 -\int_{[0,2]^2} f_0(z)\prod_{i=1}^j\lambda_{t_i}(z)\,dz\right|
 \le (\|f_0\|_\infty+\operatorname{Lip}(f_0))\,E_j.
\]
The main term separates because the physical variables \(v_i\) are independent under Lebesgue measure conditional on \(z\), with
\[
 \lambda_t(z)=\int {\bf1}_M(z+a v){\bf1}_M(z-(b-a)v)\,dv .
\]
This exactly includes the congruence density, and no extra factor is missing. Changing variables \(A=z+a v\) gives paper 31's kernel with the \(a^{-2}\) factor. Its uniform Lipschitz bound for rectangles follows from bounding the symmetric difference of two translated scaled rectangles; translating \(z\) by \(h'\) translates each inverse image by at most \(|h'|/|a|\) or \(|h'|/(b-a)\), respectively, with side lengths bounded by a constant. Also \(\lambda_t(z)\le C_M/b^2\). Taking \(L_0\) large enough, the intersection of \(M\) and the inverse image of \(M\) under \(A\mapsto(1+|t|^{-1})A-|t|^{-1}z\) has area at least \(|M|/2\) uniformly over all board roots \(z\); use moving boundaries of the finitely many rectangles and the bounded board, or continuity in \(L^1\). Thus \(\lambda_t(z)\ge c_M/b^2\). The standard coprime count in a fixed interval, \(|J|\varphi(b)+O_J(\tau(b))\), yields
\[
 \lambda(z):=\sum_{t\in\mathcal T_R}\lambda_t(z)\asymp_M\log R
\]
uniformly on the full board.

## 3. A growing even moment without repeated-weight sums

At each good root introduce auxiliary, conditionally independent Bernoulli variables \(Y_t\) with success probabilities \(F_t(z)/8\), and put \(q_t(z)=\lambda_t(z)/8\), \(\mu(z)=\sum q_t(z)\). We chose \(L_0\ge5\), so both probabilities are \(\le1\) (the continuum \(\lambda_t\) is also bounded by the area of \(|v_l|\le2/|a|\)). Compare them with independent Bernoulli \(X_t\) of means \(q_t(z/p)\) at a continuum root. Expand \((\sum_t(Y_t-q_t(z/p)))^{2K}\) into ordered index tuples and terms. In a monomial discard repeated occurrences of a given \(Y_t\), since \(Y_t^m=Y_t\), and likewise for \(X_t\). The remaining distinct-index expectation of \(\prod Y_t\) is exactly \(\prod F_t/8\). Products of at most \(2K\) functions \(q_t\) have supremum at most 1 and Lipschitz constant \(O_M(K)\). Apply the effective moment comparison to each term with \(j\le2K\). Its total normalized error is bounded by
\[
 (C_M R^2)^{2K} (2K+1)\max_{j\le 2K} E_j .
\]
The independent Bernoulli \(2K\)-th centered moment is \(\le[C(K\mu+K^2)]^K\) with absolute \(C\): the usual exponential-moment bound for centered Bernoulli gives two-sided tail \(2\exp(-c\min(u^2/\mu,u))\); integrate the two exponential bounds against \(2Ku^{2K-1}\) and use factorial bounds. Integrate this over the board and add the comparison error.

Put \(P=\log p\), \(K=\lfloor\varepsilon P^{1/3}\rfloor\),
\(R=\lfloor\exp(P/(1000K^2))\rfloor\), \(L=\lceil\exp(P/(100K))\rceil\), for a sufficiently small fixed \(\varepsilon>0\). These parameters obey \(p>C_{L_0}R^2\). The boundary contribution has exponent at most
\(4K\log R-\log L+O_M(K+\log K)\le-0.005P/K\) for large \(p\); the Fourier contribution has exponent at most
\(4K\log R+(4K+2)\log L+(4K+2)\log\log p-P/2+O_M(K+\log K)\le -P/3\).
The exceptional-root contribution is smaller still. In particular total comparison error \(o(1)\).

For a good root with \(\sum F_t(z)\le\lambda(z/p)/4\), the auxiliary mean satisfies \(\mathbb E\sum Y_t\le\mu/4\), so by Markov its sum is \(\le\mu/2\) with probability at least \(1/2\), causing centered \(2K\)-th moment at least \((\mu/2)^{2K}/2\). Divide the integrated bound by this using \(\mu_{\min}\asymp_M\mu_{\max}\asymp_M\log R\). Choosing \(\varepsilon\) small makes \(\log R/K\asymp1/(1000\varepsilon^3)\) large enough that the ratio is \(O_M(e^{-K})\). The total number of bad roots, also including the common exceptions \(O(R^2p)\), is \(O_M(p^2\exp[-c_M(\log p)^{1/3}])\).

In a two-period board every physical line contains at most four sites of the carrier: it reduces to a genuine line modulo \(p\), meets the nonsingular hyperbola in at most two residues, and each residue repeats on a primitive integer line every \(p\) steps, so at most twice in the board. A distinct unordered endpoint pair through a root contributes at most once to all negative-weight counts. Thus for a geometric mask, \(\sum F_t\le6\,c_{\rm mask}(z)\), and fixed low \(k\) is impossible on good non-bad roots for all sufficiently large \(p\).

## 4. Deterministic deletions and remaining gap

Let \(T\) be the exact frame mask of the conic. For the canonical clean seed \(S\), \(|T\triangle S|=O(1)\) (paper 31 definition; changing rounding conventions affects only \(O(1)\) boundary rows/columns, with \(\le2\) sites each). Work with \(T\setminus D'\subset S\setminus D\) where \(D'=(D\cup(T\setminus S))\cap T\), \(|D'|\le |D|+O(1)\). Each destroyed incidence using a deleted endpoint \(A\) requires its other endpoint \(B\equiv A\bmod b\) coordinatewise. For each fixed residue pair modulo \(b\le R\), the frame carrier has at most
\[
 3p/b^2+O(\sqrt p\log^2 p+1)
\]
points in that physical congruence class, uniformly over \(b,A,\gamma\). Indeed, write \(X=r_1+b i,\ Y=r_2+b j\) and split the frame into four rectangles. In each the free integer \(i,j\) run over intervals of the indicated dimensions divided by \(b\), up to rounding; the conic is an affine-translated nondegenerate product in \((i,j)\) because \(b\) is invertible mod \(p\). Complete Fourier of this conic is a Kloosterman sum; Fourier completion over the two intervals gives their sizes multiplied and divided by \(p\), with error \(O(\sqrt p\log^2 p)\). If an interval exceeds \(p\), split it into at most three pieces. The total main term is \(3p/b^2+O(1)\) from the frame area and rounding. Count both endpoint roles, any repeated charges harmless. The total across \(\mathcal T_R\) and all deleted endpoints is therefore
\[
 O\bigl(|D'|(p\log R+R^2\sqrt p\log^2 p)\bigr)=O(|D'|p\log R).
\]
At any outside site on \(\le k\) secants of \(S\setminus D\) and not already in the low-original-count exceptional set, the surviving negative-weight incidence count is \(\le k\) by cleanliness. It therefore lost \(\gg\log R\) incidences. Divide the deterministic total charge by this lower bound and add the original exceptional set. This proves the stated result and explains why it is uniform over adaptive choices of \(D\). For no deletion and fixed independent retention, the same order follows in expectation by disjointness of the endpoints of distinct original seed secants and the binomial tail at order \(\log R\).

The scope limitation is important: \(p^2\exp[-c(\log p)^{1/3}]\) is much larger than \(p\), so it does not bound the best insertion count by \(o(p)\), nor exclude a correlated linear candidate family. No statement is made about an asymptotic gain above \(3/2\).


## 5. Stronger effective transfer: square root rather than cube root in the exponent

The preceding mesh bounds can be strengthened to the square-root exponent in the opening statement. Here is a self-contained power-saving discrepancy argument for the physical window, avoiding dimension-dependent meshing. It replaces Section 2's discrepancy estimate, while the finite-field and deletion arguments remain unchanged. The strengthened arbitrary-deletion assertion also holds (with constants depending on \(M\)) for any fixed positive-area finite rectangle-union mask: apply the same congruence-class count rectangle-wise and use the bound of four carrier points per line after deletion.

Use a rectangular ambient free-coordinate domain for \((z,v_1,\ldots,v_j)/p\), with \(z\in[0,2)^2\) and every \(v_i\in[-2,2)^2\). Test first on an arbitrary axis-aligned sub-box in that domain. Each endpoint coordinate condition is a one-variable interval restriction \(\ell(x)\in I\subset[0,2]\), where \(\ell(x)=z_m+a_i v_{i,m}\) or \(z_m-(b_i-a_i)v_{i,m}\). On the whole ambient domain \(|\ell(x)|\le C_{L_0}R\). Choose a real period \(M_0=C_{L_0}'R\) large enough that all these values lie in \((-M_0/4,M_0/4)\), so there is no wrap alias when the interval restriction is written on the circle as \(\ell(x)/M_0\bmod1\in I/M_0\). Split the finite rectangle-union mask into a fixed number of disjoint half-open rectangles (assign boundary inclusions explicitly, or use the same strips to handle them); choose a rectangle for each endpoint and sum at the end at cost only \(C_M^j\). Each product has at most \(4j\) interval indicators.

Here are explicit trigonometric envelopes for such intervals. With \(H=\lceil p^{3/10}\rceil\), \(\delta=p^{-1/10}\), use the periodic Fejér kernel
\[
 K_H(x)=\frac{1}{H+1}\left(\frac{\sin\pi(H+1)x}{\sin\pi x}\right)^2.
\]
Its integral is 1 and its mass outside distance \(\delta\) of 0 is at most \(\epsilon_0=C/((H+1)\delta)\), by integrating the bound \(K_H(x)\le C/((H+1)x^2)\) for \(0<|x|\le1/2\). For any circular interval \(J\), take its \(\delta\)-enlargement \(J^+\) and majorant
\[
 P_J=(1-\epsilon_0)^{-1}({\bf1}_{J^+}*K_H).
\]
It is nonnegative, at least \({\bf1}_J\), and at most \(1+2\epsilon_0\). Off the \(2\delta\)-boundary strips of \(J\) its excess over \({\bf1}_J\) is at most \(2\epsilon_0\), by the same tail estimate. Thus \(0\le P_J-{\bf1}_J\le 2\epsilon_0+2{\bf1}_{\partial_{2\delta}J}\). Its Fourier \(\ell^1\)-norm is \(O(\log(H+2))\): the interval coefficients are at most \(C/(1+|m|)\) and the kernel multiplies them by factors in \([0,1]\) restricted to \(|m|\le H\). Half-open endpoints and point restrictions are covered by the same boundary strips.

We compare the arithmetic incidence measure \(p^{-2}\) times counting with uniform discrete volume \(p^{-d_j}\) times counting over the same free-coordinate integer points in the sub-box. For a product of trigonometric envelopes, each Fourier term is a separable exponential \(\prod_l e(\theta_l n_l/p)\) in the physical integer coordinates \(n_l\), with real \(\theta_l\). On any interval of integers of length at most \(p\) the finite-field Fourier \(\ell^1\)-norm of \(e(\theta n/p)\) restricted to that interval is \(O(\log p)\), uniformly for real \(\theta\): the finite geometric series bounds its normalized coefficient at residue \(k\) by \(\min(1,C/\operatorname{dist}(\theta-k,p\mathbb Z))\), interpreted as 1 at distance zero, and the distances range with at most two nearest residues in each unit shell. Split physical boxes at period boundaries before this step, at cost \(C^{d_j}\). Section 1's uniform complete estimate, including the zero-frequency error, then makes the difference between arithmetic and uniform discrete evaluations of the product at most
\[
 C_M^{j+1}(j+1)\,\frac{(C\log p)^{6j+2}}{\sqrt p},
\]
since there are at most \(4j\) envelope factors and \(d_j=2+2j\) free coordinates. Crucially no factor \(H^{O(j)}\) occurs: only \(\ell^1\)-norms are used.

By telescoping the product, the error from replacing indicators by their envelopes under either measure is bounded by \(C^j\) times a sum of \(O(j+1)\) boundary masses and the constant error \(\epsilon_0\) times ambient mass (which is \(C^j\) as in Section 2). A boundary mass is a union of a bounded number of strips \(\ell(x)\in J'\) of width \(O(R\delta)\), with no alias. For uniform discrete volume, condition on every coordinate except one with maximum coefficient of \(\ell\): the remaining coordinate is an interval of length at most \(O(R\delta)\), because the maximum coefficient is at least 1. This gives \(C^{d_j}O(R\delta+1/p)\), including border points. For the arithmetic measure, majorize each boundary strip by its own \(P_{J'/M_0}\); its discrete mass is bounded by the same argument on a slightly larger strip plus \(C^{d_j}O(\epsilon_0)\), and Fourier comparison for one envelope has cost bounded by the preceding general discrepancy. Finally the uniform discrete count for the actual polyhedral masks differs from the physical volume by \(O(C_M^{j+1}(j+1)^2/p)\): mesh only for this uniform comparison, each grid cell of side \(1/p\) not crossing a boundary is exact, and the hyperplane mesh argument of Section 2 bounds total boundary-cell volume. This does not count \(p^{d_j}\) separate arithmetic errors.

For a Lipschitz test \(f_0(z)\), mesh just its two root coordinates at resolution \(L_z=\lceil p^{1/100}\rceil\); estimate it by a constant on each sub-box at sup error \(O(\operatorname{Lip}(f_0)/L_z)\). Combine the per-sub-box estimates, then remove the common exceptional roots as in Section 2 without dividing into boxes again. Thus that displayed effective moment estimate is valid with the improved error
\[
 E'_j\ \ll\ C_M^{j+1}(j+1)^2
 \left[L_z^{-1}+L_z^2\left(\frac{(C\log p)^{6j+2}}{\sqrt p}
                  +R\delta+\epsilon_0+p^{-1}\right)+R^2/p\right].
\]
The comparison with the same Lebesgue kernel follows by conditioning on the root exactly as before.

In Section 3 now take \(K=\lfloor \varepsilon\sqrt{P}\rfloor\), \(R=\lfloor\exp(P/(1000K))\rfloor\), with \(P=\log p\) and fixed \(\varepsilon>0\) sufficiently small. For \(j\le2K\), \(C_M^{j+1}(j+1)^2(\log p)^{6j+2}=p^{o(1)}\), \(R=p^{o(1)}\), and the summation factor \((C_MR^2)^{2K}=p^{0.004+o(1)}\). Hence the comparison error including the moment expansion still tends to zero (the slowest factor \(L_z^{-1}\) contributes \(p^{-0.006+o(1)}\)). Now \(\log R/K\asymp1/(1000\varepsilon^2)\), so the same Bernoulli moment and Markov argument yield \(O_M(p^2 e^{-c_M\sqrt{\log p}})\) bad sites, and the same deterministic deletion charge adds \(O_M(p|D|)\). The low threshold may grow to \(c_M\sqrt{\log p}\) by decreasing the constant. Still not an \(o(p)\) augmentation bound.


An independent integer check compared the free-coordinate parametrization with direct ordered endpoint-pair enumeration in 72 cases (9,211 incidences) across four small primes. This corroborates the parametrization, not the asymptotic estimates.
