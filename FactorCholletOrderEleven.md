# Chollet's permanent inequality in order eleven

Research note, 28 November 2026.

**Theorem.** Let \(A,B\) be arbitrary \(11\times11\) complex Hermitian positive semidefinite matrices. Then
\[
 \operatorname{per}(A\circ B)\le \operatorname{per}(A)\operatorname{per}(B).
\tag{1}
\]
If both diagonals are strictly positive, equality holds exactly when both matrices are diagonal. If either matrix has a zero diagonal entry, both sides vanish.

There is no rank, real-entry, or graph-support assumption. The proof uses fully covered exact rational inequalities, but it is not a Lean formalization. It does not settle orders \(n\ge12\). Restricted by maximum off-diagonal modulus after correlation normalization, the same small-entry argument below gives \(r\le2/5\) in order 12 and \(r\le3/8\) in order 13.

[McBee, *Chollet's permanent conjecture through order ten*](https://hexagonmath.org/pdf/2611.01163v1), proves the unrestricted theorem through 10, and describes an outstanding intermediate gap in order 11 in §6. He provides the double-border geometry used here. The new small-entry estimates reach \(21/50=0.420\), and a newly specified rational double-border schedule covers \([417/1000,1]\). The two exact ranges overlap. The lower-order cases actually needed for the induction are replayed by the accompanying programs as well, using McBee's order-7 and order-9 border polynomials and a short one-border argument credited below. No unarchived schedule or floating-point inequality is a premise.

## 1. Reductions and notation

Write \(\operatorname{per} M=\sum_{\sigma}\prod_i M_{i,\sigma(i)}\). The permanent of a PSD matrix is nonnegative: if the matrix is the Gram matrix of vectors \(v_i\), this permanent is the squared norm of their product of linear forms in the symmetric tensor space with orthogonal monomials of squared norm \(\alpha!\). The identity follows by expanding the product, or by projecting the tensor product onto its symmetric part. In particular the permanent is monotone in PSD Loewner order: adding a PSD Gram matrix takes the orthogonal direct sum of the Gram vectors and preserves the old norm term in the sector using no new coordinates. We use [Lieb's block inequality](https://doi.org/10.1512/iumj.1967.16.16008),
\[
 \operatorname{per}A\ \ge\ \prod_j\operatorname{per} A[I_j]
\tag{2}
\]
for any partition into principal blocks, in particular \(\operatorname{per}A\ge\prod_i A_{ii}\). Each \(A[I]\) denotes the principal submatrix indexed by \(I\).

As in Chollet's reduction, Cauchy–Schwarz on permutation products gives
\[
 |\operatorname{per}(A\circ B)|^2
 \le \operatorname{per}(A\circ\bar A)\operatorname{per}(B\circ\bar B).
\tag{3}
\]
Thus it suffices to prove \(\operatorname{per}(A\circ\bar A)\le\operatorname{per}(A)^2\). Positive diagonal congruence normalizes \(A\) to a correlation matrix and scales both sides by the same positive factor. A zero diagonal entry in a PSD matrix forces its row and column to vanish. Henceforth assume \(A_{ii}=1\).

Let \(H=A-I\), let \(X_{ij}=|H_{ij}|^2\), and suppose \(|H_{ij}|\le r_0\) off the diagonal. Set
\[
 E=r_0^2,\quad M=\binom n2,\quad s=\sum_{i<j}X_{ij},\quad
 d_i=\sum_jX_{ij},\quad R=\sum_i d_i^2,\quad Q=\sum_{i<j}X_{ij}^2.
\]
This \(E\) is a scalar, and \(X\) is a symmetric hollow matrix with entries in \([0,E]\). We have \(s^2/M\le Q\le Es\), \(R\ge4s^2/n\). Define
\[
 U_m(Z)=\sum_{|\operatorname{supp}(\sigma)|=m}
             \prod_{i:\,\sigma(i)\ne i}Z_{i,\sigma(i)}.
\]
Then \(\operatorname{per}(I+Z)=1+\sum_{m=2}^n U_m(Z)\), and \(A\circ\bar A=I+X\).

## 2. Strong lower bounds from random blocks

### 2.1 Global cubic and quartic bounds

The eigenvalues \(\xi_i\) of \(H\) satisfy \(\xi_i\ge-1\), \(\sum_i\xi_i=0\), and \(\sum_i\xi_i^2=2s\). Expanding \(\sum_i(\xi_i+1)(\xi_i-2s/n)^2\ge0\) yields
\[
 U_3(H)=\operatorname{tr}H^3/3
    \ge (-2s+4s^2/n)/3.
\tag{4}
\]
This uses all the PSD constraints from the common global spectrum, rather than bounding each triangle independently. Likewise
\[
 U_4(H)=\tfrac12 s^2+\tfrac14\operatorname{tr}H^4-R+Q
    \ge \tfrac12 s^2-\tfrac34 R+Q.
\tag{5}
\]
For the identity, the contribution from two disjoint transpositions is \((s^2+Q-R)/2\). The trace of \(H^4\) counts every oriented simple 4-cycle four times. Four-step closed walks with exactly two distinct vertices contribute \(2Q\); those with exactly three contribute \(2R-4Q\), by enumerating the choices of the two distinct neighbors of the doubled vertex. Thus the remaining oriented 4-cycle contribution is \((\operatorname{tr}H^4-2R+2Q)/4\). For the inequality, \(\operatorname{tr}H^4=\|H^2\|_F^2\ge R\), since the diagonal of \(H^2\) is \(d_i\). The simpler bound \(R\le2(n-1)Q\) also gives \(U_4(H)\ge s^2/2-(3(n-1)/2-1)Es\).

### 2.2 Exact degree-square cap

Let \(L_n(j)\) be the largest sum of squared degrees of a simple graph on \(n\) vertices with \(j\) edges. It is enough to enumerate graphs obtained from a single vertex by adding isolates or universal vertices. To see this, in any maximizer write \(u,v\) for vertices with \(d_u\ge d_v\). If \(w\notin\{u,v\}\) is adjacent to \(v\) and not to \(u\), moving \(vw\) to \(uw\) strictly increases the squared degree sum by \(2(d_u-d_v)+2\). Thus neighborhoods are nested in this sense. A minimum-degree vertex is either isolated or adjacent to a vertex that is forced by nesting to be universal. Delete the respective isolated or universal vertex; the remaining neighborhood relation is preserved, and induction gives the claimed construction. This proves the necessary compression without using an assumed description of all extremal graphs.

For \(j\le s/E\le j+1\) and \(\theta=s/E-j\),
\[
 R\le E^2\{(1-\theta)L_n(j)+\theta L_n(j+1)\}.
\tag{6}
\]
Indeed the maximum of the convex squared degree sum on the capped edge-mass polytope is attained at an extreme point, where all but at most one weight divided by \(E\) are zero or one. Interpolating the two simple graphs of that extreme point and applying convexity proves (6). Integer edge masses, including the final all-edges endpoint, are included by continuity.

### 2.3 Logarithmic strengthening of block Lieb

For a principal block \(I\) of size \(k=3\) or 4, put \(S_I=\sum_{\{i,j\}\subset I}X_{ij}\), and \(V_I=\operatorname{per}A[I]-1\). Let \(S_*=\binom k2 E\). We have \(\alpha_k S_I\le V_I\le V_*\), with
\[
 \alpha_3=1-2r_0/3,\quad V_*^{(3)}=3E+2r_0^3;\qquad
 \alpha_4=2/3,\quad V_*^{(4)}=6E+8r_0^3+9r_0^4.
\]
The triangle lower bound follows from \(3|abc|\le r_0(|a|^2+|b|^2+|c|^2)\). The four-point lower bound is [Grone–Pierce's correlation-matrix inequality](https://doi.org/10.1137/0609016), \(\operatorname{per} A[I]\ge(\|A[I]\|_F^2-1)/3\). The displayed upper bounds follow by counting the supports of permutations in a 3- or 4-point block. All \(\alpha_k\) are positive for the parameters used.

For \(\alpha=\alpha_k\) and the corresponding caps, define
\[
 \ell=\frac{\log(1+\alpha S_*)}{S_*},\quad
 h=\frac{\log((1+V_*)/(1+\alpha S_*))}{V_*-\alpha S_*},\quad
 K=\frac{\alpha^2}{2(1+\alpha S_*)^2}.
\]
Concavity with a uniform second-derivative bound gives
\(\log(1+\alpha S_I)\ge \ell S_I+K S_I(S_*-S_I)\). Also the logarithm's secant between \(\alpha S_I\) and \(V_I\) is at least \(h\): average its decreasing derivative on the linear interpolation of these two endpoints and compare with the interpolation of their respective upper bounds. Thus
\[
 \log(1+V_I)\ge
 \ell S_I+K S_I(S_*-S_I)+h(V_I-\alpha S_I).
\tag{7}
\]

For a uniformly random \(k\)-subset \(I\), let \(f_m=\binom{k}{m}/\binom{n}{m}\) (zero if \(m>k\)). Then
\[
 \begin{split}
 \mathbb{E}S_I &= f_2 s,\\
 \mathbb{E}S_I^2 &= f_4 s^2+(f_3-f_4)R+(f_2-2f_3+f_4)Q,\\
 \mathbb{E}V_I &= f_2 s+f_3 U_3(H)+f_4 U_4(H).
 \end{split}
\tag{8}
\]
The second equation expands pairs of distinct edges according to whether they share a vertex. The third keeps exactly the permutations whose supports lie in \(I\). Average the logarithm of (2) over a uniform partition with block sizes \((4,4,3)\) at order 11. Then (7)–(8), with (4)–(6), give a lower bound on \(\log\operatorname{per}A\). For any ignored singleton the permanent is one. The checker uses a nonnegative lower bound separately for the expected quadratic term and the expected defect in (7), because both original terms are nonnegative.

## 3. Upper bounds retaining permutation edge overlaps

The self-Hadamard upper bound is obtained by comparing four estimates for each \(U_m(X)\). They are valid simultaneously. The first two are McBee's elementary edge-cap and closed-walk cycle-index estimates; the last two preserve more of the injective permutation structure.

### 3.1 One selected edge and the unrestricted cycle bound

Write \(D_m\) for the derangement count of \(m\) letters, \(K_m=\binom nm D_m\), and \(u=\sqrt{2Es}\ge\|X\|_F\). Keeping one factor in each product and bounding the rest by \(E\) gives
\[
 U_m(X)\le K_m E^{m-1}s/M.
\tag{9}
\]
A directed simple cycle of length \(j\) has each cyclic starting position counted in the trace of \(X^j\). Dropping vertex-disjointness, as in McBee's Lemma 3.3, allows unordered selections of cycles with repetition: \(j\)-cycles have aggregate weight at most \(\operatorname{tr}(X^j)/j\), and the exponential generating expansion divides the ordered lists of \(k\) such cycles by \(k!\). Equivalently one uses \([z^m]\exp(\sum_{j\ge2}z^j\operatorname{tr}(X^j)/j)\). This bounds \(U_m(X)\) by \(p_m u^m\), where \(p_0=1,p_1=0\) and \(p_m=m^{-1}\sum_{j=2}^m\rho_j p_{m-j}\). We use \(\rho_2=1\), \(\rho_3=(n-2)/\sqrt{n(n-1)}\), \(\rho_j=((n-1)/n)^{(j-2)/2}\) for \(j\ge4\). The cubic is Okumura's trace inequality for a traceless symmetric matrix; directly, for normalized eigenvalues with squared sum one, put \(a=1/\sqrt{n(n-1)}\), \(b=(n-1)a\), and sum \((b-x_i)(x_i+a)^2\ge0\). The remaining powers follow from \(\max|x_i|\le\sqrt{(n-1)/n}\) by Cauchy–Schwarz and \(\sum x_i=0\). All radical constants are rounded upward rationally in the checker.

### 3.2 Two selected edges

Select an unordered pair of directed edges of a uniform derangement supported on \(m\) points. The probabilities of a reversed pair, a pair with one shared endpoint, and a disjoint pair respectively are
\[
 p_0'=D_{m-2}/D_m,\quad p_1'=2/(m-1)-2p_0',\quad
 p_2'=1-p_0'-p_1'.
\]
Indeed the expected number of 2-cycles is \(\binom m2 D_{m-2}/D_m\); each vertex in a longer cycle supplies one adjacent pair and a vertex of a 2-cycle supplies none of that type. By symmetry within each type, putting \(\alpha=p_0'/M,\ \beta=p_1'/((n-2)M),\ \gamma=p_2'/(3\binom n4)\) gives
\[
 U_m(X)\le K_m E^{m-2}
 \left\{\tfrac{\gamma}{2}s^2+\tfrac{\beta-\gamma}{2}R+
             (\alpha-\beta+\tfrac{\gamma}{2})Q\right\}.
\tag{10}
\]
This uses the adjacent undirected sum \(R/2-Q\) and the disjoint undirected sum \((s^2+Q-R)/2\). Choose the safe lower or upper bound for each moment according to the coefficient's sign.

### 3.3 Three selected edges

Fix three distinct directed nonloop arcs with distinct source vertices and distinct target vertices, and let \(v\) be the size of the union of their endpoints. In \(S_n\), the number of permutations of support \(m\) containing these arcs is
\[
 \binom{n-v}{m-v}\sum_{j=0}^{m-v}(-1)^j\binom{m-v}{j}(m-3-j)!,
\tag{11}
\]
zero if \(v>m\). Choose the remaining vertices of the support. A potential fixed point of the remaining bijection cannot be at a vertex touched by one of the specified arcs; inclusion–exclusion on the \(m-v\) untouched vertices proves (11). For each type weight its undirected products by (11) divided by \(\binom m3\), multiplied by the number of allowed orientations:

| Underlying type | \(v\) | Orientations |
|---|---:|---:|
| three disjoint edges | 6 | 8 |
| a two-edge path and a disjoint edge | 5 | 4 |
| a simple three-edge path | 4 | 2 |
| a triangle | 3 | 2 |
| a doubled edge and a disjoint edge (doubled edge distinguished) | 4 | 2 |

These exhaust the patterns since every vertex has in- and out-degree at most one in the selected arcs. Denote the five coefficients by \(a_0,\ldots,a_4\); each actual permutation product can retain any three factors and bound its others by \(E\). For any \(b\ge a_0\), the sum of their retained undirected products with coefficients is at most
\[
 \frac{b s^3}{6}+(a_1-b)_+ W_1+(a_2-b)_+W_2+
                 (a_3-b)_+W_3+a_4 W_4,
\tag{12}
\]
where \(W_i\) sums the products of the corresponding type, with \(x_e^2 x_f\) for the last type. The total weight of all triples of distinct simple edges is at most \(s^3/6\), including triples absent from the table, and gives the baseline \(b s^3/6\). The following upper bounds are used:
\[
 \begin{split}
 W_1 &\le s\,\min\big((n-2)Es,\ R/2-s^2/M\big),\\
 W_2 &\le\min\big((n-1)^2 E^2 s,\ \tfrac12\sqrt{(n-1)/n}\,u R\big),\\
 W_3 &\le \rho_3 u^3/6,\\
 W_4 &\le E\big((1-4/n)s^2+Es\big).
 \end{split}
\tag{13}
\]
For \(W_1\), drop disjointness of the third edge and bound the adjacent-pair weight using \(R\le2(n-1)Q\) or \(Q\ge s^2/M\). For \(W_2\), choose the middle edge; the choices at its two ends total at most \(\sum_{i<j} X_{ij}d_i d_j\). Bound \(d_i\le(n-1)E\) or use the Rayleigh estimate for \(d^TXd/2\). For \(W_3\) use the traceless cubic trace bound. For \(W_4\) drop one copy of the doubled edge with a factor \(E\), obtaining at most twice the undirected disjoint sum times \(E\), and use \(R\ge 4s^2/n\). Multiplying (12) by \(E^{m-3}\), with (13), gives the last upper bound. The program can choose among \(b=a_0,a_1,a_2,a_3\) satisfying \(b\ge a_0\); no optimizing claim is needed.

### 3.4 Exact closed-interval comparison

The [small-entry checker](verify_factor_chollet_small_entries.py) sets \(s=E y^2\) so \(0\le y\le\sqrt M\). On each piece \(j\le y^2\le j+1\), (6) gives an affine expression in \(y^2\) for the upper bound on \(R\). Its quotient by \(y^2\) is bounded using the sign of the intercept; the first piece has zero intercept and is continuous at zero. Every term of (7)–(13) is then bounded after division by \(y^2\), with signs tracked as in the formulas. Positive rational lower bounds for the logarithm coefficients use
\(\log t\ge 2\sum_{j=0}^{29}((t-1)/(t+1))^{2j+1}/(2j+1)\) for \(t\ge1\), rounded downward. Square-root endpoints are enclosed with outward integer square roots. Dividing the exponential lower bound minus one by \(y^2\) is safe: if \(\log\operatorname{per}A/y^2\ge L>0\) on \([y_-,y_+]\), then
\[
 \frac{\operatorname{per}(A)^2-1}{y^2}
 \ge \sum_{j=1}^{17}\frac{(2L)^j y_-^{2j-2}}{j!}.
\]
All terms are nonnegative. The resulting rational lower bound strictly dominates the sum of the rational upper bounds for \(U_m(X)/y^2\) on each closed piece. Adjacent pieces overlap their exact algebraic endpoints; failed boxes subdivide at their rational midpoint. Thus \(y>0\) gives strict inequality and \(y=0\) is the diagonal equality case.

The verifier closes 57 boxes at maximum subdivision depth 1 for \(n=11,r_0=21/50\), with the lower floor of the normalized gap \(46\) in units \(10^{-6}\). Its optional \(n=12,13\) checks close 66 and 116 boxes respectively. A [separate literal enumeration](verify_factor_chollet_support_independent.py) verifies the degree-square compression for all 33,866 graphs of orders 2 through 6, the exact cubic and quartic identities on signed rational inputs, and 30,178 fixed-arc completions and orientations using literal small permutations.

## 4. Exact double-border continuation for large entries

Here use \(r=\max_{i\ne j}|A_{ij}|\). Permute a maximal pair to the last two positions and phase its off-diagonal to \(r\). Permutation preserves the multiset of permutation products, and diagonal unitary conjugation preserves each product. This is the two-border structure of [McBee, §4](https://hexagonmath.org/pdf/2611.01163v1), with a weighted-mean form of his auxiliary scalar that simplifies the interval proof.

Set \(c=(1+r)/2,\ s_0=(1-r)/2\). For \(r<1\), the two border vectors are \(\sqrt c e_+ \mathbin{\pm}\sqrt{s_0}e_-\) in their two-dimensional span. Write the top \(q=n-2\) vectors as \(v_i+ x_i e_++z_i e_-\), with \(v_i\) perpendicular to both directions. Let \(S\) be the Gram matrix of those \(v_i\), \(R_+=xx^*\), \(R_-=zz^*\), and \(B(t)=S+t_1R_++t_2R_-\) for \(t_1,t_2>1\). In the factorially normalized symmetric-tensor monomial basis, multiplying by the product of the two border forms means multiplication by \(c e_+^2-s_0e_-^2\). Its squared-norm operator on the sector of total border degree \(k\le q\) is the tridiagonal-by-parity matrix \(G_{k,r}\), with \(a+b=k\),
\[
 (G_{k,r})_{a,a}=c^2(a+2)(a+1)+s_0^2(b+2)(b+1),\quad
 |(G_{k,r})_{a,a+2}|^2=(cs_0)^2(a+2)(a+1)b(b-1).
\tag{14}
\]
These formulas are immediate from multiplying \(e_+^a e_-^b/\sqrt{a!b!}\) by \(e_+^2\) or \(e_-^2\). Distinct total orthogonal-mode occupations yield orthogonal sectors. Write \(D_k(u)\) for the diagonal with entries \(u_1^a u_2^b\). Norm-squared scaling of the top Gram is exactly \(D_k(t)\). Hence \(G_{k,r}\succ\mu D_k(t)\) for all \(k\) implies \(\operatorname{per}A>\mu \operatorname{per} B(t)\): the product of the \(q\) nonzero top linear forms is nonzero.

In the self-Hadamard Gram representation the corner has modulus \(r^2\); put \(c_2=c^2+s_0^2=(1+r^2)/2\) and \(s_2=2cs_0=(1-r^2)/2\). With \(a=|x|^2\), \(b=|z|^2\) and \(u=x\circ\bar z\), the new two projection covariances are
\[
 P_+=(ca+s_0b)(ca+s_0b)^T/c_2,\qquad
 P_-=2\mathop{\rm Re}(u)\mathop{\rm Re}(u)^T.
\]
Indeed the off-block entries are absolute squares of the two border coordinates, and their sum and difference give these normalizations. Write the new top remainder as \(T_0\), which is PSD by this Gram projection. Define
\[
 v=(c,s_0)^T/\sqrt{c_2},\quad z_0=(s_0,-c)^T/\sqrt{c_2},
 \quad D=\operatorname{diag}(t_1^2,t_2^2)-z_0z_0^T,\quad
 w_1=(v^TD^{-1}v)^{-1},\ w_2=t_1t_2.
\tag{15}
\]
Here \(D\succ0\) because \(v,z_0\) are an orthonormal pair and \(t_i>1\). Cauchy–Schwarz in the \(D\) inner product gives \(D-w_1vv^T\succeq0\). Expanding the self-Hadamard top Gram now gives
\[
 B(t)\circ\overline{B(t)}\succeq T_0+w_1P_++w_2P_-.
\tag{16}
\]
For detail, the two pure square terms in the unscaled Gram are \(aa^T+bb^T\). Their remainder after \(P_+\) is \((s_0a-cb)(s_0a-cb)^T/c_2\), giving \(D-w_1vv^T\) in (16) with the coefficient columns \([a\ b]\). The two mixed rank-one terms are \(uu^*+\bar u\bar u^*\), whose remainder after \(P_-\) is \(2\mathop{\rm Im}(u)\mathop{\rm Im}(u)^T\); it scales by \(w_2\ge1\). The two cross sums between \(S\) and \(R_+\), and between \(S\) and \(R_-\), are PSD by the Schur product theorem, and scale by \(t_1,t_2\ge1\). The \(S\)-square term is unchanged. This proves (16).

If also \(\mu^2 D_k(w)\succ G_{k,r^2}\) for every \(k\le q\), then the tensor upper comparison, (16), Loewner monotonicity, and the order-\(q\) self-Hadamard case give successively
\[
 \operatorname{per}(A\circ\bar A)
 \le \mu^2\operatorname{per}(T_0+w_1P_++w_2P_-)
 \le \mu^2\operatorname{per}(B(t)\circ\overline{B(t)})
 \le \mu^2\operatorname{per}(B(t))^2
 < \operatorname{per}(A)^2 .
\tag{17}
\]
At \(r=1\), the two border vectors coincide and there is just the \(e_+\) line. Formula (14) becomes the diagonal factor \((k+2)(k+1)\) at \(a=k,b=0\), \(w_1=t_1^2\), and (16) follows directly from expanding \(S+t_1 R_+\) times its conjugate in the Hadamard product. All \(b=0\) comparisons hold strictly at the verified endpoint, so (17) applies there too without dividing by \(s_2=0\).

For replication of the schedule, the \(2\times2\) inverse in (15) simplifies to
\[
 w_1=
 \frac{c^2(t_2^2-1)t_1^2+s_0^2(t_1^2-1)t_2^2}
      {c^2(t_2^2-1)+s_0^2(t_1^2-1)} .
\tag{18}
\]
It is increasing in \(r\) when \(t_1\ge t_2\), by the relative weights in this mean. It is increasing in each \(t_i\) by the positive inverse formula in (15), as increasing the positive diagonal increases \(D\). This lets the [double-border checker](verify_factor_chollet_double_border.py) bound \(w_1\) uniformly from below on each interval. The diagonal entries in the two strict spectral tests and the squares of the off-diagonal entries are bounded with rational endpoints. In each parity block the successive positive pivots of a symmetric tridiagonal matrix are \(d_0\) and \(d_i-e_{i-1}^2/p_{i-1}\). Lower diagonals and upper off-diagonal squares produce inductive lower bounds for these pivots. Thus no square roots of the off-diagonal entries, eigenvalue approximation, or interpolation tolerance is needed in verification.

At order 11 the schedule is the piecewise linear interpolation of 15 tabulated rational knots in that checker. It covers \([417/1000,1]\) in 63 closed leaves of depth at most 4, with all certified pivots at least \(2792195\cdot10^{-9}\). The three schedule variables at each point have \(t_1>t_2>1\) and \(\mu>0\).

## 5. Base ladder and conclusion

For completeness, the base argument through order 6 is the single-border induction of [Li, Zhao and Luo](https://www.preprints.org/manuscript/202608.2196), as in McBee. A last vector \(e\) with norm one separates the top Gram into \(S+vv^*\). Writing \(p_k\ge0\) for the coefficient occupation norms in the \(e\) line, \(\operatorname{per}(S+t vv^*)=\sum_k t^k p_k\) and the full permanent is \(\sum_k(k+1)p_k\). In the self-Hadamard Gram the analogous top split is \(T+ww^T\), with \(w=|v|^2\). By expansion, \((S+\sqrt{2}\,vv^*)\circ\overline{(S+\sqrt{2}\,vv^*)}\succeq T+2ww^T\): its cross terms are scaled upward and its rank-one square doubles. For \(0\le k\le5\), \(k+1\le2^k\le(k+1)^2\). These inequalities compare the two occupation weights and allow induction using order \(n-1\) exactly as in (17), without needing strictness. The base \(n=1\) is equality.

At order 7 the new small-entry checker covers \(r\le1/5\) and the double-border checker replays McBee's published polynomial schedule on \([1/5,1]\) with base 5. At order 9 the analogous ranges are \(r\le8/25\) and \([8/25,1]\), with base 7. The respective small checks use 21 and 36 closed boxes; the double checks use 104 and 42 closed boxes. This supplies the order-9 input in (17) for order 11, independently of the published implementation. The prior McBee arithmetic code at revision [203f6fd](https://github.com/coracle-us/conjectures/tree/203f6fdc6a007edcfe2fcbce80208d5746690468/results/chollet-permanent-through-10) was also replayed unchanged in ordinary Python and reported all 480 checks passing. The two lower-order border schedules are credited to that paper; our verifier uses different interval arithmetic.

Finally the two order-11 ranges \([0,21/50]\) and \([417/1000,1]\) cover all possible \(r\), and the self-Hadamard inequality is strict except at a diagonal correlation matrix. Returning from normalization and using (3) proves (1) and its equality statement.

Run all attached programs in ordinary Python 3 (no -O):

```sh
python3 verify_factor_chollet_small_entries.py --additional
python3 verify_factor_chollet_double_border.py
python3 verify_factor_chollet_support_independent.py
```
