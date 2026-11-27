# Uniform zonotopes and their box splines: covariance in every rank, convex order in corank at most three

## Results and scope

Let \(g_1,\ldots,g_m\in\mathbb R^d\) span \(\mathbb R^d\), \(d\ge1\). Write \(G=[g_1\ \cdots\ g_m]\), \(r=m-d\), and
\[
Z=G[-1/2,1/2]^m,\qquad
X=\sum_{i=1}^m U_i g_i,\qquad Y\sim\operatorname{Unif}_d(Z),
\]
where the \(U_i\) are independent and uniform on \([-1/2,1/2]\). The law of \(X\) is the box-spline pushforward; it need not be uniform on its support \(Z\). Unif denotes normalized volume, not a measure on the boundary. The corank here belongs to the **given** list of generators and can change under splitting a vector into parallel pieces.

1. **Every \(r\):** \(\operatorname{Cov}(Y)\succeq\operatorname{Cov}(X)\). There is an exact decomposition into a diagonal-in-generators term and positive semidefinite rank-two quotient energies. In particular the kernel of the difference is the orthogonal complement of the span of those \(g_j\) occurring with nonzero coefficient in some linear dependence. Zero columns have no effect. Equality of matrices holds exactly when the nonzero columns are linearly independent.
2. **\(r\le3\):** \(X\preceq_{\mathrm{cx}}Y\) in the full multivariate sense: \(\mathbb E\phi(X)\le\mathbb E\phi(Y)\) for every finite convex \(\phi:\mathbb R^d\to\mathbb R\). There is an intermediate explicit mixture with independently rounded generator endpoints. If the nonzero columns are dependent, the inequality is strict for each strictly convex \(\phi\).
3. **\(d\le2\), every \(r\):** every one-dimensional marginal satisfies convex order. The planar proof writes the uniform zonogon marginal as a positive mixture of at most two merged uniform sums.
4. A balanced integer dual example in corank four gives a **negative fourth signed coefficient**. It obstructs a term-by-term extension of the positivity proof, **not** the unrestricted convex order or Laplace comparison. No general assertion about either is made beyond the proved regimes.

These statements concern abstract convex geometry and uniform rounding, with no claim about a specific lattice, sampler, or cryptosystem. For a lattice whose Voronoi cell is a zonotope, the statements apply if the stated generators realize that cell; the competing law is exactly the box-spline pushforward for those generators, not an arbitrary error law.

## 1. Complementary tiling, with explicit signs

For \(r=0\), \(X=Y\) in law by the change of variables. Otherwise choose a full row rank \(r\times m\) matrix \(B=[b_1\ \cdots\ b_m]\) with \(BG^\top=0\). Thus \(\ker G=\operatorname{im} B^\top\). For an \(r\)-subset \(J\), let \(v_J=|\det B_J|\), and when \(v_J>0\) set
\[
s_{J,j}=\operatorname{sgn}((B_J^{-1}h)_j),\quad j\in J,
\qquad V=\sum_{J:\ v_J>0}v_J .
\]
Here \(h\in\mathbb R^r\) is outside every proper span of at most \(r-1\) columns of \(B\). Thus all of these coefficients are nonzero. For \(I=J^c\), the parallelepiped
\[
T_J=\sum_{j\in J}s_{J,j}g_j/2+\sum_{i\in I}[-g_i/2,g_i/2]
\tag{1}
\]
is a tile, up to volume-zero overlap, and its volume fraction is \(v_J/V\).

For completeness, fix \(y\in Z\) and maximize \(\ell\cdot t\) on the box fiber \(Gt=y\), where \(B\ell=h\). The difference of two fiber points is \(B^\top z\); its change of objective is \(h\cdot z\). If the \(J\) coordinates are saturated at the prescribed endpoints, any feasible displacement \(\delta=B^\top z\) has
\[
\ell\cdot\delta=h^\top z=(B_J^{-1}h)^\top\delta_J\le0.
\]
The inequality is strict for a nonzero displacement since \(\delta_J=0\) implies \(\delta=0\). Conversely every maximizing vertex of the fiber has at least \(r\) linearly independent active coordinate constraints on \(\operatorname{im} B^\top\); otherwise it could move in a nonzero direction within the active face of the fiber. The projections of cube faces with more than \(r\) fixed coordinates have dimension less than \(d\). Off this finite null union, the maximizing vertex therefore has exactly \(r\) active coordinates \(J\), \(B_J\) invertible. Varying each active coordinate separately into the box while keeping the other \(J\) coordinates fixed proves the required signs. This also proves disjointness of tile interiors up to that null union. Finally, complementary minors of the two orthogonal row spaces satisfy \( |\det G_{J^c}|=c\,|\det B_J|\) with a fixed \(c>0\): orthonormalize each row space and take complementary minors of the resulting square orthogonal matrix; the two row-space scaling determinants are independent of \(J\). Thus tile probabilities are as stated.

Replacing \(h\) by \(-h\) reflects every tile and leaves the uniform law unchanged. In identities using the tiling one may therefore symmetrize the signs globally.

## 2. The positive rank-two quotient energy

For every independent \((r-2)\)-subset \(S\) when \(r\ge2\), define a symmetric matrix
\[
C_S=\sum_{\substack{\{j,k\}\subset[m]\setminus S\\J=S\cup\{j,k\},\,v_J>0}}
v_Js_{J,j}s_{J,k}\frac{g_jg_k^\top+g_kg_j^\top}{2}.
\tag{2}
\]
Dependent \(S\) give zero; when \(r<2\) the sum over \(S\) is empty. For any \(u\in\mathbb R^d\) put \(a_j=u^\top g_j\); then \(\sum_j a_j b_j=0\).

To compute (2), pass to the two-dimensional quotient of \(\mathbb R^r\) by \(\operatorname{span}\{b_i:i\in S\}\). Choose coordinates with \(h\) projecting to \((1,0)\). Write \((x_j,y_j)\) for the projected \(b_j\). Zero projected columns contribute nothing; all other columns have \(y_j\ne0\) by genericity of \(h\). In these coordinates
\[
v_{S\cup\{j,k\}}=D_S|x_jy_k-x_ky_j|,\qquad
s_{J,j}s_{J,k}=-\operatorname{sgn}(y_jy_k)
\]
for \(D_S>0\) constant in \(j,k\), whenever \(v_J>0\). The second equality follows by solving the two-dimensional coordinate equation for \((1,0)\), whose coefficients for \(b_j,b_k\) are respectively \(y_k/(x_jy_k-x_ky_j)\) and \(-y_j/(x_jy_k-x_ky_j)\). If \(x_j/y_j=x_k/y_k\), the first determinant vanishes and the associated pair contributes zero.

With \(t_j=x_j/y_j\), \(c_j=a_j y_j\), the projected balance gives \(\sum_j c_j=0\). Consequently
\[
u^\top C_Su
=-D_S\sum_{j<k}c_jc_k|t_j-t_k|
=D_S\int_{\mathbb R}\left(\sum_{j:t_j\le t}c_j\right)^2dt \ \ge0 .
\tag{3}
\]
Indeed \( |t_j-t_k|=\int |\mathbf 1_{t_j\le t}-\mathbf 1_{t_k\le t}|^2dt\); expanding and using the zero sum proves the identity. Compact support follows from the zero sum. Formula (3) is a conditional negative type identity for the absolute distance on a line. Notably (3) proves each \(C_S\succeq0\) separately, without a global cancellation across \(S\). Its directional kernel is also explicit: for every distinct \(t_j\), the sum of \(c_j\) over its tied group must vanish.

## 3. Sharp covariance lower term and exact kernel

On tile \(J\), \(u^\top Y\) has conditional variance \(\sum_{i\notin J}a_i^2/12\) and conditional mean \(\frac12\sum_{j\in J}s_{J,j}a_j\). The unconditional mean is zero by central symmetry of \(Z\). Variance subtraction gives
\[
\boxed{\quad
\operatorname{Cov}(Y)-\operatorname{Cov}(X)
=\frac16\sum_j p_jg_jg_j^\top+\frac1{2V}\sum_{S:\,|S|=r-2}C_S,\qquad
p_j=V^{-1}\sum_{J\ni j}v_J .
\quad}
\tag{4}
\]
Here \(p_j>0\) iff \(b_j\ne0\), since every nonzero column extends to a column basis. The latter holds iff some vector in \(\ker G=\operatorname{im}B^\top\) has nonzero \(j\)-coordinate. Since all terms in (4) are positive semidefinite, a zero directional gap implies \(a_j=0\) for every \(b_j\ne0\). Conversely this condition makes both terms zero because each summand of (2) uses two nonzero \(B\) columns. This proves the kernel claim. The factor \(1/6\) in the lower term cannot increase uniformly: when \(r=1\) there is no pair term, and, for example, two nonzero parallel segments give a nonzero gap. For an orthogonal projection of the standard cube onto a \(d\)-plane (orthonormal rows of \(G\)), (4) in particular gives \(\operatorname{Cov}(Y)\succeq I_d/12\).

## 4. Full convex order for corank at most three

Let \(R_j\) be independent fair signs, independent of all uniforms. Write \(X^{(S)}\) for the box sum in which \(U_jg_j\) is replaced by \(R_jg_j/2\) for \(j\in S\). Let \(\eta\) be the mixture of \(X^{(J)}\) using the complementary basis probabilities \(v_J/V\). For each \(J\), one replaces a centered segment uniform by its symmetric endpoints one at a time. Chord convexity and conditional expectation prove \(X\preceq_{\rm cx}\eta\) in all ranks. The comparison is strict for each strictly convex \(\phi\) if some \(g_j\ne0\) has \(p_j>0\).

For a smooth convex test \(\phi\), use commuting averaging and translation operators. For a single saturated coordinate, evaluation at \(s g_j/2\) is \(A_j+sD_j\) inside the sum, where \(A_j=(T_{g_j/2}+T_{-g_j/2})/2\) and \(D_j=(T_{g_j/2}-T_{-g_j/2})/2\). Translation acts by \(T_v\phi(x)=\phi(x+v)\). In the average of the two reflected tilings, all odd subsets of differences cancel for each tile. The empty subset gives exactly the mixture \(\eta\). For an index pair \(\{j,k\}\) the fundamental theorem of calculus twice gives
\[
D_jD_k\phi(x)
=\frac14\mathbb E\!\left[g_j^\top\nabla^2\phi(x+U_jg_j+U_kg_k)g_k\right].
\]
For \(r\le3\) no even subset larger than two exists. Group the pairs by \(S=J\setminus\{j,k\}\). After differentiation, all remaining coordinates outside \(S\) are independent uniforms, those in \(S\) are independent endpoints, and the sampled argument thus has the law of \(X^{(S)}\), independent of the two indices in that group. Hence
\[
\mathbb E\phi(Y)-\mathbb E_\eta\phi
=\frac1{4V}\sum_{S:\,|S|=r-2}
\mathbb E\!\left[\operatorname{tr}(C_S\nabla^2\phi(X^{(S)}))\right]\ge0 .
\tag{5}
\]
Positive semidefiniteness of both matrices proves the sign. Smooth approximation by convolution extends (5)'s inequality to every finite convex function: such functions are continuous on \(\mathbb R^d\) and the measures have common compact support. Strictness follows from the first comparison, as claimed. In particular this is not merely a comparison for quadratic or directional exponential tests.

## 5. Planar marginals without a corank restriction

Fix a scalar direction in dimension two and write the planar coordinates as \((x,y)\), with horizontal coordinate the chosen linear functional. Flip signs of active generators so that their horizontal lengths \(a_i>0\); vertical generators give total added section thickness \(w_0=\sum_{i:a_i=0}|(g_i)_y|\). Translate to uncentered segments \([0,g_i]\). Set \(L=\sum_{a_i>0}a_i\). Order active slopes \(s_i=(g_i)_y/a_i\) increasingly, and let \(A_j=\sum_{i\le j}a_i\). Lower boundary follows the slopes in increasing order and upper boundary in decreasing order, by linear optimization at fixed \(x\) over the coefficient box. Their difference, including the vertical segments, is
\[
w(x)=w_0+\sum_j(s_{j+1}-s_j)\big(\min(x,A_j)+\min(x,L-A_j)-x\big),\quad 0\le x\le L .
\]
For each \(b=A_j\in(0,L)\), the bracket is the length of \([0,b]\cap[x-(L-b),x]\). Dividing it by \(b(L-b)\) gives the density of the sum of independent \([0,b]\) and \([0,L-b]\) uniforms. Thus the projected uniform zonogon is a positive mixture of those sums and, when \(w_0>0\), a \([0,L]\) uniform. Centering all laws subtracts \(L/2\).

Each of these component laws dominates the original box-spline marginal in convex order by merging two groups of lengths, or all lengths. The basic merge is immediate from Jensen: for \(\ell_i\ge0\), \(L_0=\sum_i\ell_i>0\), \(\sum_i\ell_i U_i=L_0\sum_i (\ell_i/L_0)U_i\), and the expectation of a convex function is at most that for \(L_0U_1\). Merge independent groups successively. This proves planar marginal convex order, not a claim about arbitrary convex functions in two variables. In dimension one the same merge proves the full assertion for all lists.

## 6. The first higher signed term can be negative

In corank four, specialize the reflected tiling expansion to \(\phi(x)=\exp(u^\top x)\). The four-difference term, up to the positive factor \(\mathbb E e^{u^\top X}/(16V)\), is
\[
P_4=\sum_{|J|=4}v_J\prod_{j\in J}s_{J,j}a_j,\qquad a_j=u^\top g_j .
\]
A balanced example is \(a_j=1\) for all eight indices and \(B\) the matrix whose columns are the following eight rows transposed:
\[
\begin{pmatrix}
6&-3&-1&-6\\-4&1&1&-3\\0&-2&-4&6\\-3&6&5&5\\
-4&5&-1&4\\4&7&-2&-7\\2&-5&1&4\\-1&-9&1&-3
\end{pmatrix}.
\]
The columns sum to zero; choose \(\operatorname{row}(G)=\ker B\), which contains the all-ones vector and so supplies the required \(u\). For \(h=(1,0,0,0)\) all 70 determinants and all basic Cramer numerators are nonzero. Grouping bases by the number of negative signs, from 0 to 4, gives determinant masses
\[
(8344,\ 20155,\ 23033,\ 20155,\ 8344).
\]
The alternating sum is \(-589\). The included program verifies this by exact integer arithmetic. It also checks the quotient-energy and filtration identities with integer/rational inputs; it does not replace the proofs for arbitrary real inputs. This example disproves only the nonnegativity of each higher signed layer. The entire comparison also includes the endpoint mixture and positive lower layers.

## Prior geometry and reproducibility

Shephard's [Combinatorial Properties of Associated Zonotopes](https://doi.org/10.4153/CJM-1974-032-5) gives the classical parallelepiped paving framework; the fiber proof above pins down the particular signs used here. The term box spline and its pushforward interpretation follow Vergne's [A Remark on the Convolution with the Box Spline](https://doi.org/10.4007/annals.2011.174.1.19). Rademacher's [On the monotonicity of the expected volume of a random simplex](https://arxiv.org/abs/1008.3944) concerns a different comparison, inclusion of convex bodies and covariance monotonicity. These are not cited as proving (3)–(5). We do not claim an exhaustive priority search. The branch's [weighted graphical flow result](flow-lattice-voronoi-tree-transform.md) shows full Laplace comparison in every corank for a different restricted family via a determinant of balanced directed arc weights.

Run with Node.js: **node verify-zonotope-box-spline-orders.js**. The script uses only the built-in strict assertions and no proof dependencies, external data, or packages.
