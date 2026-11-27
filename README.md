# The binary ranks in Hyun–Kwon–Wang–Wu Open Problem 7 need not agree

**Result.** The proposed equality is false. The ranks are \((29,30)\)
for an explicit pair in eight variables, the smallest possible dimension
for a counterexample. In every dimension \(m=8,16,24,\ldots\) our family
has
\[
  \operatorname{rank}_2(TD_h)=2+2m+2\binom{m/2}{2},\qquad
  \operatorname{rank}_2(D_{g,h})=1+2m+2\binom{m/2}{2}.
\]
For every admissible pair the two ranks differ by at most one, always
with \(D_{g,h}\) of lower or equal rank. The proof gives an exact test
for the drop, and equality whenever \(h\) has degree at most three.
The proof is independent of computation or an external catalogue.

## 1. Exact question and notation

Jong Yoon Hyun, Jieun Kwon, Jiaxin Wang, and Yansheng Wu,
[*Designs, linear codes, plateaued functions, and their interconnections*,
arXiv:2605.24355v1](https://arxiv.org/abs/2605.24355v1), May 2026:
[§IV-A, p. 5](https://arxiv.org/pdf/2605.24355v1#page=5); [Theorem 10 and Open Problem 7, p. 17](https://arxiv.org/pdf/2605.24355v1#page=17).
On \(V=\mathbb F_2^m\), Theorem 10 requires \(g,h,g+h\) bent and
\((g+h)^*=g^*+h^*\) pointwise, where the dual is defined by
\(W_f(a)=\sum_{z\in V}(-1)^{f(z)+a\cdot z}=2^{m/2}(-1)^{f^*(a)}\).
The problem proposes equal binary ranks for the matrices
\[
 T_{b,z}=h(z+b),\qquad
 A_{b,z}=g(b)+h(z+b)+(g+h)(z).
\]
Rows are indexed by all blocks \(b\in V\), columns by all points \(z\in V\).
These are the original incidence matrices of \(TD_h\) and \(D_{g,h}\),
not their dephased cores. The rank convention is over \(\mathbb F_2\).
For our family \(h^*(0)=0\), so both original designs have the same
parameters, including the same choice of block size.

## 2. Exact rank comparison for any nonconstant \(h\)

Put \(f_0(z)=f(z)+f(0)\) for any Boolean \(f\), and let
\[
 B_{b,z}=h(b+z)+h(b)+h(z)+h(0).
\]
It is symmetric, has zero first row and column (index \(0\)), and is
alternating. Write \(C\) for \(B\) restricted to nonzero indices.
By symmetry \(\operatorname{Row}C=\operatorname{Col}C\), identifying
rows and columns as coordinate vectors; we insert a zero at coordinate
0 to view this as a space of functions on \(V\). This space is denoted \(U_h\); its elements are sums
of normalized first differences of \(h\). If \(\deg h=d>0\), all
elements of \(U_h\) have degree at most \(d-1\). In particular
\(h_0\notin U_h\).

For either matrix \(T,A\), add row 0 to every other row, then add
column 0 to every other column. Both operations are involutions and
preserve rank. Explicitly for an original matrix \(M\), its
\((b,z)\) entry with \(b,z\ne0\) becomes
\(M_{b,z}+M_{0,z}+M_{b,0}+M_{0,0}\), which is \(B_{b,z}\)
for either \(T\) or \(A\). A nonzero-index entry on a margin has
just \(M_{0,0}\) added; the corner is unchanged. The resulting
matrices, with margin vectors displayed only on nonzero indices, are
\[
 T'\!=\!\begin{pmatrix}h(0)&h_0^\top\\ h_0&C\end{pmatrix},\qquad
 A'\!=\!\begin{pmatrix}0&g_0^\top\\ (g+h)_0&C\end{pmatrix}.
\]
For a matrix \(\begin{pmatrix}c&v^\top\\u&C\end{pmatrix}\), if
\(u\notin\operatorname{Col} C\), its first column adds one independent
column to the other columns. The other columns have rank
\(\operatorname{rank} C + [v^\top\notin\operatorname{Row} C]\):
projection onto their bottom coordinates gives the column space of
\(C\), and adds a one-dimensional kernel exactly when there exists
\(a\in\ker C\) with \(v^\top a\ne0\). Equivalently \(v^\top\notin
\operatorname{Row} C\). If it is only \(v^\top\) that is outside, transpose.
Since \(g_0+(g+h)_0=h_0\notin U_h\), at least one of the two margins of
\(A'\) is outside. Consequently
\[
 \operatorname{rank}_2(T)=\operatorname{rank}_2 C+2,\quad
 \operatorname{rank}_2(A)=
 \operatorname{rank}_2(T)-[\,g_0\in U_h\ \text{or}\ (g+h)_0\in U_h\,].
 \tag{1}
\]

## 3. An infinite counterexample family

Let \(s\ge2\) be even, let \(d=2s\), and identify \(Y=\mathbb F_4^s\)
with \(\mathbb F_2^d\) using \(1,\omega\) in each coordinate, where
\(\omega^2+\omega+1=0\). Use \(z=(x,y)\in
\mathbb F_2^d\times Y\), \(m=2d=4s\), with the ordinary binary coordinate
dot product. Define
\[
 e(y)=\sum_{j=1}^s {\bf1}_{y_j\ne0}\in\mathbb F_2,\quad
 P(y)=\omega y+e(y)y,\qquad g(x,y)=x\cdot y,\quad h(x,y)=x\cdot P(y).
\]
The function \(e\) is constant on each nonzero \(\mathbb F_4\)-line
orbit. On that orbit \(P\) multiplies by either \(\omega\) or
\(\omega^2\), whereas \(P+I\) uses the other multiplier. Both fix zero.
Thus \(P,P+I\) are permutations, \(P+I=P^{-1}\), and
\(P^{-1}+(P+I)^{-1}=I\) as pointwise sums of maps. For any permutation
\(Q\) of the binary \(d\)-space, summing over \(x\) in the Walsh
transform of \(x\cdot Q(y)\) leaves only \(y=Q^{-1}(a)\), so
\[
 W_{x\cdot Q(y)}(a,b)=2^d(-1)^{b\cdot Q^{-1}(a)}.
\]
Taking \(Q=I,P,I+P\) proves the three bent conditions and the precise
dual identity in Theorem 10. Their Walsh values at zero are all \(2^d\).

For each coordinate \(j\), let \(a_j,b_j\) be the directions \(1,\omega\)
in that coordinate (zero elsewhere), and write \(E_j\) for the coordinate
projection onto that plane, including it back in \(Y\).
For any \(y\), varying just that coordinate through the four elements
gives
\[
 \Delta_{a_j}\Delta_{b_j} P(y)=(I+E_j)y.
\]
Indeed the sum of all four vectors in the plane is zero. The constant
contribution to \(e\) from the other coordinates therefore sums to zero,
as does the linear \(\omega y\) contribution. The indicator in the
varied coordinate is 1 at the three nonzero values; summing those three
vectors leaves the other coordinates once and the varied coordinate
zero. Summing this identity over \(j\) gives \(y\), since \(s\) is even
and \(\sum_j E_j=I\). With the same shifts in the \(y\)-half of \(V\),
\[
 g=\sum_{j=1}^s \Delta_{a_j}\Delta_{b_j}h
   =\sum_{j=1}^s (B_{a_j,\bullet}+B_{b_j,\bullet}+B_{a_j+b_j,\bullet}).
\]
The second equality follows by expanding each difference; the margin
terms vanish because \(h(0,y)=0\) for all \(y\). Thus \(g=g_0\in U_h\),
and (1) proves a rank drop of exactly one in the original matrices.

## 4. Exact ranks

For clarity, use \(y_1,\ldots,y_d\) for the binary coordinates from
now on, and set \(\Omega=\sum_{i=1}^s y_{2i-1}y_{2i}\). The indicator
on a binary pair is \(u+v+uv\); thus the degree-four part of \(h\) is
\[
 H_4=\sum_{j=1}^d x_j\wedge y_j\wedge\Omega .
\]
Here the wedge records top-degree squarefree products, in the exterior
algebra over \(\mathbb F_2\) (repeated variables vanish, no sign changes).
This part is nonzero since \(s\ge2\).

Express \(T_{b,z}=h(b+z)\) as the matrix of coefficients in the two
Boolean monomial bases for \(b\) and \(z\). The evaluation matrices are
invertible: indexed by subsets, these are inclusion matrices with
unit diagonal ordered compatibly with inclusion. Thus this change
preserves rank. In the resulting matrix, the block of bidegree
\((i,j)\) vanishes for \(i+j>4\); the blocks with \(i+j=4\) depend
only on \(H_4\).

* Blocks \((0,4),(4,0)\) have rank 1.
* Blocks \((1,3),(3,1)\) have rank \(m\). Their maps are first
  contractions of \(H_4\). Contractions in the \(x\)-coordinates
  give \(u\wedge\Omega\) for binary linear forms \(u\) on \(Y\). For
  any nonzero coefficient on \(y_j\) in \(u\), use a paired wedge
  disjoint from \(j\); the coefficient on that resulting triple is
  nonzero and has no other source. So this map is injective.
  A contraction in a nonzero \(y\)-direction \(a\) has, for any
  \(a_j=1\), \(x_j\)-coefficient \(\Omega+y_j\wedge\iota_a\Omega\),
  where \(\iota_a\) denotes insertion of \(a\) into an alternating form.
  This is nonzero: the alternating matrix of \(\Omega\) has rank
  \(d\ge4\), while that of a wedge of two linear forms has rank at most
  2. The \(x\)- and \(y\)-contractions have different \(x\)-degrees,
  so their images are independent.
* The block \((2,2)\) has rank \(2\binom d2\). It has zero rows
  and columns for two \(x\)-variables (there is only one \(x\)
  in any term of \(H_4\)). The remaining nonzero pieces are
  transpose maps between mixed \(xy\) pairs and pure \(yy\) pairs.
  A mixed contraction on \(x_j\) and \(y_a\) gives
  \(\delta_{a,j}\Omega+y_j\wedge y_{\bar a}\), where \(\bar a\)
  is the other coordinate in the \(a\)-pair. For any two distinct
  nonpartner \(j,k\), take \(a=\bar k\) to obtain
  \(y_j\wedge y_k\). For partner pairs this yields the paired
  wedge plus \(\Omega\). On the \(s\)-dimensional span of paired
  wedges these \(s\) columns form \(I+J\), \(J\) the all-ones
  matrix. Since \(s\) is even, \(J^2=0\) over \(\mathbb F_2\)
  and \(I+J\) is invertible. Hence the mixed-to-pure map is
  surjective, proving the claimed rank.

The degree-four columns are supported only on the degree-zero row,
so split off one pivot, clearing that row by column operations.
Degree-four rows now split off one pivot at degree-zero column;
clearing that column by row operations affects no remaining block.
Next, degree-three columns are supported only on degree-one rows; the
\((1,3)\) block has full row rank. Use its pivots to eliminate those
rows, with no changes to degree-two or degree-three rows. The
transpose argument removes degree-one columns, using pivots in
degree-three rows whose other remaining entries are zero. What is
left is only the block \((2,2)\), unchanged. Therefore
\(\operatorname{rank}_2 T=2+2m+2\binom d2\); apply (1) for \(A\).
At \(s=2\) this gives \(T=30\) and \(A=29\); the padded normalized
core has rank 28. The actual \(m=8\) design parameters are \((256,120,56)\).

## 5. Why eight variables are minimal

If \(h\) is quadratic then every element of \(U_h\) is affine,
whereas \(g\) and \(g+h\) are bent and non-affine on positive even
dimension. If \(h\) is cubic and \(f\in U_h\), its degree-two part is
a sum of contractions of the squarefree cubic form of \(h\) by
the first-difference directions. By linearity it is the contraction
by the vector \(a\) equal to their sum. Explicitly, its polar form
on \((b,c)\) is the alternating trilinear form obtained by polarizing
the cubic part, evaluated on \((a,b,c)\). This follows term by term
on squarefree cubic monomials: the quadratic part of a difference is
the sum of the three terms formed by deleting one variable and
multiplying by its component of the difference direction. Thus the
polar form has \(a\) in its radical if \(a\ne0\), and is zero if
\(a=0\). A quadratic with a nonzero radical direction has a constant
derivative in that direction, so it is not bent: pairing \(x\) with
\(x+a\) makes the Walsh transform vanish at frequencies for which the
character sign is opposite the derivative sign. Affine functions are
not bent either. This proves equality in (1) for degree at most three.

For even \(m\ge4\) the degree of a bent function is at most \(m/2\).
Indeed, a monomial coefficient of size \(k>m/2\) is the parity of the
truth table on its coordinate \(k\)-plane \(W\). The sum of the signs
on \(W\), by Walsh orthogonality, is
\(2^{k-m/2}\sum_{a\in W^\perp}(-1)^{h^*(a)}\). This is divisible
by four when \(k\ge m/2+2\), and also when \(k=m/2+1\) since
\(|W^\perp|\) is even in that case. The corresponding weight is even.
It follows that \(m=4,6\) cannot admit a counterexample. At \(m=2\)
no admissible triple exists: the only possible bent top monomial is
the single quadratic monomial and it cancels in the sum. Odd \(m\)
cannot give Boolean bent functions (or, using the definition in the
source, the dimension is already required to be even). Hence \(m=8\)
is the smallest possible counterexample dimension in the original
positive-dimensional design setting.

## 6. Scope, prior work, and replay

The structural setting and the problem are from Theorem 10 and Open
Problem 7 in the linked preprint. Its Example 4 is a different
eight-variable pair; that pair has both ranks 30, so does not test
the inequality above. The statement proved here is a negative answer
to the proposed universal equality; it does not assert that every
admissible pair has a rank drop or that every dimension \(m\ge8\)
admits one.

The separate older results on [binary ranks of Maiorana–McFarland
translation designs](https://doi.org/10.1007/s11425-007-0167-4) and
[normalized Hadamard matrices and switching](https://doi.org/10.1016/j.disc.2018.11.022)
give useful context. They do not establish the rank change between
the two original incidence matrices in Theorem 10. The
[September 2026 preprint by Wu, Wang, and Hyun](https://arxiv.org/abs/2609.13968)
addresses the separate Polujan–Pott isomorphism question for
translation designs. Literature checks through 27 November 2026
used the exact title and arXiv number, author combinations, Open
Problem 7 and Theorem 10, and binary rank/switching terminology;
no resolution of the same question was found in the primary sources
located. This is not a categorical priority claim about the particular
permutation or the elementary tools used.

Run with Python 3.10+ (standard library only; no data downloads):
```sh
python3 verify_direct.py
python3 verify_coefficients.py
```
The first checks the exact theorem hypotheses by direct character sums
and both original incidence matrices at \(m=8\); it also checks all
point-pair and block-pair incidences. The second uses polynomial-basis expansion,
an independent binary elimination routine, and the explicit binary
pair formulas for \(m=8,16,24,32\). Neither is a substitute for the
all-parameter proof above.
