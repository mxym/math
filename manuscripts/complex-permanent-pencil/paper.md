# Sharp permanent--determinant norms in three and four rows

mxym/math research project. AI-assisted manuscript, 7 October 2026.

For every complex coefficient \(\lambda\), the least constant in
\[
|\operatorname{per} A+\lambda\det A|
\le C_\lambda\prod_{i=1}^3\|A_{i\cdot}\|_2
\]
is
\[
C_\lambda=\max\{2/\sqrt3,|1+\lambda|,|1-\lambda|,
                         |\lambda+i/\sqrt3|,|\lambda-i/\sqrt3|\}.
\]
We prove this on the entire complex plane, obtain the exact coefficient lens,
classify equality for the sharp absolute-value permanent--determinant
inequality, and calculate the exact amplification and tensor product norm of
every marginal-preserving three-row permutation law. Equality outside that
absolute-value endpoint is not classified here.

The proof is a self-contained Hermitian-matrix certificate with five explicit
sharp lower witnesses. The rational interpolation checkers certify universal
polynomial identities using degree bounds explained in Section 5; the analytic
positivity and equality arguments are given in the text. No numerical optimizer
or solver output is a premise of the proof. This is a traditional proof, not a
Lean formalization.

The permanent-only endpoint is classical: E. A. Carlen, E. H. Lieb and
M. Loss, *An inequality of Hadamard type for permanents*, Methods and
Applications of Analysis 13 (2006), 1--18. The project previously proved the real
three-row endpoint in
[the robust-permanent note](../../notes/sharp-robust-permanent/paper.md), Section 9.
The complex pencil proof below does not assume the Bristiel--Caputo permanent
inequality; that result is an input to the earlier all-arity robustness note.
The present coefficient classification is a distinct three-row statement.
Part Q supplies the complete four-row tradeoff
\[
|\operatorname{per}A|+c|\det A|
\le\max\{3/2,1+c\}\prod_{i=1}^4\|A_{i\cdot}\|_2\quad(c\ge0),
\]
its full equality classification and quantitative pairwise deficit, an exact
all-column two-row symmetric--alternating spectrum, and exact four-row parity
tensor norms. It also determines the four-row pencil norm for real coefficients.
It does not assert that same pencil formula for every nonreal coefficient, or
classify every marginal-preserving four-row law. Part Q uses a self-contained
two-row Laplace/Cauchy argument; its permanent-only endpoint is classical.
No all-arity or general-exponent extension is asserted. A limited literature
screen is recorded separately and does not establish mathematical priority.


## 1. The main inequality and its sharp equality cases

Write \(\operatorname{per}A\) and \(\det A\) for the permanent and determinant of \(A\in\mathbb C^{3\times3}\), with rows \(a,b,c\), and put
\[
\rho=\frac2{\sqrt3},\qquad s=\frac2{\sqrt3}-1>0.
\]

**Theorem 1 (sharp complex inequality).** Every complex \(3\times3\) matrix satisfies
\[
\boxed{\quad
|\operatorname{per}A|+s|\det A|
\le\rho\,\|a\|_2\|b\|_2\|c\|_2.\quad}
\tag{1}
\]
The two coefficients are jointly sharp: an all-ones matrix shows that \(\rho\) cannot decrease even with the determinant term removed, and the identity matrix shows that, at the displayed \(\rho\), the positive coefficient \(s\) cannot increase.

**Theorem 2 (complete complex equality cases).** Besides matrices with a zero row, equality in (1) occurs exactly for:

- complex monomial matrices (exactly one nonzero entry in each row and column);
- matrices \(A=uv^{\mathsf T}\) of rank one, where \(u_i\ne0\) for each row and \(0<|v_1|=|v_2|=|v_3|\).

There are no restrictions on nonzero phases or row scalings. The more general exact complex coefficient classification is Theorem 1A below. In particular, the absolute-value estimate for *complex* matrices is not a formal consequence of the earlier real-matrix certificate.

## 2. Exact complex coefficient lens and Hermitian certificate

For a complex coefficient \(\lambda\), put
\[
q=|\lambda|^2,\qquad x=\operatorname{Re}\lambda,\qquad
h=\frac13-q,\quad v=2x.
\]
The **coefficient lens** is the closed region
\[
\mathcal L=\left\{\lambda\in\mathbb C:q+2|x|\le\frac13\right\}
=\left\{\lambda:|1+\lambda|\le\rho,\ |1-\lambda|\le\rho\right\}.
\tag{2a}
\]
The second equality follows by squaring the two absolute values and using \(\rho^2=4/3\).

**Theorem 1A (complete complex coefficient classification).**
For each complex \(\lambda\), the trilinear inequality
\[
\boxed{\quad
|\operatorname{per}A+\lambda\det A|
\le\rho\,\prod_{i=1}^3\|A_{i,*}\|_2
\quad\text{for every }A\in\mathbb C^{3\times3}
\quad}\tag{2b}
\]
holds **if and only if** \(\lambda\in\mathcal L\). No larger
complex coefficient domain is possible at the sharp \(\rho\).

**Necessity.** For the identity matrix,
\(\operatorname{per}I_3=\det I_3=1\) and the row-norm
product is 1, so (2b) requires \(|1+\lambda|\le\rho\).
For any odd permutation matrix, its permanent is 1 and
determinant is \(-1\), and (2b) requires \(|1-\lambda|\le\rho\).
Together these inequalities are equivalent to (2a). \(\square\)

We next prove sufficiency. For any complex \(\lambda\), expanding
in the last row gives the exact matrix identity
\[
\operatorname{per}A+\lambda\det A
=c^{\mathsf T}M_\lambda(a)b,
\quad
M_\lambda(a)=
\begin{pmatrix}
0&(1-\lambda)a_3&(1+\lambda)a_2\\
(1+\lambda)a_3&0&(1-\lambda)a_1\\
(1-\lambda)a_2&(1+\lambda)a_1&0
\end{pmatrix}.
\tag{2}
\]

**Lemma 3 (Hermitian lens certificate).** For all
\(\lambda\in\mathcal L\) and \(a\in\mathbb C^3\),
\[
M_\lambda(a)^*M_\lambda(a)
\preceq\rho^2\|a\|_2^2I_3.
\tag{3}
\]

**Proof.** Write \(\lambda=x+iy\), so \(q=x^2+y^2\).
Set \(X=|a_1|^2,Y=|a_2|^2,Z=|a_3|^2\). Since
\(\lambda\in\mathcal L\), one has \(h\ge|v|\)
and therefore \(h+v\ge0,\ h-v\ge0,\ h^2-v^2\ge0\).
The exact normalization is
\[
\rho^2=\frac43,\qquad s:=\rho-1>0,\qquad
s^2+2s=\frac13.
\tag{4}
\]

Define the Hermitian matrix
\(H=\rho^2(X+Y+Z)I_3-M_\lambda(a)^*M_\lambda(a)\).
Its diagonal entries are
\[
d_1=\rho^2X+(h+v)Y+(h-v)Z,\quad
d_2=(h-v)X+\rho^2Y+(h+v)Z,
\]
\[
d_3=(h+v)X+(h-v)Y+\rho^2Z.
\tag{5}
\]
All are nonnegative. For
\(z=1-q+2iy\), the off-diagonal entries obey
\[
H_{12}=-z\bar a_2a_1,\quad
H_{23}=-z\bar a_3a_2,\quad
H_{31}=-z\bar a_1a_3,
\quad
|z|^2=(1+q)^2-v^2,
\tag{6}
\]
with the remaining entries fixed by Hermitian symmetry.

Direct algebra gives the nonnegative-coefficient expansion
for the \(\{1,2\}\)-principal minor:
\[
\boxed{
\begin{aligned}
d_1d_2-|z|^2XY={}&
\rho^2(h-v)X^2+\rho^2(h+v)Y^2+(h^2-v^2)Z^2\\
&+2\rho^2hXY
+\bigl(\rho^2(h+v)+(h-v)^2\bigr)XZ\\
&+\bigl((h+v)^2+\rho^2(h-v)\bigr)YZ .
\end{aligned}}
\tag{7}
\]
Every term is nonnegative because \(h\ge|v|\).
The other two second-order principal minors follow by cyclic
permutation of \(X,Y,Z\).

The determinant of \(H\) satisfies
\[
\det H=d_1d_2d_3-|z|^2(d_1YZ+d_2XZ+d_3XY)
-2\operatorname{Re}(z^3)XYZ,
\tag{8}
\]
with
\(\operatorname{Re}(z^3)=(1-q)^3-12(1-q)(q-x^2)\).
For the **entire coefficient lens**, the exact rational
sum-of-nonnegative-terms identity is
\[
\boxed{
\begin{aligned}
\det H=\rho^2\bigg[
 &(h^2-v^2)\left(X^3+Y^3+Z^3-3XYZ\right)\\
+&(3h^2+v^2)\left(\sum_{i\ne j}X_i^2X_j-6XYZ\right)
\bigg],
\end{aligned}}
\tag{9}
\]
where \((X_1,X_2,X_3)=(X,Y,Z)\).
Both coefficients are nonnegative; the first cubic is
nonnegative by AM--GM, and the second is
\[
\sum_{i\ne j}X_i^2X_j-6XYZ
=(X+Y+Z)(XY+YZ+ZX)-9XYZ\ge0
\tag{10}
\]
by two more AM--GM inequalities, including boundary cases
where a variable vanishes.

All three diagonal entries, all three \(2\times2\)
principal minors, and the full determinant are nonnegative,
so the Hermitian principal-minor criterion gives \(H\succeq0\).
This proves Lemma 3. \(\square\)

Cauchy--Schwarz applied to (2)--(3) yields
\[
|\operatorname{per}A+\lambda\det A|
\le\rho\|a\|_2\|b\|_2\|c\|_2
\qquad(\lambda\in\mathcal L).
\tag{11}
\]
Together with the two permutation-matrix necessity witnesses,
this proves Theorem 1A. \(\square\)

Finally, the entire circle \(|\lambda|=s\) belongs to
\(\mathcal L\), since
\[
|\lambda|^2+2|\operatorname{Re}\lambda|
\le s^2+2s=\frac13.
\]
For any \(P,D\in\mathbb C\),
\(\max_{|\lambda|=s}|P+\lambda D|=|P|+s|D|\).
Taking \(P=\operatorname{per}A\), \(D=\det A\) in (11)
proves the absolute-value inequality (1). The disk of radius
\(s\) is the largest **centered disk** contained in the
coefficient lens; the lens itself extends much farther in the
pure-imaginary direction, reaching \(\lambda=\pm i/\sqrt3\).

The full rational identity (9), including the infinite complex
parameter scope, is certified by [check_lens.py](../../notes/complex-permanent-determinant/check_lens.py).
The original disk-specialized \(\mathbb Q(\sqrt3)\) certificate
[check.py](../../notes/complex-permanent-determinant/check.py) independently checks its specialization,
obtained by inserting \(q=s^2,h=2s,v=2x\):
\[
\det H=4\rho^2\left[(s^2-x^2)U+(3s^2+x^2)V\right],
\tag{9a}
\]
where \(U,V\) are the two nonnegative cubics in (9).
This second expression is used for the equality classification below.

## 2B. Exact norm of the permanent–determinant pencil for every complex coefficient

The preceding sharp-lens theorem answers when the best constant is at
most \(2/\sqrt3\). In fact, the same Hermitian calculus determines the
**exact optimal constant for every \(\lambda\in\mathbb C\)**, both inside
and outside that lens.

**Theorem 1B (complete complex pencil norm).** For every
\(\lambda\in\mathbb C\), the least \(C_\lambda\ge0\) such that
\[
|\operatorname{per}A+\lambda\det A|
\le C_\lambda\prod_{i=1}^3\|A_{i,*}\|_2
\qquad\text{for every }A\in\mathbb C^{3\times3}
\tag{20}
\]
is exactly
\[
\boxed{
C_\lambda=\max\left\{
\frac2{\sqrt3},\ |1+\lambda|,\ |1-\lambda|,\
\left|\lambda+\frac{i}{\sqrt3}\right|,\
\left|\lambda-\frac{i}{\sqrt3}\right|
\right\}.}
\tag{21}
\]
Each entry inside the maximum is attained by an explicit
unit-row matrix, so none is an extraneous upper-bound device.

**Proof: five sharp lower witnesses.** The all-ones matrix, normalized
so all its rows have norm one, has permanent \(2/\sqrt3\) and determinant
zero. An even permutation matrix has permanent \(1\) and determinant
\(1\), while an odd permutation matrix has permanent \(1\) and
determinant \(-1\). These establish the first three entries in (21).

For the last two, put \(a=(1,1,1)/\sqrt3\) in the exact operator
matrix (2). It is a **normal circulant matrix** with eigenvalues
\[
\frac2{\sqrt3},\quad
\frac{-1+i\sqrt3\lambda}{\sqrt3},\quad
\frac{-1-i\sqrt3\lambda}{\sqrt3}.
\tag{22}
\]
The absolute values of the last two are
\(|\lambda+i/\sqrt3|\) and \(|\lambda-i/\sqrt3|\)
(up to their order). In each case let \(b\) be the corresponding unit
Fourier eigenvector and \(c=\overline b\). Then the matrix with rows
\(a,b,c\) has unit row norms and
\(c^{\mathsf T}M_\lambda(a)b\) equal to that eigenvalue.
This realizes each of the last two entries of the maximum.
Therefore the optimal constant is at least the right side of (21).

**Proof: universal matching upper bound.** Write
\[
q=|\lambda|^2,\quad x=\operatorname{Re}\lambda,\quad
y=\operatorname{Im}\lambda,\quad
B=C_\lambda^2,\quad h=B-1-q,\quad v=2x.
\]
By the definition of \(C_\lambda\),
\[
B\ge\frac43,\qquad
B\ge1+q+2|x|,\qquad
B\ge q+\frac13+\frac{2|y|}{\sqrt3}.
\tag{23}
\]
In particular \(h\ge|v|\) and \(h^2-v^2\ge0\). The
third bound in (23) implies
\[
3(B-q)-1\ge2\sqrt3|y|\ge0,
\qquad
F:=[3(B-q)-1]^2-12y^2\ge0.
\tag{24}
\]

As in Section 2, let \(X=|a_1|^2,Y=|a_2|^2,Z=|a_3|^2\)
and form
\[
H_B=B(X+Y+Z)I_3-M_\lambda(a)^*M_\lambda(a).
\]
The diagonal and off-diagonal formulas (5)--(6) remain valid
with \(\rho^2\) replaced by \(B\) and \(h=B-1-q\).
Thus its diagonal entries are
\[
d_1=BX+(h+v)Y+(h-v)Z,\quad
d_2=(h-v)X+BY+(h+v)Z,\quad
d_3=(h+v)X+(h-v)Y+BZ.
\tag{25}
\]
They are all nonnegative. Its \(\{1,2\}\) principal minor is
\[
\begin{aligned}
d_1d_2-|z|^2XY={}&
B(h-v)X^2+B(h+v)Y^2+(h^2-v^2)Z^2\\
&+2BhXY+
\bigl(B(h+v)+(h-v)^2\bigr)XZ\\
&+\bigl((h+v)^2+B(h-v)\bigr)YZ\ge0,
\end{aligned}
\tag{26}
\]
where \(z=1-q+2iy\); the other two principal minors are its
cyclic analogues. The coefficients are all nonnegative by (23).

The determinant admits a more general **exact rational SOS decomposition**.
Write the two nonnegative cubic forms
\[
U=X^3+Y^3+Z^3-3XYZ\ge0,
\qquad
V=(X+Y+Z)(XY+YZ+ZX)-9XYZ\ge0.
\]
Then, with no restriction on the symbolic parameters \(B,q,x\)
for the identity itself,
\[
\boxed{
\begin{aligned}
\det H_B={}&
B(h^2-v^2)U+B(3h^2+v^2)V\\
&+(3B-4)\Big([3(B-q)-1]^2-12(q-x^2)\Big)XYZ .
\end{aligned}}
\tag{27}
\]
Here \(q-x^2=y^2\). Every term in (27) is nonnegative:
the first two by \(B>0,h\ge|v|\), and the last by
\(3B-4\ge0\) and \(F\ge0\) from (24). Thus \(\det H_B\ge0\).

All seven principal minors of the Hermitian \(3\times3\)
matrix \(H_B\) are nonnegative. By the principal-minor
criterion, \(H_B\succeq0\), equivalently
\[
\|M_\lambda(a)b\|_2^2\le
B\|a\|_2^2\|b\|_2^2
\quad\text{for all }a,b\in\mathbb C^3.
\]
Using (2) and complex Cauchy--Schwarz in the last row gives
(20) with \(C_\lambda=\sqrt B\), as required. Combined with
the five explicit lower witnesses, this proves Theorem 1B.
\(\square\)

**Exact independent verification.** The two polynomial identities
(26) and (27), each of degree at most three separately in
\(X,Y,Z,B,q,x\), are certified in
[check_full_norm.py](../../notes/complex-permanent-determinant/check_full_norm.py) over \(\mathbb Q\).
It compares both sides at all \(4^6=4096\) rational nodes
and applies iterated polynomial interpolation to establish
each identity for *every* choice of those six symbolic variables.
The proof of the sign conditions (23)--(24), the seven-minor
criterion and the five lower witnesses is written above.
The checker thus does **not** infer a general theorem from
a numerical scan over \(\lambda\).

**Examples and consequences.** For real \(t\), (21) becomes
\[
C_t=\max\left\{\frac2{\sqrt3},1+|t|\right\};
\tag{28}
\]
indeed \(|t\pm i/\sqrt3|^2=t^2+1/3<
(1+|t|)^2\). For \(t=iy\) purely imaginary,
\[
C_{iy}=\max\left\{\frac2{\sqrt3},
\sqrt{1+y^2},\ |y|+\frac1{\sqrt3}\right\}.
\tag{29}
\]
In particular, Theorem 1A follows again:
\(C_\lambda\le2/\sqrt3\) holds if and only if the two
even/odd permutation-matrix bounds
\(|1\pm\lambda|\le2/\sqrt3\) hold; these imply the Fourier
bounds through \(q+2|x|\le1/3\).
The largest centered coefficient disk is still the disk
of radius \(s=2/\sqrt3-1\), which yields the sharp
absolute-value inequality (1).

Theorem 1B does **not** assert the equality classification
for every \(\lambda\) outside the lens; Theorem 2 describes
all equality matrices for the sharp *absolute-value*
inequality (1). Nor does the formula cover higher matrix
orders or exponents other than the Euclidean row norm.

## 3. Proof of the equality classification

Assume no row is zero and equality holds in (1). Choose \(|\lambda|=s\) realizing the maximum in (11). Equality throughout forces \(H\) singular, so \(\det H=0\). Let
\[
U=X^3+Y^3+Z^3-3XYZ,\quad
V=(X+Y+Z)(XY+YZ+ZX)-9XYZ.
\]
Both are nonnegative, while \(3s^2+x^2>0\); therefore (9a) forces \(V=0\). If all of \(X,Y,Z\) are positive, equality in the two AM–GM inequalities gives \(X=Y=Z\). If some are zero, the explicit polynomial
\(V=\sum_{i\ne j}X_i^2X_j-6XYZ\) vanishes only if at most one coordinate is nonzero. In that one-sparse case \(U>0\), and (9a) also forces \(s^2-x^2=0\), hence \(\lambda=\pm s\) is real.

If \(X=Y=Z=r^2>0\), multiply columns by suitable unimodular factors to arrange \(a=(r,r,r)\). Both sides of (1) are unchanged. The matrix \(M_\lambda(a)\) in (2) is circulant with Fourier eigenvalues
\[
2r,\quad(-1+i\sqrt3\lambda)r,\quad(-1-i\sqrt3\lambda)r.
\]
The last two have modulus at most \((1+\sqrt3s)r=(3-\sqrt3)r<2r\). Thus the top right and left singular spaces are uniquely spanned by \((1,1,1)\). Equality in Cauchy–Schwarz and (11) forces \(b\) and \(c\) to be constant rows after the same column dephasing. Hence \(A=uv^{\mathsf T}\) with \(|v_1|=|v_2|=|v_3|>0\).

Otherwise \(a\) has one nonzero coordinate. After a column permutation and a possible sign flip of the maximizing \(\lambda\), write \(a=(r,0,0)\) and \(\lambda=s\). The only nonzero entries of \(M_\lambda(a)\) are \(M_{23}=(1-s)r\) and \(M_{32}=(1+s)r\). Since \(s>0\), its unique top right and left singular directions are the relevant coordinate vectors. Equality forces \(b,c\) to be supported on the two other columns, so \(A\) is monomial.

Conversely, direct substitution gives equality for the two listed nonzero classes. This proves Theorem 2. \(\square\)

## 4. Sharp robustness for complex-valued permutation functions

Let \(\nu\) be a probability law on \(S_3\) with uniform one-point marginals. Every such law has the form
\[
\nu_t(\pi)=\frac16+t\,\operatorname{sgn}(\pi),\quad
|t|\le\frac16,\quad \|\nu_t-u\|_{\rm TV}=3|t|.
\tag{12}
\]
Indeed, every even permutation and every odd permutation agree at exactly one position; their masses sum to \(1/3\) by the uniform marginal equation. This implies all even masses coincide, all odd masses coincide, and gives (12).

Put
\(\|f\|_{2,u_3}=(\frac13\sum_{j=1}^3|f(j)|^2)^{1/2}\).

**Corollary 4 (complex exact endpoint, if and only if).**
For arbitrary complex functions \(f_1,f_2,f_3\) on \(\{1,2,3\}\), the inequality
\[
\left|\mathbb E_{\pi\sim\nu}\prod_{i=1}^3f_i(\pi(i))\right|
\le\prod_{i=1}^3\|f_i\|_{2,u_3}
\tag{13}
\]
holds for *all* such functions exactly when
\[
\boxed{\|\nu-u\|_{\rm TV}\le
\frac1{\sqrt3}-\frac12.}
\tag{14}
\]
The boundary is included.

**Proof.** For \(A_{ij}=f_i(j)\),
\[
6\,\mathbb E_{\nu_t}\prod_if_i(\pi(i))
=\operatorname{per}A+6t\det A.
\]
If \(3|t|\le s/2\), (1) bounds the modulus by \(\rho\prod\|f_i\|_{\ell^2}/6=\prod\|f_i\|_{2,u_3}\), using \(\rho 3^{3/2}=6\).

Conversely choose three indicator rows supported on the coordinates of a permutation of the more likely parity. The left side is \(1/6+|t|\), and the normalized norm product is \(3^{-3/2}\). Necessity follows:
\(|t|\le 3^{-3/2}-1/6=s/6\), equivalently (14). \(\square\)

**Equality refinement.** If none of the three rows vanishes, then at a TV distance strictly below (14), equality in (13) occurs only for rows \(f_i(j)=u_i v_j\) with \(u_i\ne0\) and a common vector satisfying \(0<|v_1|=|v_2|=|v_3|\). At the TV boundary there are additionally the permutation-indicator/monomial configurations of the favored parity. This follows from Theorem 2 and the strict gain in \(s|\det A|\) when \(|6t|<s\) and \(\det A\ne0\).

**Corollary 5 (complex tensorization with different laws).**
Let \(N\ge1\), and take independent permutations \(\pi_\ell\sim\nu_\ell\) on \(S_3\), with all one-point marginals uniform and each satisfying (14), without assuming the laws are identical. For all complex functions \(F_i:\{1,2,3\}^N\to\mathbb C\),
\[
\left|\mathbb E\prod_{i=1}^3
F_i(\pi_1(i),\dots,\pi_N(i))\right|
\le
\prod_{i=1}^3
\left(3^{-N}\sum_{x\in\{1,2,3\}^N}|F_i(x)|^2\right)^{1/2}.
\tag{15}
\]
**Proof.** Induct on \(N\). Condition on the first \(N-1\) permutations and apply (13) in the final coordinate. The conditional absolute expectation is bounded by the product of
\(G_i(x)=(\frac13\sum_j|F_i(x,j)|^2)^{1/2}\).
Taking absolute values before averaging the outer variables, then applying the induction hypothesis to the nonnegative \(G_i\), gives (15) since
\(3^{-(N-1)}\sum_xG_i(x)^2=3^{-N}\sum_{x,j}|F_i(x,j)|^2\).
This also proves the endpoint and the nonidentical-law assertion. \(\square\)

## 4B. Exact norm of every three-row permutation product, including tensor powers

The complete pencil norm also gives a sharp answer **outside** the
previously treated small-TV region, for arbitrary complex functions
and an arbitrary number of independent, nonidentically distributed
columns.

For \(|t|\le1/6\) let
\[
\nu_t(\pi)=\frac16+t\,\operatorname{sgn}(\pi),\qquad
\kappa(t)=\max\left\{1,\frac{\sqrt3}{2}(1+6|t|)\right\}.
\tag{30}
\]

**Corollary 6 (sharp amplification for every three-row law).**
For every \(|t|\le1/6\),
\[
\boxed{
\sup_{\substack{f_i:\{1,2,3\}\to\mathbb C\\
                 f_i\not\equiv0}}
\frac{\left|\mathbb E_{\nu_t}\prod_{i=1}^3f_i(\pi(i))\right|}
{\prod_{i=1}^3\|f_i\|_{2,u_3}}
=\kappa(t).}
\tag{31}
\]
In particular, the constant is identically one **exactly** for
\[
3|t|=\|\nu_t-u\|_{\mathrm{TV}}
\le\frac1{\sqrt3}-\frac12.
\]
The same formula quantifies, sharply, how much the inequality
fails beyond its optimal TV neighborhood.

**Corollary 7 (exact nonidentical-column tensor norm).**
Let \(N\ge1\) and let independent \(\pi_\ell\sim\nu_{t_\ell}\)
with arbitrary \(|t_\ell|\le1/6\). Define the normalized \(L^2\) norms
of functions on \(\{1,2,3\}^N\) as in (15). Then
\[
\boxed{
\sup_{\substack{F_1,F_2,F_3\ne0}}
\frac{
\left|\mathbb E\prod_{i=1}^3
F_i(\pi_1(i),\ldots,\pi_N(i))\right|}
{\prod_{i=1}^3\|F_i\|_{2,u_3^{\otimes N}}}
=\prod_{\ell=1}^{N}\kappa(t_\ell).
}
\tag{32}
\]
The equality is exact for each finite \(N\), not merely an
asymptotic rate or an upper estimate.

**Proof.** As in (16),
\(6\,\mathbb E_{\nu_t}\prod_i f_i(\pi(i))
=\operatorname{per}A+6t\det A\).
Use Theorem 1B with **real** \(\lambda=6t\):
by (28), \(C_{6t}=\max\{2/\sqrt3,1+6|t|\}\).
Each normalized row \(L^2\) norm is the Euclidean row norm
divided by \(\sqrt3\). Thus the optimal ratio is
\[
\frac{3^{3/2}}6C_{6t}
=\frac{\sqrt3}{2}\max\left\{\frac2{\sqrt3},
                                    1+6|t|\right\}
=\kappa(t).
\]
Both extremal types have **nonnegative witnesses**:
constant functions if \(\kappa(t)=1\), or three
indicator functions selecting any permutation of the
more likely parity if \(\kappa(t)=(\sqrt3/2)(1+6|t|)\).
This proves (31).

For arbitrary complex functions on \(N\) coordinates,
condition on the first \(N-1\) permutations and apply (31)
to the last column; by taking the modulus of the
conditional expectation, bound the remaining integrand
using the nonnegative functions
\[
G_i(x)=\left(\frac13\sum_{j=1}^{3}|F_i(x,j)|^2\right)^{1/2}.
\]
Iterate this argument over the other independent columns.
Each step incurs its *sharp* factor \(\kappa(t_\ell)\), and
the nested \(L^2\) norms collapse to the normalized
\(N\)-fold counting measure, yielding the upper bound (32).

For equality, choose for each column \(\ell\) one of the
nonnegative one-column extremizing triples
\((f_{1,\ell},f_{2,\ell},f_{3,\ell})\) just displayed and put
\(F_i(x_1,\ldots,x_N)=\prod_{\ell=1}^N f_{i,\ell}(x_\ell)\).
Independence factorizes the expectation, and the
normalized norms factorize, so the ratio is exactly
\(\prod_\ell\kappa(t_\ell)\). This proves (32). \(\square\)

These are sharp **operator norm identities**, not only
sufficient conditions for an inequality. They remain limited
to three-row laws with uniform one-point marginals, which
are exactly the even/odd mixtures (12).

## 5. Exact certificates and trust boundary

The strongest [full-pencil norm checker](../../notes/complex-permanent-determinant/check_full_norm.py) proves the rational six-variable determinant identity (27) and its second-order minor identity (26) by verifying each at \(4^6=4096\) rational interpolation points. Every polynomial has separate degree at most three in \(X,Y,Z,B,q,x\), so iterated polynomial interpolation establishes the identities globally. The analytic sign conditions (23)–(24) and the five sharp lower witnesses complete the norm theorem. This does not merely test a finite set of complex coefficients.

The [rational lens checker](../../notes/complex-permanent-determinant/check_lens.py) certifies the **full** complex-coefficient Hermitian identities (7) and (9). No approximation of the coefficient \(\lambda\) is involved: its real and squared-modulus variables \(x,q\) are left symbolic. Both sides of each identity are polynomials over \(\mathbb Q\) of degree at most three separately in the five variables \(X,Y,Z,x,q\). The checker verifies both identities at every one of \(4^5=1024\) nodes in \(\{0,1,2,3\}^5\). Repeated univariate interpolation (four roots force any degree-at-most-three polynomial to vanish) **proves the identities globally**, rather than extrapolating from finite numerical examples. The analytic lens positivity follows from \(h\ge|v|\), AM–GM and Hermitian principal-minor criteria proved above.

The separate original [sharp-disk checker](../../notes/complex-permanent-determinant/check.py) verifies the specialization (9a) at \(4^4=256\) exact nodes over \(\mathbb Q(\sqrt3)\), along with its specialized second-order minor identity. This cross-check uses an explicit pair representation of quadratic field elements, not a floating evaluation of \(\sqrt3\). Two deliberately corrupted formulas are rejected. A [third exact field-valued regression](../../notes/complex-permanent-determinant/check_matrix.py) verifies the Hermitian entries (5)–(6) against direct complex matrix multiplication for 60 rational algebraic matrix/phase pairs. This finite regression is a safeguard, not a substitute for the all-input direct-multiplication argument.

From repository root:

~~~sh
python3 notes/complex-permanent-determinant/check_full_norm.py
python3 -O notes/complex-permanent-determinant/check_full_norm.py
python3 notes/complex-permanent-determinant/check_lens.py
python3 -O notes/complex-permanent-determinant/check_lens.py
python3 notes/complex-permanent-determinant/check.py
python3 -O notes/complex-permanent-determinant/check.py
python3 notes/complex-permanent-determinant/check_matrix.py
python3 -O notes/complex-permanent-determinant/check_matrix.py
python3 notes/complex-permanent-determinant/check_tensor.py
python3 -O notes/complex-permanent-determinant/check_tensor.py
~~~

All five scripts must reproduce their respective frozen reports in both ordinary and optimized Python modes. All three checkers use the Python standard library, exact integers/rationals, no floating-point comparisons and no external solver. A separate [exact tensor regression](../../notes/complex-permanent-determinant/check_tensor.py) enumerates
960 permutation tuples for ten rational parameter vectors and
checks the sharp normalized nonnegative equality witnesses of
Corollaries 6–7. The all-dimensional tensor norm itself is proved
analytically by the induction and factorization in Section 4B;
its validity is not inferred from the finite regression.

The full mathematical proof also uses elementary AM–GM, the Hermitian principal-minor criterion, Cauchy–Schwarz, Fourier singular-value separation and tensorization as stated in Sections 2–4. The certificate does not formalize these analytic arguments in Lean, and the paper has not received independent human refereeing or historical priority certification.

### Dependencies and references

The earlier project's [real three-row endpoint proof](../../notes/sharp-robust-permanent/paper.md), Section 9, motivates the question and is credited, but the complex Hermitian certificate (5)–(10) is derived here. The classical permanent-only complex bound was proved by Carlen, Lieb and Loss, *An inequality of Hadamard type for permanents*, Methods and Applications of Analysis **13** (2006), 1–18. The broader permutation-moment context is in OpenAI/math, *A strict four-row permanent inequality and permutation moments* (26 September 2026). No claim is made about the exact complex robustness region for four or more rows, or about all exponents between the Bristiel–Caputo critical exponent and two.

## Part Q: Four-row determinant tradeoffs and parity tensor norms

## Q.1. Main theorem

For A in C^(4x4), write per A and det A for its permanent and determinant. All row norms are Euclidean.

**Theorem Q.1.** For every complex 4x4 matrix A and every real c >= 0,
\[
\boxed{
|\operatorname{per}A|+c|\det A|
\le M(c)\prod_{i=1}^4\|A_{i,*}\|_2,\qquad
M(c)=\max\{3/2,\,1+c\}.
}\ \tag{Q.1}
\]
Both branches are sharp. If all rows are nonzero, equality occurs precisely as follows:

- For 0 <= c < 1/2, A is rank one, with a common column vector whose four entries have equal nonzero modulus.
- For c = 1/2, A is either such a rank-one matrix or a complex monomial matrix.
- For c > 1/2, A is monomial.

A zero row produces trivial equality for every c. The all-1/2 matrix has unit row norms, permanent 3/2 and determinant zero. Every permutation matrix has unit row norms, permanent 1 and absolute determinant 1. These prove sharpness.

**Corollary Q.2 (complete real-coefficient pencil norm).**
For every real t,
\[
\boxed{\sup_{A:\,\prod_i\|A_{i,*}\|_2>0}
\frac{|\operatorname{per}A+t\det A|}
{\prod_i\|A_{i,*}\|_2}
=\max\{3/2,\,1+|t|\}.}\tag{Q.2}
\]
The upper bound comes from (Q.1); an even or odd permutation matrix, chosen according to the sign of t, realizes the second branch. The all-1/2 matrix realizes the first. The analogous exact norm for nonreal t in four rows is **not** claimed.

## Q.2. An infinite family of exact rectangular two-row inequalities

For n >= 2 and a,b in C^n, define
\[
S_n(a,b)=\sum_{j<k}|a_jb_k+a_kb_j|^2,\qquad
W_n(a,b)=\sum_{j<k}|a_jb_k-a_kb_j|^2.\tag{Q.3}
\]
Put U=||a||², V=||b||², E=|<a,b>|², and T=sum_j |a_j|²|b_j|², with <a,b>=sum_j a_j conjugate(b_j). Expanding the squares yields
\[
\boxed{S_n=UV+E-2T,\qquad W_n=UV-E.}\tag{Q.4}
\]
These are identities over complex numbers, not inequalities.

**Theorem Q.3 (sharp rectangular symmetric–alternating spectrum).**
For every n >= 2, c >= 0 and a,b in C^n,
\[
\boxed{
S_n(a,b)+cW_n(a,b)
\le\max\{2-2/n,\,1+c\}\|a\|_2^2\|b\|_2^2.
}\tag{Q.5}
\]
Both branches are achieved: normalized identical flat rows give 2-2/n; the disjoint coordinate rows e1,e2 give 1+c.

**Proof.** If a or b vanishes, there is nothing to prove. Otherwise normalize both to norm one. Define
\[
\eta=|\langle a,b\rangle|^2\in[0,1],\quad
\tau=\sum_j|a_j|^2|b_j|^2,\quad
\Delta_n=\tau-\eta/n\ge0,\quad c_n=1-2/n.
\]
The inequality Delta_n >= 0 is ordinary Cauchy–Schwarz on the n complex numbers a_j conjugate(b_j). Combining (Q.4) gives the **exact identity**
\[
\boxed{
S_n+cW_n=1+c+(c_n-c)\eta-2\Delta_n.
}\tag{Q.6}
\]
Because eta is between 0 and 1, the right side is at most max(1+c,2-2/n), proving (Q.5) even for c > 1.

The complete nonzero-row equality criteria are:
\[
\begin{array}{c|l}
c<c_n& a,b \text{ proportional and equimodular on all n coordinates}\\
c=c_n& a_j\overline{b_j}\text{ is independent of }j\\
c>c_n& a,b \text{ have disjoint coordinate supports}.
\end{array}\tag{Q.7}
\]
Indeed, below c_n equality needs eta=1 and Delta_n=0; above it, eta=Delta_n=0; at the transition only Delta_n=0. Equality in the Cauchy inequality defining Delta_n means the products a_j conjugate(b_j) are all the same. This proves every case. QED.

This provides an exact all-n family rather than a finite verification table. The four-column instance is especially effective because the four-row Laplace decomposition splits into equal two-column pieces.

## Q.3. Two-row Laplace method for the four-row inequality

Normalize A's four nonzero rows and call them a,b,d,e. For each two-column subset J={j,k} with j<k define
\[
p_{ab}(J)=a_jb_k+a_kb_j,\qquad
w_{ab}(J)=a_jb_k-a_kb_j.
\]
Let J^c denote the complementary two columns. The standard permanent and determinant Laplace expansions are, exactly,
\[
\operatorname{per}A=\sum_{|J|=2}p_{ab}(J)p_{de}(J^c),\qquad
\det A=\sum_{|J|=2}\varepsilon_J w_{ab}(J)w_{de}(J^c),
\tag{Q.8}
\]
where epsilon_J is the sign of the column shuffle (J,J^c). The complement map permutes the six two-column subsets. Cauchy–Schwarz gives
\[
|\operatorname{per}A|\le\sqrt{S_4(a,b)S_4(d,e)},\qquad
|\det A|\le\sqrt{W_4(a,b)W_4(d,e)}.\tag{Q.9}
\]
Applying two-dimensional Cauchy–Schwarz to the last two bounds,
\[
\begin{aligned}
|\operatorname{per}A|+c|\det A|
&\le\sqrt{S_4(a,b)S_4(d,e)}
+c\sqrt{W_4(a,b)W_4(d,e)}\\
&\le\sqrt{F_c(a,b)F_c(d,e)},\qquad
F_c(x,y):=S_4(x,y)+cW_4(x,y).
\end{aligned}\tag{Q.10}
\]
Theorem Q.3 with n=4 bounds each F_c by M(c). Scaling the rows back proves (Q.1). The explicit sharpness matrices in Section Q.1 prove the constant cannot decrease. QED.

## Q.4. Quantitative rigidity and all equality matrices

**Theorem Q.4 (explicit pairwise deficit).**
For a complex 4x4 matrix with four nonzero rows, normalize its rows to unit length. For each row pair i<j set
\[
\eta_{ij}=|\langle a_i,a_j\rangle|^2,\qquad
\Delta_{ij}=\sum_{k=1}^{4}|a_{ik}|^2|a_{jk}|^2-\eta_{ij}/4\ge0.
\]
Define
\[
\delta_{ij}(c)=
\begin{cases}
(1/2-c)(1-\eta_{ij})+2\Delta_{ij},&0\le c\le1/2,\\
(c-1/2)\eta_{ij}+2\Delta_{ij},&c\ge1/2.
\end{cases}\tag{Q.11}
\]
Then
\[
\boxed{
M(c)-\frac{|\operatorname{per}A|+c|\det A|}
{\prod_i\|A_{i,*}\|_2}
\ge\frac16\sum_{1\le i<j\le4}\delta_{ij}(c).
}\tag{Q.12}
\]
For any specific pairing {i,j} disjoint union {k,l} of all four row labels, the right side may be replaced by (delta_ij+delta_kl)/2.

**Proof.** By (Q.6) with n=4, F_c(a_i,a_j)=M(c)-delta_ij(c). Apply (Q.10) after permuting rows into the selected pairing:
\[
\frac{|\operatorname{per}A|+c|\det A|}{\prod_i\|A_{i,*}\|_2}
\le\sqrt{(M-\delta_{ij})(M-\delta_{kl})}
\le M-\frac{\delta_{ij}+\delta_{kl}}2,
\]
where the last step is AM–GM. Average the inequalities for the three perfect matchings of four row labels; each unordered pair occurs once. QED.

**Proof of the equality classification in Theorem Q.1.**
Equality forces all six nonnegative deltas in (Q.12) to vanish.

When c<1/2, all row-pair inner products have modulus one, so every pair of unit rows is proportional. The vanishing of Delta for any pair then forces all four coordinate moduli equal to 1/2. The matrix is rank one with a common equimodular column vector.

When c>1/2, all eta_ij=Delta_ij=0. Equality in the underlying Cauchy inequality then says each product a_{ik} conjugate(a_{jk}) vanishes. The supports of the four nonzero rows are pairwise disjoint subsets of four columns; hence each is a distinct singleton. This is precisely the monomial class.

When c=1/2, all Delta_ij=0. Therefore for every distinct pair of rows i,j the product
\[
a_{ik}\overline{a_{jk}}=z_{ij}\tag{Q.13}
\]
is independent of column k. If no pair of row supports intersects, the rows are monomial. Otherwise some z_ij is nonzero, forcing both corresponding rows to have full column support. Every other nonzero row intersects one of these full-support rows, hence also has full support. All z_ij are then nonzero. For any three distinct rows i,j,h and any column k,
\[
|a_{ik}|^2=\frac{|z_{ij}|\,|z_{ih}|}{|z_{jh}|},\tag{Q.14}
\]
which is independent of k. Every normalized row is therefore equimodular (modulus 1/2). Equation (Q.13) relative to any fixed reference row now forces every row to be a scalar multiple of that row; the matrix is rank one. The two classes listed in Theorem Q.1 really attain equality at c=1/2, completing the proof. QED.

Inequality (Q.12) is a quantitative near-extremizer statement without asserting an optimal global distance modulus. Below c=1/2 it forces almost parallel/equimodular row pairs; above c=1/2 it forces nearly disjoint coordinate supports.

**An exact interpolation and quadratic deficit.** Let \(J_4\) be the
all-ones matrix and set \(B_t=(1-t)I_4+tJ_4\) for \(0\le t\le1\).
Every row has squared norm \(1+3t^2\), and direct expansion gives
\[
\operatorname{per}B_t=1+6t^2+8t^3+9t^4,\qquad
\det B_t=(1-t)^3(1+3t)=1-6t^2+8t^3-3t^4.
\]
Both are nonnegative on this interval. At the critical weight \(c=1/2\)
the normalized deficit has the exact form
\[
\boxed{
\frac32-
\frac{|\operatorname{per}B_t|+\frac12|\det B_t|}
{(1+3t^2)^2}
=\frac{6t^2(1-t)^2}{(1+3t^2)^2}.}\tag{Q.14a}
\]
Thus the gap vanishes at the monomial and rank-one endpoints
and is strictly positive in between, quadratically near either
endpoint. The polynomial identity in (Q.14a) is also checked by the
formal exact checker. This example does not by itself prove a
universal optimal distance-to-extremizers modulus.

## Q.5. Exact parity-biased S4 norm and tensorization

Let u be uniform on the symmetric group S4. For real t with |t| <= 1/24 define
\[
\nu_t(\pi)=1/24+t\,\operatorname{sgn}(\pi).\tag{Q.15}
\]
There are twelve permutations of each parity; for every fixed i,j exactly three even and three odd permutations send i to j. Thus nu_t has **uniform one-point marginals**, and
\[
\|\nu_t-u\|_{\rm TV}=12|t|.\tag{Q.16}
\]
This is a one-parameter parity subfamily, not the space of all uniform-marginal S4 laws.

For complex f on {1,2,3,4}, let
\(\|f\|_{2,u_4}=(\frac14\sum_j|f(j)|^2)^{1/2}\).

**Corollary Q.5 (sharp parity-law norm).** For every |t| <= 1/24,
\[
\boxed{
\sup_{f_1,\dots,f_4\ne0}
\frac{\left|\mathbb E_{\pi\sim\nu_t}\prod_{i=1}^4 f_i(\pi(i))\right|}
{\prod_i\|f_i\|_{2,u_4}}
=\kappa(t):=\max\{1,\tfrac23(1+24|t|)\}.
}\tag{Q.17}
\]
Consequently the normalized complex L2 inequality with constant one holds throughout this parity family **if and only if**
\[
\boxed{\|\nu_t-u\|_{\rm TV}\le1/4.}\tag{Q.18}
\]
The boundary is included; beyond it the exact optimal amplification factor grows linearly and reaches 4/3 at |t|=1/24.

**Proof.** For A_ij=f_i(j), one has
\(24\mathbb E_{\nu_t}\prod_i f_i(\pi(i))=\operatorname{per}A+24t\det A\).
Each normalized row L2 norm is half its Euclidean norm, so their product is 1/16 of the Euclidean product. Corollary Q.2 with the **real** coefficient 24t gives the exact norm
\((16/24)M(|24t|)=\kappa(t)\).
Constant rows realize the first branch. For the second branch, take indicator rows selecting a permutation of the more likely parity: its probability is 1/24+|t|, and the normalized product of row norms is 1/16. Equation (Q.16) gives the iff radius (Q.18). QED.

**Corollary Q.6 (exact nonidentical-column tensor norm).**
For any N>=1 let independent permutations \(\pi_\ell\sim\nu_{t_\ell}\) with arbitrary |t_l|<=1/24. For arbitrary complex functions \(F_i:\{1,2,3,4\}^N\to\mathbb C\) use normalized counting L2 norms. Then
\[
\boxed{
\sup_{F_1,\dots,F_4\ne0}
\frac{\left|\mathbb E\prod_{i=1}^4
F_i(\pi_1(i),\dots,\pi_N(i))\right|}
{\prod_{i=1}^4\|F_i\|_{2,u_4^{\otimes N}}}
=\prod_{\ell=1}^N\kappa(t_\ell).
}\tag{Q.19}
\]
**Proof.** Induct on N. Condition on the first N-1 permutations and apply (Q.17) to the final column, obtaining the product of the nonnegative conditional L2 functions
\(G_i(x)=(\frac14\sum_j|F_i(x,j)|^2)^{1/2}\).
Take the modulus before averaging the outer permutations; apply the induction hypothesis to the nonnegative G_i. Their normalized squared L2 norms telescope to those of F_i.

For sharpness, at each column choose constant row functions or four permutation-indicator row functions, according to the maximizing branch of kappa(t_l). Take products across columns for each row. Independence factors both the expectation and the normalized norms; the resulting ratio is exactly the right side of (Q.19). QED.

## Q.6. Scope, exact checking, and prior work

The [exact certificate](../../notes/four-row-permanent-tradeoff/check.py) verifies (Q.4) for n=4 as a universal integer-polynomial identity treating the formal conjugates as independent variables. It also verifies both Laplace identities (Q.8) as universal polynomial equalities in all sixteen matrix entries. This is coefficient comparison, not evaluating a random finite grid. Rational arithmetic checks the flat/monomial witnesses, parity counts, exact TV formula and seven rational t instances. The all-n rectangular theorem is proved algebraically in Section Q.2, not inferred from finite cases.

Reproduce with standard-library Python:

~~~sh

python3 -B notes/four-row-permanent-tradeoff/check.py
python3 -B -O notes/four-row-permanent-tradeoff/check.py

~~~

The reports must match each other and [the frozen replay](../../notes/four-row-permanent-tradeoff/results/replay.txt). The analytic Cauchy–Schwarz, stability and tensor arguments are contained in this paper; they are not replaced by the finite checker.

The classical sharp permanent-only complex row-norm bound of Carlen, Lieb and Loss, *An inequality of Hadamard type for permanents* (2006), [arXiv:math/0508096](https://arxiv.org/abs/math/0508096), has constant n!/n^(n/2), equal to 3/2 at n=4. The present elementary argument recovers its four-row case while retaining the **sharp determinant term** and complete equality/deficit information. The earlier [three-row complex pencil norm](../../notes/complex-permanent-determinant/PAPER.md) treats three rows by a different Hermitian method. The four-row setting is related to [OpenAI/math's strict four-row permanent and permutation moment manuscript](https://github.com/openai/math/blob/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/02-permanent.tex), but no improvement in the full Thorp-shuffle mixing time is claimed.

The exact **nonreal** four-row pencil norm remains unclassified. The tradeoff (Q.1) is not claimed for five or more rows. The radius (Q.18) applies **only** to parity-mixture S4 laws, not arbitrary uniform-one-point-marginal measures on S4. No novelty/priority certification, human referee review or full proof-assistant formalization is asserted.