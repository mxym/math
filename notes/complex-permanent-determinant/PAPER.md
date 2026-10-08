# A sharp complex permanent–determinant inequality in three rows

**Research note, 8 October 2026.** Complete written proof and exact algebraic certificate. The prior [robust permanent manuscript](../sharp-robust-permanent/paper.md), Section 9, established the real trilinear inequality and the sharp nonnegative three-row radius. This note proves the complex strengthening, the **complete sharp complex coefficient lens**, and all complex equality cases for the absolute-value inequality. This is AI-assisted research, not human peer review or a literature-wide priority determination.

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
parameter scope, is certified by [check_lens.py](check_lens.py).
The original disk-specialized \(\mathbb Q(\sqrt3)\) certificate
[check.py](check.py) independently checks its specialization,
obtained by inserting \(q=s^2,h=2s,v=2x\):
\[
\det H=4\rho^2\left[(s^2-x^2)U+(3s^2+x^2)V\right],
\tag{9a}
\]
where \(U,V\) are the two nonnegative cubics in (9).
This second expression is used for the equality classification below.

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

## 5. Exact certificates and trust boundary

The primary [rational lens checker](check_lens.py) certifies the **full** complex-coefficient Hermitian identities (7) and (9). No approximation of the coefficient \(\lambda\) is involved: its real and squared-modulus variables \(x,q\) are left symbolic. Both sides of each identity are polynomials over \(\mathbb Q\) of degree at most three separately in the five variables \(X,Y,Z,x,q\). The checker verifies both identities at every one of \(4^5=1024\) nodes in \(\{0,1,2,3\}^5\). Repeated univariate interpolation (four roots force any degree-at-most-three polynomial to vanish) **proves the identities globally**, rather than extrapolating from finite numerical examples. The analytic lens positivity follows from \(h\ge|v|\), AM–GM and Hermitian principal-minor criteria proved above.

The separate original [sharp-disk checker](check.py) verifies the specialization (9a) at \(4^4=256\) exact nodes over \(\mathbb Q(\sqrt3)\), along with its specialized second-order minor identity. This cross-check uses an explicit pair representation of quadratic field elements, not a floating evaluation of \(\sqrt3\). Two deliberately corrupted formulas are rejected. A [third exact field-valued regression](check_matrix.py) verifies the Hermitian entries (5)–(6) against direct complex matrix multiplication for 60 rational algebraic matrix/phase pairs. This finite regression is a safeguard, not a substitute for the all-input direct-multiplication argument.

From repository root:

~~~sh
python3 notes/complex-permanent-determinant/check_lens.py
python3 -O notes/complex-permanent-determinant/check_lens.py
python3 notes/complex-permanent-determinant/check.py
python3 -O notes/complex-permanent-determinant/check.py
python3 notes/complex-permanent-determinant/check_matrix.py
python3 -O notes/complex-permanent-determinant/check_matrix.py
~~~

Each script must reproduce its own frozen report in both ordinary and optimized Python modes. All three checkers use the Python standard library, exact integers/rationals, no floating-point comparisons and no external solver. The full mathematical proof also uses elementary AM–GM, the Hermitian principal-minor criterion, Cauchy–Schwarz, Fourier singular-value separation and tensorization as stated in Sections 2–4. The certificate does not formalize these analytic arguments in Lean, and the paper has not received independent human refereeing or historical priority certification.

### Dependencies and references

The previous project's [real three-row endpoint proof](../sharp-robust-permanent/paper.md), Section 9, motivates the question and is credited, but the complex Hermitian certificate (5)–(10) is derived here. The classical permanent-only complex bound was proved by Carlen, Lieb and Loss, *An inequality of Hadamard type for permanents*, Methods and Applications of Analysis **13** (2006), 1–18. The broader permutation-moment context is in OpenAI/math, *A strict four-row permanent inequality and permutation moments* (26 September 2026). No claim is made about the exact complex robustness region for four or more rows, or about all exponents between the Bristiel–Caputo critical exponent and two.