# Three-row collision energies and permanent–determinant tradeoffs

**Research note, October 2026.** Theorems below hold over the complex field and for **every indicated n**, not just checked small instances. The sharp unrestricted six-row critical case is NOT claimed.

## 1. Setup, bosonic identity and Gram invariants

Let \(U\in\mathbb C^{3\times n}\) have rows \(u,v,w\), where \(n\ge3\).
Set
\[
S_n(U)=\sum_{|J|=3}|\operatorname{per}(U_J)|^2,\qquad
W_n(U)=\sum_{|J|=3}|\det(U_J)|^2=\det(UU^*).
\tag{1}
\]
The last equality is complex Cauchy–Binet. Separate row homogeneity allows normalization \(\|u\|=\|v\|=\|w\|=1\), provided no row vanishes (in which case the desired inequalities are trivial). All final bounds rescale by the product of the three squared row norms. Throughout \(\langle x,y\rangle=\sum_i x_i\overline y_i\), linear in the first argument.

Define
\[
a=\langle u,v\rangle,\quad b=\langle v,w\rangle,\quad d=\langle w,u\rangle,\quad
s=|a|^2+|b|^2+|d|^2,\quad t=\Re(abd).
\tag{2}
\]
By Cauchy–Schwarz and arithmetic–geometric mean,
\[
0\le s\le3,\qquad t\le |abd|\le(s/3)^{3/2}\le s/3.
\tag{3}
\]
Direct Gram expansion gives
\[
\operatorname{per}(UU^*)=1+s+2t,\qquad W_n(U)=1-s+2t.
\tag{4}
\]

**Lemma 1 (bosonic collision identity).** Let
\(F(z)=(\sum_j u_jz_j)(\sum_jv_jz_j)(\sum_jw_jz_j)
=\sum_{|\alpha|=3}c_\alpha z^\alpha\). Then
\[
\operatorname{per}(UU^*)=\sum_{|\alpha|=3}\alpha!|c_\alpha|^2,\quad
S_n(U)=\sum_{\alpha\in\{0,1\}^n,|\alpha|=3}|c_\alpha|^2.
\tag{5}
\]
Consequently \(\Delta_n=\operatorname{per}(UU^*)-S_n(U)\ge0\),
and for three nonzero rows, \(\Delta_n=0\) exactly when the three row
supports are pairwise disjoint.

**Proof.** Write \(u_1=u,u_2=v,u_3=w\). The squared norm of
\(\frac1{\sqrt6}\sum_{\sigma\in S_3}
u_{\sigma(1)}\otimes u_{\sigma(2)}\otimes u_{\sigma(3)}\)
is \(\operatorname{per}(UU^*)\): expand and reindex the pairs of
permutations. For any ordered coordinate triple with multiplicities
\(\alpha\), its tensor coefficient equals \(\alpha!c_\alpha/\sqrt6\).
There are \(6/\alpha!\) triples of that multiplicity, proving the first
formula. The squarefree polynomial coefficients are precisely the
three-column permanents, giving the second. Equality means that
\(F\) has degree at most one in each variable. The polynomial ring is
an integral domain, so the degree in \(z_j\) of a product of nonzero
linear factors equals the number of its factors that contain \(z_j\).
Thus equality holds precisely for pairwise disjoint row supports. QED.

## 2. Sharp all-width high-determinant branch

**Theorem 2.** For every \(n\ge3\), every complex \(3\times n\)
matrix \(U\), and every real \(c\ge5\),
\[
\boxed{S_n(U)+cW_n(U)\le
(1+c)\|u\|^2\|v\|^2\|w\|^2.}
\tag{6}
\]
The coefficient is sharp. If no row vanishes, equality holds if and
only if the supports of \(u,v,w\) are pairwise disjoint.

**Proof.** For normalized rows, by (3)–(5),
\[
S_n+cW_n\le (1+s+2t)+c(1-s+2t)
\le 1+c+\frac{5-c}{3}s\le1+c.
\tag{7}
\]
Distinct coordinate rows attain equality. For \(c>5\), equality in the
last inequality forces \(s=0\), and equality in Lemma 1 then requires
disjoint supports. For \(c=5\), if \(s>0\), equality in
\(|abd|\le(s/3)^{3/2}\le s/3\) requires \(s=3\). Thus the three rows
are parallel, but their polynomial \(F\) has a nonzero \(z_j^3\)
coefficient, so Lemma 1 is strict. Hence \(s=0\) also for \(c=5\).
Conversely any three disjoint-support normalized rows have
\(S_n=W_n=1\). QED.

The threshold 5 is **only a proven sufficient threshold**, not
asserted optimal. In particular this theorem does not reach the
six-row critical weight \(7/3\).

## 3. Exact all-width flat-modulus Pareto envelope

Put
\[
A_n=1-\frac6n+\frac{12}{n^2},\quad
B_n=1-\frac4n,\quad
C_n=\frac{6(n-1)(n-2)}{n^2},\quad
d_n=C_n-A_n=5-\frac{12}{n}.
\tag{8}
\]
A normalized three-row matrix is **equimodular** when every entry has
modulus \(n^{-1/2}\). Phases are arbitrary.

**Theorem 3.** For every \(n\ge3\), every equimodular complex
\(3\times n\) matrix \(U\), and every real \(c\ge0\),
\[
\boxed{S_n(U)+cW_n(U)\le\max\{C_n,A_n+c\}.}
\tag{9}
\]
The bound is attained at both endpoints for every \(n\).
Equality, allowing independent row and column phases, is exactly:
- when \(c<d_n\): three parallel equimodular rows;
- when \(c=d_n\): three parallel rows or three mutually orthogonal rows;
- when \(c>d_n\): three mutually orthogonal equimodular rows.

Parallel flat rows attain \(C_n\); three rows of the normalized
\(n\times n\) Fourier matrix attain \(A_n+c\). In particular for
\(n=6,c=7/3\), (9) gives \(S_6+(7/3)W_6\le10/3\)
within the equimodular class, with equality only for parallel rows.

**Proof.** For \(j\ne k\), the coefficient of \(z_j^2z_k\) in
\(F\) is \(u_jv_jw_k+u_jw_jv_k+v_jw_ju_k\). Set
\(q_j=u_jv_jw+u_jw_jv+v_jw_ju\). Since
\(q_j(j)=3u_jv_jw_j\), (5) gives the **exact** collision formula
\[
\Delta_n=2\sum_j\|q_j\|^2-12\sum_j|u_jv_jw_j|^2.
\tag{10}
\]
For equimodular rows, each diagonal square sum in
\(\sum_j\|q_j\|^2\) contributes \(1/n\).
The three conjugate cross terms contribute respectively
\(2|a|^2/n,2|b|^2/n,2|d|^2/n\).
For example, summing the cross term between the first two
summands of \(q_j\) yields
\(\sum_j|u_j|^2v_j\overline w_j\langle w,v\rangle
=|\langle v,w\rangle|^2/n\).
Also \(\sum_j|u_jv_jw_j|^2=1/n^2\). Therefore
\[
\Delta_n=\frac6n+\frac{4s}{n}-\frac{12}{n^2}.
\tag{11}
\]
Equations (4) and (11) give the **exact identities**
\[
S_n(U)=A_n+B_ns+2t,\qquad W_n(U)=1-s+2t.
\tag{12}
\]
Write \(x=\sqrt{s/3}\in[0,1]\). By (3),
\[
S_n+cW_n\le A_n+c+3(B_n-c)x^2+2(1+c)x^3=:f_c(x).
\tag{13}
\]
For \(x>0\), \(f'_c(x)=6x\{B_n-c+(1+c)x\}\).
The term in braces is strictly increasing in \(x\). Thus
\(f_c\) is either increasing or first decreasing and then increasing,
so its maximum occurs at \(x=0\) or \(x=1\).
Here \(f_c(0)=A_n+c\) and \(f_c(1)=C_n\).
Both are attained by the stated explicit flat frames.

For \(c<d_n\) the unique maximizing endpoint is \(x=1\),
forcing \(s=3\), i.e. parallel normalized rows by equality in
Cauchy–Schwarz. For \(c>d_n\) it is \(x=0\), forcing
\(s=0\), i.e. orthogonal rows. At \(c=d_n\),
\[
f_{d_n}(x)=C_n-6(B_n+1)x^2(1-x),\qquad B_n+1=2-4/n>0,
\tag{14}
\]
so no interior \(0<x<1\) can be an equality case. QED.

**Corollary 4.** The exact phase-independent straight-line frontier
for this subclass is
\[
\boxed{S_n(U)+(5-12/n)W_n(U)\le6(n-1)(n-2)/n^2,}
\tag{15}
\]
with exactly parallel flat or mutually orthonormal flat equality.
It is *not* asserted for arbitrary modulus profiles.

## 4. Coordinate-row boundary face, all widths

**Proposition 5.** Suppose \(u=e_j\), \(v',w'\) are the restrictions
of the other two rows to the \(n-1\) columns different from \(j\),
and \(m=n-1\). Then
\[
S_n(U)+cW_n(U)=S_m^{(2)}(v',w')+cW_m^{(2)}(v',w')
\le\max\{2-2/m,1+c\}\|v'\|^2\|w'\|^2.
\tag{16}
\]
In particular at \(n=6,c=7/3\), the sought critical bound holds
for **all** complex matrices with a coordinate row.
Nonzero equality occurs precisely when all three row supports are
pairwise disjoint; they need not be singletons.

**Proof.** Laplace expansion along row \(e_j\) kills all three-column
minors not containing \(j\), and the remaining minors reduce to
two-row minors on the other columns. For normalized two-row vectors
\(p,q\), let \(h=\langle p,q\rangle\) and \(Q=\sum_i|p_iq_i|^2\).
The degree-two version of (5) gives
\(S_m^{(2)}=1+|h|^2-2Q\), while
\(W_m^{(2)}=1-|h|^2\).
Cauchy–Schwarz yields \(Q\ge|h|^2/m\), hence
\[
S_m^{(2)}+cW_m^{(2)}
\le1+c+(1-c-2/m)|h|^2
\le\max\{2-2/m,1+c\}.
\]
Rescale to arbitrary rows. At \(c=7/3>1-2/5\), equality
requires \(h=0,Q=0,\|v'\|=\|w'\|=1\); therefore \(v,w\)
vanish at column \(j\) and have disjoint supports. Conversely this
configuration attains the bound. QED.

## 5. Exact Johnson-incidence lifting for one flat row

For \(u=f=(1,\ldots,1)/\sqrt n\) and arbitrary complex \(v,w\), define
\(y_{\{i,j\}}=v_iw_j+v_jw_i\). Let \(B\) be the triangle–edge
incidence matrix, \(B_{T,e}={\bf1}_{e\subseteq T}\).

**Theorem 6.** For every \(n\ge3\),
\[
\boxed{S_n(f,v,w)=n^{-1}\|By\|_2^2.}
\tag{17}
\]
For \(n\ge4\), the exact full orthogonal spectrum of \(B^*B\) is
\[
\begin{array}{c|c}
\text{eigenvalue}&\text{multiplicity}\\\hline
3(n-2)&1\\
2(n-3)&n-1\\
n-4&n(n-3)/2.
\end{array}\tag{18}
\]
For \(n=3\), the third eigenspace is absent and the two eigenvalues
are 3 and 0 (multiplicities 1 and 2). In particular,
\(S_n(f,v,w)\le3(n-2)\|y\|_2^2/n\).
An arbitrary flat first row reduces to \(f\) by column phase changes.

**Proof.** Laplace expansion of a three-column permanent along
\(f\) gives \(\operatorname{per}(U_T)=n^{-1/2}\sum_{e\subseteq T}y_e\),
so (17) follows. Let \(C\) be the vertex–edge incidence matrix.
Counting triangles containing one or two edges gives
\(B^*B=(n-4)I+C^*C\).
Also \(CC^*=(n-2)I+J\), where \(J\) is the \(n\times n\)
all-ones matrix. Its eigenvalues are \(2(n-1)\) once
and \(n-2\) with multiplicity \(n-1\). The rank of \(C\)
is \(n\) for \(n\ge3\). Thus \(C^*C\) also has a zero
eigenspace of dimension \(\binom n2-n\), yielding (18).
The operator norm proves the final bound. QED.

## 6. The unresolved six-row critical case

The previously established balanced-Laplace reduction
(see the reference note below) would prove the sharp complex
six-row permanent–determinant tradeoff if the *general*
three-by-six rectangular estimate
\[
\boxed{S_6(U)+(7/3)\det(UU^*)\stackrel{?}{\le}10/3
\quad\text{for every normalized }U\in\mathbb C^{3\times6}}
\tag{19}
\]
were established. This research note does **not** prove (19).
Theorem 3 covers arbitrary phases at flat moduli, and Proposition 5
covers the coordinate-row face; Theorem 2 covers all-row weights
\(c\ge5\), which is insufficient.

For normalized rows and the collision deficit
\(\Delta=\operatorname{per}(UU^*)-S_6(U)\), (4) gives the exact identity
\[
S_6+(7/3)W_6-10/3=(4/3)(5t-s)-\Delta.
\tag{20}
\]
Thus the **unproved proposed collision inequality**
\[
\Delta\stackrel{?}{\ge}(8/3)t
\tag{21}
\]
is a *sufficient* condition for the complete critical result,
because \(3t\le s\). On the flat-modulus class it follows
from (11), \(s=3x^2,t\le x^3\), and
\(1+3x^2-4x^3=(1-x)(4x^2+x+1)\ge0\).
The missing step is a global phase-and-modulus collision estimate,
not a finite numerical optimization.

A tempting stronger shortcut,
\(9S_6\le5\operatorname{per}(UU^*)+4\det(UU^*)\),
is **false**. Take
\(u=w=(0,1,1,1,1,1)/\sqrt5\) and \(v=e_1\).
Then \(S_6=8/5\), \(\operatorname{per}(UU^*)=2\),
\(\det(UU^*)=0\), hence
\(9S_6-5\operatorname{per}(UU^*)-4\det(UU^*)=22/5>0\).
This is an exact algebraic counterexample, not a heuristic.

## 7. Dependencies, replay and scope

The all-even balanced Laplace transfer and the bosonic coefficient
identity previously appeared in the companion
[even-row transfer note](../../notes/four-row-permanent-tradeoff/EVEN_ROW_TRANSFER.md).
The present argument develops the complete sharp flat-modulus envelope,
the all-width sufficient high-weight branch, the coordinate boundary
and the incidence spectrum; each has its own proof above.
The classical permanent-only norm theorem is due to
E. Carlen, E. Lieb and M. Loss,
*An Inequality of Hadamard Type for Permanents* (2006),
arXiv:math/0508096.

The standard-library checker independently enumerates original
permanent/determinant minors for finite Gaussian-rational examples,
verifies the exact formula (12), the case distinctions in (9),
the coordinate reduction (16) and the explicit false-shortcut
witness. It uses no floating-point arithmetic, random optimizer or
external solver. Its finite checks are NOT a substitute for Sections
1–5, which prove the infinite statements mathematically.
No novelty priority, external peer-review, or Lean formalization is
claimed; the general critical six-row claim remains open.
