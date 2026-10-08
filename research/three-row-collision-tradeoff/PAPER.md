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
Theorem 7 below extends the critical result to any matrix with
**at least two separately equimodular rows**, with no restriction
on the third row. Proposition 5 covers the coordinate-row face;
Theorem 2 covers all-row weights
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

## 8. Sharp collision inequality with only **two** equimodular rows

The preceding full flat-modulus optimization assumed that **all three**
rows have constant coordinate moduli. We now remove that condition
entirely from the **third** row in the critical six-column dimension.
This gives a more substantial portion of the conjectured (19) and,
unlike a numerical search, provides a rigorous all-complex proof.

**Theorem 7 (two-flat-row collision theorem; sharp constant).**
Suppose \(U\in\mathbb C^{3\times6}\) has two rows whose respective
six coordinate moduli are equal (the two common moduli need not
coincide). The third row is **arbitrary**. Then, with the notation
of (2) and (5) for normalized nonzero rows,
\[
\boxed{\quad
\Delta_6(U)\ge \frac83\,\Re\!\left(
\langle u,v\rangle\langle v,w\rangle\langle w,u\rangle
\right).\quad}
\tag{22}
\]
Both sides scale by the product of row squared norms, so the statement
also holds without normalization. The constant \(8/3\) is **best
possible** for this class; with three nonzero rows, equality occurs
**only** when the rows are parallel and equimodular.

**Corollary 8 (full critical tradeoff on the two-flat-row locus).**
For all matrices under Theorem 7,
\[
\boxed{\quad
S_6(U)+\frac73\det(UU^*)
\le\frac{10}{3}\|u\|^2\|v\|^2\|w\|^2.\quad}
\tag{23}
\]
Apart from a zero row, equality occurs precisely for three parallel
equimodular rows. In particular, **the third row is not required to be
equimodular or nonvanishing in every coordinate** for (23).

The proof is organized so its only nontrivial sign claim reduces to
a factored identity in two real scalar variables.

### 8.1. The exact two-flat collision formula

After row normalization and a permutation of the rows, assume \(u,v\)
are the two equimodular rows. Multiplying each column by a unimodular
scalar leaves every squared permanent minor, Gram invariant and
determinant minor unchanged. We may therefore arrange
\[
u=f=\frac1{\sqrt6}(1,\ldots,1),\qquad
v=\frac1{\sqrt6}(r_1,\ldots,r_6),\quad |r_j|=1.
\tag{24}
\]
Multiplying \(v\) by a scalar of modulus one, arrange further that
\[
m:=\frac16\sum_{j=1}^6r_j\in[0,1]\text{ is real},\qquad
\langle u,v\rangle=m.
\tag{25}
\]
The vector \(w\in\mathbb C^6\) is entirely unrestricted and need not be
normalized in the intermediate quadratic-form argument.

**Lemma 9.** Under (24)--(25),
\[
\boxed{\displaystyle
\Delta_6(f,v,w)=\frac23\left(
\|w\|^2+|\langle w,f\rangle|^2
+|\langle w,v\rangle|^2
+m\sum_{j=1}^6\Re(r_j)|w_j|^2\right).}
\tag{26}
\]

**Proof.** Apply the exact collision identity (10) to the rows
\(f,v,w\). In the intermediate expression
\(\sum_j\|q_j\|^2\), the terms quadratic in \(w\) can be
collected without assuming anything about the moduli of its entries.
For arbitrary normalized \(u,v\), let
\(a=\langle u,v\rangle\) and \(p_j=|u_j|^2,q_j=|v_j|^2\).
Direct expansion of (10), grouping the diagonal and off-diagonal
coordinate products, yields
\[
\begin{aligned}
\Delta_n(u,v,w)
={}&2\Big(\sum_jp_jq_j\Big)\|w\|^2
+2\sum_j(p_j+q_j)|w_j|^2
-12\sum_jp_jq_j|w_j|^2\\
&+4\sum_j\Re(u_j\overline{v_j}\,\overline a)|w_j|^2
+4\Re\!\left(
\langle (p_jv_j)_j,w\rangle\,
\overline{\langle v,w\rangle}
+\langle(q_ju_j)_j,w\rangle\,
\overline{\langle u,w\rangle}\right).
\end{aligned}
\tag{27}
\]
This formula is an equality in complex arithmetic. When both
\(u,v\) have modulus \(1/\sqrt6\), we have
\(p_j=q_j=1/6\) and \(\sum p_jq_j=1/6\);
the coefficient of \(\sum|w_j|^2\) from the first line is
\(2/6+4/6-12/36=2/3\). The last line's two inner-product
terms become \((2/3)(|\langle v,w\rangle|^2+
|\langle u,w\rangle|^2)\), while the remaining diagonal
term becomes \((2/3)m\sum_j\Re(r_j)|w_j|^2\).
This is exactly (26). QED.

### 8.2. Positive-definite rank-one comparison

Put
\[
\beta=\langle w,v\rangle,\qquad
d=\langle w,f\rangle,\qquad
a_j=1+m\Re(r_j),\qquad z=v-2mf.
\tag{28}
\]
Since \(t=m\Re(d\overline\beta)\), completing a scalar square
in (26) gives the exact identity
\[
\boxed{\displaystyle
\frac32\left(\Delta_6-\frac83t\right)
=\sum_{j=1}^6a_j|w_j|^2
+|\langle w,z\rangle|^2
-(4m^2-1)|\langle w,f\rangle|^2.}
\tag{29}
\]

If \(0\le m\le1/2\), then \(a_j\ge1-m>0\) and
\(4m^2-1\le0\), proving (22), strictly for nonzero \(w\).
If \(m=1\), all \(r_j=1\), so \(v=f,z=-f,a_j=2\);
the right side of (29) is
\[
2\big(\|w\|^2-|\langle w,f\rangle|^2\big)\ge0,
\tag{30}
\]
with equality precisely when \(w\) is proportional to \(f\).

It remains to treat \(1/2<m<1\). Write
\(D=\operatorname{diag}(a_1,\ldots,a_6)\) and
\(H=D+zz^*\). All \(a_j\ge1-m>0\), so \(H\)
is positive definite. By the weighted Cauchy--Schwarz inequality,
\[
|\langle w,f\rangle|^2
\le\langle f,H^{-1}f\rangle\,\langle w,Hw\rangle.
\tag{31}
\]
It therefore suffices to prove
\[
(4m^2-1)\langle f,H^{-1}f\rangle\le1.
\tag{32}
\]

Define three scalars
\[
A=\frac16\sum_j\frac1{a_j},\qquad
B=\frac16\sum_j\frac{r_j-2m}{a_j},\qquad
C=\frac16\sum_j\frac{|r_j-2m|^2}{a_j}.
\tag{33}
\]
The rank-one inverse identity (obtained by directly multiplying
\(D+zz^*\) by
\(D^{-1}-D^{-1}zz^*D^{-1}/(1+z^*D^{-1}z)\))
gives **exactly**
\[
\langle f,H^{-1}f\rangle=A-\frac{|B|^2}{1+C}
\le A-\frac{(\Re B)^2}{1+C}.
\tag{34}
\]
Let \(x_j=\Re(r_j)\). From (25), \(\sum_j x_j/6=m\),
and \(a_j=1+mx_j\). The identity
\(mx_j/a_j=1-1/a_j\) yields
\[
\frac16\sum_j\frac{x_j}{a_j}=\frac{1-A}{m}.
\]
Using \(|r_j|=1\) in the definitions of \(B,C\),
\[
\boxed{\quad
\Re B=\frac{1-(1+2m^2)A}{m},\qquad
1+C=(5+4m^2)A-3>0.\quad}
\tag{35}
\]

Substitute (35) into the desired estimate (32). The difference
between 1 and its **stronger** upper bound factorizes as
\[
\begin{aligned}
&1-(4m^2-1)
\left(
A-\frac{[1-(1+2m^2)A]^2}
{m^2[(5+4m^2)A-3]}
\right)\\
&\hspace{20pt}=
\boxed{\displaystyle
\frac{(1-m^2)\,[1+(2m-1)A]\,[(2m+1)A-1]}
{m^2[(5+4m^2)A-3]}.}
\end{aligned}
\tag{36}
\]
Equation (36) is an elementary polynomial identity after
clearing its positive denominator; an independent integer-polynomial
checker is included in the companion code.

Every factor on the right is **strictly positive** for
\(1/2<m<1\): the denominator is positive by (35),
\(1-m^2>0\), \(1+(2m-1)A>0\), and Jensen's
inequality for the convex function \(x\mapsto1/(1+mx)\)
gives
\[
A\ge\frac{1}{1+m(6^{-1}\sum_jx_j)}
=\frac1{1+m^2},
\qquad
(2m+1)A-1
\ge\frac{2m-m^2}{1+m^2}>0.
\tag{37}
\]
Combining (34)--(37) proves (32) **with strict inequality**.
Then (31) proves (29) nonnegative, strictly for nonzero \(w\).
This completes the proof of Theorem 7. Sharpness occurs at
\(u=v=w=f\), where \(\Delta_6=8/3\), \(t=1\);
(30) proves the only nonzero equality class.

**Proof of Corollary 8.** For normalized nonzero rows,
(20), Theorem 7 and (3) give
\[
S_6+\frac73 W_6-\frac{10}{3}
=\frac43(5t-s)-\Delta_6
\le\frac43(3t-s)\le0.
\tag{38}
\]
An equality case in (38) must attain equality in Theorem 7,
and hence all rows are parallel and equimodular. Conversely,
that family has \(S_6=10/3,W_6=0\).
The statement with arbitrary row norms follows by homogeneity,
and a zero row is a trivial equality case. QED.

**Research boundary.** The proof treats all complex matrices with
at least **two separately equimodular rows**, including wildly
nonflat third rows. It does not establish the collision bound (21)
or critical tradeoff (19) when **none or only one** of the
three rows has constant coordinate moduli. Numerical eigenvalue
experiments outside the proved locus are discovery-only.

## 9. Sharp six-row permanent–determinant norm on a broad structural class

The two-flat rectangular theorem is strong enough to settle the
original **six-by-six matrix inequality**, with exactly the conjectured
global best coefficient, on a class with a large number of otherwise
unconstrained complex entries. The class includes *both* anticipated
global extremizer types.

Call a nonzero row of length six **flat** if its six coordinate
moduli are all equal, and **coordinate** if it is supported on one
column. A triple of rows is **certified** if it contains either
(a) at least two flat rows, or (b) at least one coordinate row.
No restriction is placed on the other rows in that triple.

**Theorem 10 (sharp six-row structured partition theorem).**
Let \(A\in\mathbb C^{6\times6}\). Suppose its six rows admit a
partition into two certified triples. Then for **every real \(c\ge0\)**,
\[
\boxed{\quad
|\operatorname{per}A|+c|\det A|
\le\max\left\{\frac{10}{3},1+c\right\}
\prod_{i=1}^6\|A_{i,*}\|_2.\quad}
\tag{39}
\]
The constant is **best possible even inside this structured class**:
for \(c\le7/3\) take the matrix all of whose entries are \(1/\sqrt6\);
for \(c\ge7/3\) take any complex monomial matrix with unit-modulus
nonzero entries. The theorem applies in particular to each of the
following cases:
1. at least **four flat rows**, with the other two rows arbitrary;
2. at least **two coordinate rows**, with the other four rows arbitrary;
3. at least **one coordinate row and two other flat rows**, with the
   remaining three rows arbitrary.

The assumption is **sufficient, not necessary**. No claim of the
unrestricted six-row inequality or a global classification of
non-extremizing matrices is made.

**Proof.** A zero row gives the zero-equals-zero case. Normalize
all nonzero rows separately. Choose the certified row partition
\(R\sqcup R^c=[6]\) with \(|R|=|R^c|=3\), and set \(U=A_R\),
\(V=A_{R^c}\). By Theorem 7 / Corollary 8 and Proposition 5,
each certified triple obeys
\[
S_6(U)+\frac73 W_6(U)\le\frac{10}{3},
\qquad
S_6(V)+\frac73 W_6(V)\le\frac{10}{3}.
\tag{40}
\]
The balanced Laplace permanent and determinant expansions, together
with Cauchy--Schwarz on complementary three-column subsets, yield
\[
\begin{aligned}
|\operatorname{per}A|+\frac73|\det A|
&\le\sqrt{S_6(U)S_6(V)}
       +\frac73\sqrt{W_6(U)W_6(V)}\\
&\le\sqrt{\left(S_6(U)+\frac73W_6(U)\right)
          \left(S_6(V)+\frac73W_6(V)\right)}\\
&\le\frac{10}{3}.
\end{aligned}
\tag{41}
\]
The middle inequality is Cauchy--Schwarz in \(\mathbb R^2\).
The first is precisely the column-complement matching in the
balanced-Laplace lemma; all signs in the determinant are immaterial
inside the absolute values.

For \(0\le c\le7/3\), discard the nonnegative term
\((7/3-c)|\det A|\) from the left side of (41).
For \(c\ge7/3\), apply Hadamard's determinant inequality
\(|\det A|\le1\) to obtain
\[
|\operatorname{per}A|+c|\det A|
\le\frac{10}{3}+\left(c-\frac73\right)=1+c.
\]
This proves the piecewise right side of (39), and row homogeneity
restores the product of norms.

To verify the three advertised sufficient patterns, place two of
four flat rows into each triple; or put one of two coordinate rows
in each triple; or place the one coordinate row into one triple
and the two flat rows into the other. Fill the unused slots
arbitrarily. The explicit normalized constant matrix has
permanent \(6!/6^3=10/3\) and determinant zero. A permutation
matrix has absolute permanent and determinant equal to one.
Both admit certified partitions, proving **the exact sharpness of
(39) within its stated class** at every weight. QED.

**Scope for the full six-row problem.** Theorem 10 is a completed
**sharp six-row inequality on a substantial structural subclass**,
not merely a numerical special-case verification. To extend it
to all complex six-by-six matrices it remains necessary to
prove the unrestricted rectangular critical estimate (19),
or to find a different global inequality circumventing that step.

## 10. A Gram-only certificate and a full-dimensional six-row region

The sharp six-row statement is also provable for an explicit
**full-dimensional open set** of complex matrices, rather than only
the algebraic flat/coordinate loci. This observation uses the
**sign** of the cycle term in (20) and needs no optimizer.

For three arbitrary (not necessarily normalized) rows \(u,v,w\),
write \(G=UU^*\), \(P=G_{11}G_{22}G_{33}\),
\[
Q=|G_{12}|^2G_{33}+|G_{23}|^2G_{11}+|G_{31}|^2G_{22},
\qquad
T=\Re(G_{12}G_{23}G_{31}).
\tag{42}
\]
Define the **Gram screen** by the polynomial inequality \(5T\le Q\).
It is computable without normalization, square roots or solving
any polynomial system.

**Theorem 11 (unrestricted three-row Gram certificate).**
For every complex \(U\in\mathbb C^{3\times6}\), not necessarily
flat and allowing zero coordinates, if \(5T\le Q\), then
\[
\boxed{S_6(U)+\frac73\det(UU^*)\le\frac{10}{3}P.}
\tag{43}
\]
For three nonzero rows, a sufficient condition is
\[
|\langle\widehat u,\widehat v\rangle|^2+
|\langle\widehat v,\widehat w\rangle|^2+
|\langle\widehat w,\widehat u\rangle|^2
\le\frac{27}{25},
\tag{44}
\]
where hats denote unit row normalizations. In particular it suffices
that the absolute correlation of **each** row pair is at most \(3/5\).

**Proof.** The Gram permanent and determinant obey
\(\operatorname{per}G=P+Q+2T\) and
\(\det G=P-Q+2T\). Lemma 1 gives
\(\Delta=\operatorname{per}G-S_6\ge0\). Hence the following
identity holds **without row normalization**:
\[
\boxed{\displaystyle
S_6+\frac73\det G-\frac{10}{3}P
=\frac43(5T-Q)-\Delta.}
\tag{45}
\]
The Gram screen makes both terms on its right nonpositive,
proving (43). To prove (44), for normalized rows let
\(s=|a|^2+|b|^2+|d|^2\); by (3),
\(t\le(s/3)^{3/2}\le s/5\) whenever \(s\le27/25\).
This is exactly \(5T\le Q\) after restoring norms. The uniform
correlation bound \(3/5\) implies \(s\le3(3/5)^2=27/25\). QED.

**Corollary 12 (sharp six-row inequality on an open coherence region).**
The conclusion (39) holds for every complex \(6\times6\) matrix whose
six nonzero, individually normalized rows satisfy
\[
\max_{1\le i<j\le6}
|\langle\widehat A_{i,*},\widehat A_{j,*}\rangle|
\le\frac35.
\tag{46}
\]
More generally, Theorem 10 remains valid when its definition of a
certified row triple is enlarged to permit **any triple satisfying
the Gram screen \(5T\le Q\)**. The enlarged class still has
the sharp global constant \(\max\{10/3,1+c\}\), and contains a
**nonempty open neighborhood of every unitary six-by-six matrix**.

**Proof.** Under (46), every three-row submatrix satisfies
Theorem 11, so choose any balanced row partition and repeat
(40)--(41), including the interpolation to all \(c\ge0\).
The same argument works whenever each triple in some partition
has one of the three certified properties. The two sharpness witnesses
from Theorem 10 remain in this enlarged class.

The set with all six pairwise correlations strictly below \(3/5\)
is open, by continuity of Gram entries away from zero rows,
and it contains the full unitary group (all its distinct row
correlations are zero). Thus the inequality is proved on an
open set with full ambient dimension in \(\mathbb C^{6\times6}\).
The word “open” is not used to imply the entire space. QED.

**Proposition 13 (necessary Gram geometry of any critical
three-row counterexample).** If a normalized complex
\(3\times6\) matrix violates (43), and
\(a,b,d,s,t\) are as in (2), then necessarily
\[
s>\frac{27}{25},\qquad
|a|,|b|,|d|>\frac{5-\sqrt{17}}2,
\qquad
\frac{t}{|abd|}>\frac35.
\tag{47}
\]
In particular all pairwise row overlaps are bounded **strictly
away from zero**, and the invariant Bargmann three-cycle
phase has cosine strictly greater than \(3/5\).

**Proof.** By the exact identity (45), a violation forces
\(5t>s\). AM–GM (3) then gives \(s>27/25\).
Write \(x=|a|,y=|b|,z=|d|\le1\). Since
\(xyz\ge t>s/5\), we have
\[
5xyz>x^2+y^2+z^2\ge2xy+z^2.
\]
Thus \(5z-2>0\), and using \(xy\le1\) gives
\(z^2<5z-2\). The root in \([0,1]\) of the quadratic
\(z^2-5z+2=0\) is \((5-\sqrt{17})/2\).
The other two pairwise bounds follow by cyclic symmetry.
Finally
\[
\frac{t}{xyz}>
\frac{s}{5xyz}
\ge\frac{3\sqrt3}{5\sqrt{s}}\ge\frac35,
\]
where the first last inequalities use AM–GM
\(xyz\le(s/3)^{3/2}\) and \(s\le3\). QED.

**Remaining gap.** Gram screening proves a large, robust,
full-dimensional region and precisely localizes potential
counterexamples to strongly correlated row triples.
It cannot handle near-parallel triples by itself: the flat
parallel extremizer has \(s=t=3,1\), hence \(5t>s\),
yet Theorem 7 proves the needed collision compensation there.
A genuinely global bound still needs control of this
collision deficit when none of the rows is flat or coordinate.
