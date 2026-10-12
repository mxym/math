# A simultaneous all-Johnson trace kernel and a universal four-class obstruction

**Research note, 8 October 2026.** The preceding [fixed-rank orbital compression theorem](README.md) describes one \(k\)-subset action at a time. This note identifies the **entire joint linear information** contained in *all* subset-action orbital statistics in a fixed degree \(n\), proves its precise rank, and exhibits an exact positive central measure relation that preserves **all** subset-image marginals simultaneously. The relation leads to a universal \(5/14\) atom/total-variation obstruction. No world-first or independently refereed originality assertion is made: the underlying cycle-index and character-polynomial formalism has classical antecedents.

**Subsequent exact resolution:** [The universal sharp 5/14 theorem](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md) proves that the lower bound from this historical note is in fact **equal to the sharp all-rank and single middle-rank constant in every degree n>=6**. The proof includes a five-point rational dual, 44,582 exhaustive integer certificates, a uniform analytic tail, and a complete equality-contact classification.

## 1. The complete cycle polynomial

For \(g\in S_n\) with \(m_\ell(g)\) cycles of length \(\ell\), define the *cycle-invariant subset polynomial*

\[
Q_g(z)=\prod_{\ell=1}^n(1+z^\ell)^{m_\ell(g)}
=\sum_{r=0}^n A_r(g)z^r,
\tag{1}
\]

where \(A_r(g)\) counts **\(g\)-invariant subsets of cardinality \(r\)**: an invariant subset is precisely a union of whole cycles. The polynomial is palindromic,

\[
A_r(g)=A_{n-r}(g),
\tag{2}
\]

because complementation bijects invariant \(r\)-sets and invariant \((n-r)\)-sets.

For \(0\le j\le k\le n\) put

\[
F_{k,j}(g)=\#\{E\subseteq[n]:|E|=k,\ |E\cap gE|=j\}.
\tag{3}
\]

**Theorem 1 (all subset orbitals are exactly the cycle-polynomial span).** Let \(d=\lfloor n/2\rfloor\). As rational-valued class functions on \(S_n\),

\[
\boxed{\displaystyle
\operatorname{span}_{\mathbb Q}\{F_{k,j}:0\le j\le k\le n\}
=\operatorname{span}_{\mathbb Q}\{A_0,A_1,\ldots,A_d\}.}
\tag{4}
\]

In particular, the dimension of this entire joint orbital class-function space is **exactly**

\[
\boxed{d+1=\lfloor n/2\rfloor+1,}
\tag{5}
\]

even though \(S_n\) has \(p(n)\) distinct conjugacy classes. Thus, for central probability laws \(P,Q\), the following conditions are equivalent:

1. Their **full image marginal matrices agree** for the natural action on **every** \(k\)-subset family, \(k=1,\ldots,n\).
2. Their expectations of \(A_r(g)\), the counts of invariant \(r\)-subsets, agree for every \(0\le r\le d\).
3. The polynomial-valued expectations satisfy \(\mathbb E_PQ_g(z)=\mathbb E_QQ_g(z)\) as an exact coefficientwise identity.

For noncentral laws, condition 2 alone need not enforce all individual image marginals; the equivalence of 1--3 **requires centrality**.

*Proof.* Consider the exact \(2\times2\) transfer matrix

\[
T(s,t)=\begin{pmatrix}1&s\\1&st\end{pmatrix}.
\]

As in the companion all-rank transfer theorem, the trace of \(T^\ell\) enumerates the binary choices of vertices on an \(\ell\)-cycle, with \(s\) marking the number selected and \(t\) marking the selected-image overlap. If its formal eigenvalues are \(L_+=1+O(s)\) and \(L_-=O(s)\), then the exact generating identity is

\[
\begin{aligned}
\sum_{k=0}^n\sum_{j=0}^kF_{k,j}(g)s^kt^j
&=\prod_{\ell=1}^n
 \bigl(L_+^\ell+L_-^\ell\bigr)^{m_\ell(g)}\\
&=L_+^n\,Q_g(L_-/L_+).
\end{aligned}\tag{6}
\]

Here \(L_\pm\) are formal power series with polynomial rational coefficients in \(t\), so the identity is valid coefficientwise without numerical eigenvalue approximations. Expanding the final expression in the coefficients \(A_r(g)\),

\[
F_{k,j}(g)=
\sum_{r=0}^{d}\alpha_{k,j,r}(n)\,A_r(g)
\quad\text{for some fixed }\alpha_{k,j,r}(n)\in\mathbb Q.
\tag{7}
\]

To justify rationality in (7), note that the full transfer expression is symmetric in the two eigenvalues and lies in \(\mathbb Q[s,t]\); the coefficients of the pairwise palindromic combinations \(L_+^{n-r}L_-^r+L_+^rL_-^{n-r}\) are rational (equivalently, Newton recurrences in the rational trace and determinant). This proves one span inclusion. For the reverse inclusion, observe that

\[
F_{r,r}(g)=A_r(g):
\]

a set of size \(r\) has intersection \(r\) with its image precisely when it is invariant. This proves (4).

For the exact rank, evaluate (1) on the \(d+1\) conjugacy types \(g_r\) consisting of \(r\) disjoint transpositions and \(n-2r\) fixed points:

\[
Q_{g_r}(z)=(1+z)^{n-2r}(1+z^2)^r
=(1+z)^n
\left(\frac{1+z^2}{(1+z)^2}\right)^r,\qquad 0\le r\le d.
\tag{8}
\]

The rational function \(u(z)=(1+z^2)/(1+z)^2\) is nonconstant. If a linear combination of the \(d+1\) polynomials in (8) vanished, division by \((1+z)^n\) would yield a polynomial of degree at most \(d\) in \(u(z)\) vanishing identically. Since a nonconstant rational function takes infinitely many values, all its coefficients must be zero. Thus the \(d+1\) cycle polynomials in (8) are linearly independent. The reciprocal symmetry (2) bounds their ambient dimension by \(d+1\), proving equality (5).

Finally, for central \(P,Q\), equality of every \(F_{k,j}\)-expectation is equivalent to equality of every individual \(k\)-set image marginal, since the diagonal \(S_n\)-orbitals on ordered pairs \((E,H)\) are indexed by \(|E\cap H|\) and centrality makes the probability constant within each orbital. Combining this equivalence with (4) and (1)--(2) proves the three equivalent conditions. QED.

**Interpretation.** This theorem compresses the **number of independent linear constraints** to \(\lfloor n/2\rfloor+1\). It does **not** imply there are only \(O(n)\) distinct conjugacy-class columns in a finite optimization: multiple classes can have different points inside the same low-dimensional space. It also does not claim polynomial time in \(n\) for arbitrary unrestricted \(k\).

## 2. An exact universal relation supported on four conjugacy classes

**Theorem 2 (universal four-class orbital identity).** For every integer \(n\ge6\) and every \(0\le j\le k\le n\), let \(I\) be the identity class, \(K\) the class \(4\,1^{n-4}\), \(T\) the transposition class \(2\,1^{n-2}\), and \(E\) the class \(3^2\,1^{n-6}\). Then

\[
\boxed{\displaystyle
5F_{k,j}(I)+9F_{k,j}(K)
=12F_{k,j}(T)+2F_{k,j}(E)
\quad\text{for all }k,j.}
\tag{9}
\]

*Proof.* First verify the elementary **exact polynomial identity**

\[
\boxed{\displaystyle
5(1+z)^6+9(1+z)^2(1+z^4)
=12(1+z)^4(1+z^2)+2(1+z^3)^2.}
\tag{10}
\]

Both sides, when expanded in ascending powers of \(z\), have the coefficient vector

\[
(14,48,84,100,84,48,14).
\]

Multiplying (10) by \((1+z)^{n-6}\) gives, exactly,

\[
5Q_I(z)+9Q_K(z)=12Q_T(z)+2Q_E(z).
\tag{11}
\]

Apply the full all-subset transfer identity (6) to the signed combination \(5I+9K-12T-2E\). Because (11) annihilates the entire cycle polynomial, its bivariate generating expression vanishes identically. Every coefficient of \(s^kt^j\) is zero, proving (9) simultaneously for **all** ranks \(k\). QED.

Thus the signed measure on **conjugacy classes**

\[
5U_I+9U_K-12U_T-2U_E
\tag{12}
\]

belongs to the joint kernel of all Johnson orbital statistics in every degree \(n\ge6\). All classes in (12) are distinct and its coefficients sum to zero.

**Corollary 3 (a universal atom/TV obstruction even under all ranks).** Let \(C_n^{\rm all}\) denote the sharp atom-to-TV coefficient when the probability law must preserve the uniform image marginals **simultaneously on every subset family** \(\binom{[n]}k\), \(0\le k\le n\). Then for all \(n\ge6\),

\[
\boxed{C_n^{\rm all}\ge\frac5{14}.}
\tag{13}
\]

*Proof.* Let

\[
P=\frac5{14}U_I+\frac9{14}U_K,\qquad
Q=\frac67U_T+\frac17U_E.
\tag{14}
\]

They are disjointly supported, conjugation-invariant, positive, rational probability measures with \(P(e)=5/14\), \(Q(e)=0\). By (9) and centrality, their image marginal matrices agree on **every** subset family, not merely at some fixed \(k\). For any sufficiently small rational \(\delta>0\), the law \(u_n+\delta(P-Q)\) is nonnegative, has uniform image marginals for all subset ranks, and has TV distance \(\delta\) and identity-atom excess \(5\delta/14\). Therefore \(C_n^{\rm all}\ge5/14\). QED.

**Historical scope of this earlier note:** At its original publication, (13) was only a lower bound, and numerical LP exploration through degree 30 suggested sharpness. The subsequent [complete five-point rational dual proof](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md) has now proved the **matching universal upper bound in every degree n>=6**. The earlier lower-bound argument remains a separate proof ingredient; no numerical extrapolation is used in the completed theorem.

## 3. A single middle-rank action controls *all* subset ranks

**Theorem 4 (exact equivalence of uniform-marginal constraints; no centrality assumption).** Let \(n\ge2\) and \(d=\lfloor n/2\rfloor\). For an **arbitrary** probability measure \(\nu\) on \(S_n\), not necessarily central,

\[
\boxed{\displaystyle
\text{\(\nu\) has uniform image marginals on **every** \(k\)-set family}
\quad\Longleftrightarrow\quad
\text{\(\nu\) has uniform image marginals on the single \(d\)-set family}.}
\tag{15}
\]

Consequently, the sharp coefficient defined in Corollary 3 is **exactly**

\[
\boxed{C_n^{\rm all}=C_{n,\lfloor n/2\rfloor}.}
\tag{16}
\]

*Proof.* For \(0\le\ell\le d\), let \(V_\ell\) and \(V_d\) be the real permutation representations on \(\ell\)- and \(d\)-subsets. The inclusion matrix

\[
W_{\ell,d}:V_\ell\to V_d,\qquad
(W_{\ell,d}f)(E)=\sum_{\substack{S\subseteq E\\|S|=\ell}}f(S)
\]

is an \(S_n\)-intertwiner. It is **injective** whenever \(\ell\le d\le n-\ell\). Here is a complete elementary induction on \(\ell\). The assertion for \(\ell=0\) is clear. Suppose \(W_{\ell,d}f=0\); for any two vertices \(a\ne b\), subtract the vanishing inclusion sums on \(T\cup\{a\}\) and \(T\cup\{b\}\), where \(T\) is any \((d-1)\)-subset excluding \(a,b\). The difference equals

\[
\sum_{\substack{U\subseteq T\\|U|=\ell-1}}
\bigl(f(U\cup\{a\})-f(U\cup\{b\})\bigr)=0.
\]

The induction hypothesis applies on the remaining \(n-2\) vertices with ranks \(\ell-1,d-1\), since \(\ell-1\le d-1\le(n-2)-(\ell-1)\). Therefore \(f(U\cup\{a\})=f(U\cup\{b\})\) for every eligible \(U\). The Johnson graph of \(\ell\)-subsets is connected, hence \(f\) is constant; the vanishing inclusion sums force that constant to be zero. This proves injectivity.

Write \(\rho_r(g)\) for the permutation matrix in \(V_r\). Inclusion intertwines the actions:

\[
\rho_d(g)W_{\ell,d}=W_{\ell,d}\rho_\ell(g)
\quad\text{for every }g\in S_n.
\]

If the averaged action matrix in \(V_d\) under \(\nu\) equals its value under \(u_n\), then multiplying by \(W_{\ell,d}\) and using the injectivity just proved shows that the averaged action matrices agree also in \(V_\ell\), for every \(\ell\le d\). These matrix equalities are *exactly* the uniform image marginal conditions. For \(k>d\), the complement map identifies the \(k\)-subset representation with the \((n-k)\)-subset representation, and \(n-k\le d\). Thus uniform \(d\)-set marginals force uniform marginals for every rank. The converse is immediate. Since the admissible classes of probability measures in the two sharp-constant definitions coincide, so do the best constants, proving (16). QED.

Together with Corollary 3, this proves the **concrete single-rank inequality**

\[
C_{n,\lfloor n/2\rfloor}\ge5/14
\quad\text{for all }n\ge6.
\tag{17}
\]

**Resolved subsequent to this note.** The [sharp universal all-rank theorem](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md) constructs an explicit dual using five rational cycle-polynomial evaluations, verifies 44,582 finite shapes by two independent exact checkers, and proves every unbounded case by a strict rational tail inequality. It establishes **C_{n,floor(n/2)}=5/14 for every n>=6**, as well as sharp support rigidity and the faithful-subgroup bound. This replaces the earlier conjecture; the original historical lower-bound record is retained.

## 4. Reproduction, scope and follow-up

The [exact integer-only checker](check_all_rank_trace_kernel.py) uses no optimization, floating point, or third-party libraries. From the repository root run:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_all_rank_trace_kernel.py
~~~

It checks the exact polynomial relation (11) for \(n=6,\ldots,100\), independently verifies its entire \(k=1,\ldots,n\) orbital array for every \(n=6,\ldots,21\) using the short-cycle transfer evaluator, and calculates by exact rational elimination the rank \(\lfloor n/2\rfloor+1\) on the explicit transposition-class witness matrix for \(n=6,\ldots,30\). These checks are supplementary: the general rank and identity are proved above algebraically and hold for **all** stated degrees without extrapolation.

Natural stronger problems are determining the exact \(C_n^{\rm all}\) for arbitrary \(n\), finding a finite class-relation generating set for the full kernel in the ring of symmetric homogeneous binary forms, and using the linear-rank compression to streamline higher-rank exact rational LP proofs. A key distinction is that (13) supplies an all-rank lower obstruction but does not by itself prove any sharp *upper* coefficient. No historical novelty or independent peer review is claimed.
