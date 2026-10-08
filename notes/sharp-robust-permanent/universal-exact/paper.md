# A universal exact determinant formula for finite subset-action atom moduli

**8 October 2026. Complete traditional proof draft; not externally peer reviewed or Lean-formalized.**

## Abstract

For the natural action of \(S_n\) on \(k\)-subsets, constrain a probability law \(\nu\) to give a uniform image for every prescribed \(k\)-subset. We obtain, for **every finite pair** \(n\ge1,\ 0\le k\le n\), an exact rational formula for the smallest constant comparing the probability change of any permutation atom with total variation. The formula uses only explicitly prescribed integer cycle-index coefficients, determinants of size at most \(\min(k,n-k)+1\), and a finite maximum. A closed product evaluates a distinguished full-rank determinant; an extremal-circuit lemma proves that at most \(\min(k,n-k)+2\) conjugacy classes suffice for exact attainment. Unlike the earlier orbital linear program, the answer has no continuous optimization variables, implicit infimum or solver dependency. It is an **explicit finite combinatorial closed formula**, not an elementary piecewise rational expression free of any finite maximum.

## 1. Problem and boundary cases

Let \(\Omega_{n,k}=\binom{[n]}k\) and let \(u_n\) be uniform on \(S_n\). A law \(\nu\) on \(S_n\) is admissible when
\[
\nu\{\pi:\pi(E)=F\}=\binom nk^{-1}
\quad(E,F\in\Omega_{n,k}).
\]
Set
\[
C_{n,k}=
\sup_{\substack{\nu\ne u_n\\\nu\text{ admissible}}}
\frac{|\nu(\mathrm{id})-1/n!|}
{\frac12\sum_{\pi\in S_n}|\nu(\pi)-1/n!|},
\tag{1}
\]
with supremum zero if the admissible set contains only the uniform law. By left translation, the same constant applies to every other specified permutation atom. Complementation of subsets is equivariant, so \(C_{n,k}=C_{n,n-k}\).

Put \(m=\min(k,n-k)\), always satisfying \(n\ge2m\). For the singleton group \(S_1\) the constant is zero. For \(n\ge2\), \(C_{n,0}=C_{n,n}=1\): both actions are trivial and a signed identity/nonidentity perturbation attains one. For the remainder assume \(n\ge2\) and \(1\le m\le n/2\).

## 2. All integer data from \((n,m)\)

The feasible short-cycle vectors are
\[
\mathcal T_{n,m}=\left\{c=(c_1,\ldots,c_m)\in\mathbb Z_{\ge0}^m:
r_c=n-\sum_{j=1}^m jc_j\in\{0\}\cup\{m+1,m+2,\ldots\}\right\}.
\tag{2}
\]
The canonical representative of \(c\) has \(c_j\) cycles of length \(j\), together with one \(r_c\)-cycle if \(r_c>0\). The identity type \(c_*=(n,0,\ldots,0)\) is unique.

Define the two-state matrix and cycle-index polynomial recurrence
\[
M(u,t)=\begin{pmatrix}1&u\\1&ut\end{pmatrix},\quad
Z_0=2,\quad Z_1=1+ut,\quad
Z_\ell=(1+ut)Z_{\ell-1}-u(t-1)Z_{\ell-2}.
\tag{3}
\]
Define \(\Lambda(u,t)=\sum_{a\ge0}A_a(t)u^a\) as the unique formal-series solution with constant term one of
\[
\Lambda^2-(1+ut)\Lambda+u(t-1)=0.
\]
Its coefficients are integer polynomials, given by \(A_0=1\) and
\[
A_a=tA_{a-1}-\sum_{j=1}^{a-1}A_jA_{a-j}
-\mathbf1_{\{a=1\}}(t-1).
\tag{4}
\]
For \(c\in\mathcal T_{n,m}\), define **integers**
\[
F_h(c)=[u^mt^h]\,
\Lambda(u,t)^{r_c}\prod_{\ell=1}^m Z_\ell(u,t)^{c_\ell},
\quad 0\le h\le m.
\tag{5}
\]
The exact all-rank cycle-index theorem (proved independently in Section 25 of the main dossier) shows that this counts the number of \(m\)-subsets \(E\) satisfying \(|E\cap g(E)|=h\), for any \(g\) represented by \(c\). In particular \(F_h(c)\ge0\) and \(\sum_{h=0}^m F_h(c)=N:=\binom nm\).

Define the \((m+1)\times|\mathcal T_{n,m}|\) **integer matrix**
\[
A(n,m)=(a_c)_{c\in\mathcal T_{n,m}},\qquad
a_c=(1,F_0(c),\ldots,F_{m-1}(c))^T.
\tag{6}
\]
The first row encodes signed total mass zero. The other \(m\) rows encode all necessary independent marginal-orbital constraints; \(F_m\) is redundant by the fixed sum \(N\).

## 3. Main exact formula

Order the nonidentity types in \(\mathcal T_{n,m}\setminus\{c_*\}\) lexicographically. For each selection of \(m+1\) **different** such types
\[
T=\{c_1<\cdots<c_{m+1}\},
\]
form \(B_T=(a_{c_*},a_{c_1},\ldots,a_{c_{m+1}})\), an integer matrix of shape \((m+1)\times(m+2)\). For \(i=0,\ldots,m+1\), put
\[
\Delta_i(T)=(-1)^i\det(B_T\text{ with column }i\text{ deleted}).
\tag{7}
\]
Omit a selection when all \(\Delta_i(T)\) vanish. An empty maximum means zero.

**Theorem A (universal finite exact-value formula).** For every \(n\ge2\) and \(1\le m=\min(k,n-k)\le n/2\),
\[
\boxed{
C_{n,k}=
\max_{\substack{T\subseteq\mathcal T_{n,m}\setminus\{c_*\}\\
|T|=m+1,\ \sum_{i=0}^{m+1}|\Delta_i(T)|>0}}
\frac{2|\Delta_0(T)|}{\sum_{i=0}^{m+1}|\Delta_i(T)|}.
}
\tag{8}
\]
Together with the boundary cases in Section 1, this is a **terminating exact rational arithmetic formula valid for every finite \((n,k)\)**. If \(C_{n,k}>0\), an attaining marginal-preserving signed perturbation exists with support on at most \(m+2\) conjugacy classes. It is converted into a genuine nonnegative probability law for all sufficiently small positive rational amplitudes.

The proof consists of the following independent nonzero determinant evaluation and a finite-dimensional circuit lemma.

## 4. The exact full-rank determinant

**Theorem B (sharp rank theorem).** For \(n\ge2m\ge2\),
\[
\operatorname{rank}_{\mathbb Q}A(n,m)=m+1.
\tag{9}
\]
For \(j=0,\ldots,m-1\), let \(g_j\) have exactly \(j\) fixed points and one long cycle of length \(n-j\). Then
\[
\boxed{
\det(a_{g_0},\ldots,a_{g_{m-1}},a_{c_*})
=(-1)^m\prod_{r=0}^{m-1}\binom{n-2r}{m-r}\ne0.
}
\tag{10}
\]

**Proof.** For each \(j<m\), its only nontrivial cycle has length \(n-j\ge m+1\). It fixes no \(m\)-subset, because the \(j\) fixed points are fewer than \(m\). Thus its orbital generating polynomial
\[
G_j(t)=\sum_{h=0}^{m}F_h(g_j)t^h
=[u^m](1+ut)^j\Lambda(u,t)^{n-j}
\tag{11}
\]
has degree at most \(m-1\). Let \(\nabla\) denote forward differences in \(j\). The binomial theorem gives
\[
\nabla^rG_0(t)=[u^m]\Lambda(u,t)^{n-r}
(1+ut-\Lambda(u,t))^r.
\tag{12}
\]
Differentiating the defining quadratic equation for \(\Lambda\) gives the exact series identities
\[
\Lambda(u,1)=1+u,\qquad
\partial_t\Lambda(u,1)=\frac{u^2}{1+u}.
\tag{13}
\]
Consequently \(1+ut-\Lambda(u,t)\) vanishes at \(t=1\) and has first derivative \(u/(1+u)\). Therefore the polynomial \(\nabla^rG_0\) vanishes to order at least \(r\) at \(t=1\), with **exact diagonal Taylor coefficient**
\[
\frac1{r!}(\nabla^rG_0)^{(r)}(1)
=[u^m](1+u)^{n-r}\left(\frac{u}{1+u}\right)^r
=\binom{n-2r}{m-r}>0
\quad(0\le r<m).
\tag{14}
\]
Changing the column basis from \(G_0,\ldots,G_{m-1}\) to their successive forward differences is a unit-triangular transformation. Changing the row basis from coefficients of \(t^0,\ldots,t^{m-1}\) to Taylor coefficients at \(t=1\) is also unit triangular. In these bases the resulting matrix is triangular with diagonal (14). Thus
\[
\det(F_h(g_j))_{0\le h,j<m}
=\prod_{r=0}^{m-1}\binom{n-2r}{m-r}.
\]
The identity column is \((1,0,\ldots,0)^T\), so expansion along this last column yields the sign \((-1)^m\), proving (10) and (9). QED.

This is a **closed product identity for all \(n,m\)**, not a finite pattern inferred from numerical determinant evaluations.

## 5. A circuit theorem for signed \(\ell^1\) kernels

**Lemma C (maximal-minor circuit formula).** Let \(D=(d_0,\ldots,d_{p-1})\) be a real \(r\times p\) matrix of full row rank \(r\), whose first row consists entirely of ones. Put
\[
\Gamma(D)=\sup_{\substack{v\ne0\\Dv=0}}
\frac{2|v_0|}{\sum_i|v_i|},
\]
and define it to be zero if \(\ker D=\{0\}\). For each \(r\)-subset \(J\subseteq\{1,\ldots,p-1\}\), form the \(r\times(r+1)\) matrix \((d_0,d_{j_1},\ldots,d_{j_r})\) and its alternating maximal-minor vector \(\Delta(J)\) as in (7). Then
\[
\boxed{
\Gamma(D)=\max_{\substack{J\subseteq\{1,\ldots,p-1\}\\
|J|=r,\ \sum_i|\Delta_i(J)|>0}}
\frac{2|\Delta_0(J)|}{\sum_i|\Delta_i(J)|}.
}
\tag{15}
\]
An extremizer exists with support on at most \(r+1\) columns.

**Proof.** Every alternating maximal-minor vector belongs to the kernel of its rectangular matrix, by determinant expansion along a duplicated row. Extending it by zeros shows that every ratio on the right of (15) is bounded above by \(\Gamma(D)\).

Conversely suppose \(\Gamma(D)>0\). Compactness of the intersection \(\ker D\cap\{\sum|v_i|=2\}\) yields an extremizer \(v\). Reverse its sign if necessary so \(v_0>0\); normalize \(\sum_{v_i>0}v_i=1\). Since the first row of \(D\) is all ones, the negative mass also equals one. Fix the sign orthant of \(v\). The corresponding nonnegative-coordinate feasible set
\[
\mathcal P=\{x\ge0:
D\operatorname{diag}(\varepsilon)x=0,\
\sum_{\varepsilon_i=+1}x_i=1\}
\tag{16}
\]
is a compact polytope, as both positive and negative masses equal one. Choose a vertex of \(\mathcal P\) maximizing its identity coordinate, which stays strictly positive.

Let \(S\) be that vertex's nonzero support and \(w\in\ker D_S\) its signed coordinate vector, all of whose \(S\) entries are nonzero. If \(\dim\ker D_S\ge2\), there exists a nonzero kernel direction preserving the one scalar positive-mass normalization. Sufficiently small positive and negative multiples of this direction keep all support signs unchanged and produce distinct points of \(\mathcal P\) with the original vertex as their midpoint. This contradicts extremality. Therefore
\[
\dim\ker D_S=1,\qquad \operatorname{rank}D_S=|S|-1.
\tag{17}
\]
Deleting any one column of \(S\) leaves an independent family: otherwise there would be a second dependence not proportional to \(w\), whose deleted coordinate is nonzero. Hence \(S\) is an **elementary circuit** and \(|S|\le r+1\). It contains column zero because \(v_0>0\).

Extend the independent family \(S\setminus\{0\}\) to a basis of the full row space using columns from the entire matrix \(D\). Adjoin column zero, obtaining exactly \(r+1\) columns of rank \(r\). Its kernel is one dimensional and contains the original circuit vector with zeros in the added coordinates. Thus it is proportional to the alternating maximal-minor vector of this \(r\times(r+1)\) matrix, and its norm ratio appears among the right-hand terms of (15). This establishes the reverse inequality. When \(\Gamma(D)=0\), the first direction forces every candidate ratio to vanish, so the statement also holds. QED.

## 6. Completion of the universal formula and attainment

We recall precisely why orbital compression does not lose any signed marginal-preserving perturbation. Conjugation averaging of a signed law preserves its identity atom and image-marginal constraints and cannot increase total variation. For a conjugation-invariant law, equality of all image marginals is equivalent to equality of the aggregate orbital moments \(F_0,\ldots,F_m\). The total-mass row and the first \(m\) moments suffice because \(\sum F_h=N\).

Classes with identical \(c=(c_1,\ldots,c_m)\) have identical moments by (5), so their signed masses may be aggregated, never increasing the \(\ell^1\) mass. Conversely, every short-cycle vector has a canonical actual conjugacy-class representative. Any real vector \(v=(v_c)\in\ker A(n,m)\) with total mass zero can be represented by placing its signed class mass uniformly on these canonical classes. For sufficiently small positive amplitude \(\varepsilon\), adding \(\varepsilon v\) to the strictly positive uniform law gives a **nonnegative admissible probability distribution**, with identity atom change \(\varepsilon v_{c_*}\) and total variation \((\varepsilon/2)\sum_c|v_c|\). Therefore
\[
C_{n,k}=\Gamma(A(n,m)).
\tag{18}
\]
Theorem B gives \(\operatorname{rank}A=m+1\). Lemma C with \(r=m+1\) yields exactly Theorem A, equation (8).

For explicit attainment orient a maximizing minor vector so \(\Delta_0>0\) and write
\[
d=\sum_{\Delta_i>0}\Delta_i
=-\sum_{\Delta_i<0}\Delta_i>0.
\]
Define central probability laws supported on the selected canonical classes by
\[
P=\sum_{\Delta_i>0}\frac{\Delta_i}{d}\,U_{[g_i]},
\qquad
Q=\sum_{\Delta_i<0}\frac{-\Delta_i}{d}\,U_{[g_i]}.
\tag{19}
\]
Their supports are disjoint; since \(A\Delta=0\), their image marginals agree **exactly**. For small enough rational \(\varepsilon>0\),
\(\nu_\varepsilon=u_n+\varepsilon(P-Q)\) is nonnegative, admissible and has total variation \(\varepsilon\). Its identity atom excess is \(\varepsilon\Delta_0/d\), giving
\[
\frac{\nu_\varepsilon(\mathrm{id})-1/n!}
{\|\nu_\varepsilon-u_n\|_{\mathrm{TV}}}
=\frac{2|\Delta_0|}{\sum_i|\Delta_i|}=C_{n,k}.
\]
Thus Theorem A provides both an exact upper value and a matching explicit probability construction. QED.

## 7. Complexity, rational height, and examples

The number \(p=|\mathcal T_{n,m}|\) obeys
\[
p\le\prod_{j=1}^m(1+\lfloor n/j\rfloor)=O_m(n^m).
\]
There are at most \(\binom{p-1}{m+1}=O_m(n^{m(m+1)})\) ratios in (8). Each uses \(m+2\) integer determinants of size \(m+1\), evaluable by fraction-free Bareiss elimination. Hence for every **fixed \(m\)** the formula yields a polynomial-in-\(n\) terminating integer algorithm; it is not claimed polynomial in the binary input length \(\log n\).

Because \(0\le F_h(c)\le N=\binom nm\), cofactor expansion along the row of ones gives
\[
|\Delta_i|\le(m+1)!\,N^m.
\]
The first row also gives \(\sum_i\Delta_i=0\). Thus every resulting reduced rational optimum has denominator at most
\[
\boxed{(m+2)(m+1)!\binom nm^m.}
\tag{20}
\]

The independent pure-integer implementation uses the published all-rank cycle recurrence to compute \(F_h\), fraction-free Bareiss integer determinants to compute every \(\Delta_i\), and Python Fraction only for exact quotient comparison. Its fixed regression set reproduces, among others,
\[
\begin{array}{c|cccccccc}
(n,k)&(3,1)&(4,2)&(6,3)&(8,3)&(9,3)&(10,3)&(8,4)&(9,4)\\\hline
C_{n,k}&1/3&1/3&5/14&89/244&259/691&368/935&5/14&5/14.
\end{array}
\]
It checks the exact rank-product identity (10) for \(m\le9\) and multiple degrees. These finite tests are supplemental; the complete proof applies to every finite \(n,k\).

## 8. Scope and provenance

This theorem completely answers arbitrary finite-parameter **exact evaluability** in a prescribed determinant/minor sense. It does **not** produce a single short algebraic rational function or a finite number of parameter branches valid for all \((n,k)\); the finite maximization may be very large. A uniform classification of which circuit maximizes at every parameter pair remains a stronger open structural problem.

The argument uses classical ideas—LP/extreme points, signed circuits of vector configurations, determinants, cycle-index recurrences—and extends the orbital primal-dual and all-rank cycle-compression theorems previously documented in this public repository. It makes no unverified priority claim. This is an AI-assisted proof draft, not a proof-assistant kernel formalization or external human referee report. Such independent audits remain important.


## 9. The \(m+2\) support bound is genuinely sharp

**Proposition D (minimal support at \((n,k)=(11,4)\)).** For the \(S_{11}\) action on four-element subsets, the exact optimal coefficient is \(C_{11,4}=1629/4549\). Every signed marginal-preserving perturbation **attaining that optimum** has nonzero mass in at least six distinct short-cycle types. Since \(m=4\), this shows the universal support bound \(m+2\) in Theorem A **cannot be reduced to \(m+1\) uniformly**.

**Proof.** The independently certified \(n=11,k=4\) dual in the repository has coefficient vector
\[
\lambda=(-1511/955290,\,-624/159215,\,-169/191058,\,-365/95529)
\]
for the four nontrivial orbital counts. The dual function
\[
h(g)=\mathbf1_{\{g=e\}}-\sum_{j=0}^3\lambda_jF_j^{(4)}(g)
\]
has exact range \([2920/4549,\,1]\). An exhaustive integer check over **all 54 feasible short-cycle types** finds that the *only* types attaining its upper value \(1\) are
\[
(11,0,0,0),\quad(7,0,0,1),\quad(0,1,3,0),
\]
and the *only* types attaining its lower value \(2920/4549\) are
\[
(9,1,0,0),\quad(4,0,1,1),\quad(0,4,1,0).
\]
For an optimal signed perturbation, the difference between these two dual values must equal the \(\ell^1\) objective. Equality in the elementary range bound for a zero-mass signed measure forces its positive part to live **entirely on the upper contact set**, and its negative part **entirely on the lower contact set**, after orienting the identity atom positively.

Consider the resulting \(5\times6\) orbital matrix, with identity first and the five other contact types lexicographically ordered. Its exact alternating maximal-minor vector is
\[
(-344826720,\,-23708160,\,11430720,\,121927680,\,
-594397440,\,829573920).
\]
Every coordinate is **nonzero**, so the matrix has rank five and a one-dimensional kernel, with every nonzero kernel vector supported on **all six columns**. Its exact \(\ell^1\) ratio is
\[
\frac{2(344826720)}
{344826720+23708160+11430720+121927680+
 594397440+829573920}
=\frac{1629}{4549}.
\]
Conjugation averaging cannot increase total variation or change the identity atom, so an arbitrary (not necessarily central) attaining perturbation would yield a central attaining perturbation with no new short-cycle types. It, too, must therefore involve at least six types. This proves sharpness.

Every stated dual contact inequality, complete contact set and integer maximal minor is independently replayed by the published pure-integer/Fraction checker
check_sparse_support_sharpness.py. The proof is an exact finite certificate, not a numerical LP conclusion. QED.
