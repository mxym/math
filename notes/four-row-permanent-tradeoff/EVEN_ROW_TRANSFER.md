# Balanced Laplace transfer and collision-free symmetric minors

**Structural companion to the sharp four-row theorem.** This note
isolates which parts of the four-row proof extend to every even
matrix size and which extra rectangular inequality would be needed
to settle the higher-row case. All stated results have complete
proofs; the proposed endpoint inequality for three or more rows
is explicitly labeled a conjecture.

## 1. Universal even-row reduction

Let m>=1, n=2m. For a complex m-by-n matrix U and each m-subset
J of [n], denote by U_J its square m-by-m submatrix of columns J.
Put
\[
\mathcal S_m(U)=\sum_{|J|=m}|\operatorname{per}(U_J)|^2,\qquad
\mathcal W_m(U)=\sum_{|J|=m}|\det(U_J)|^2
=\det(UU^*).
\tag{1}
\]
The last identity is ordinary complex Cauchy–Binet.

**Theorem 1 (balanced Laplace transfer for all even dimensions).**
Let A be a complex n-by-n matrix, with its top m rows U and bottom
m rows V. For every c>=0,
\[
\boxed{
|\operatorname{per}A|+c|\det A|
\le\sqrt{(\mathcal S_m(U)+c\mathcal W_m(U))
        (\mathcal S_m(V)+c\mathcal W_m(V))}.
}\tag{2}
\]
In particular, any universal rectangular estimate
\[
\mathcal S_m(U)+c\mathcal W_m(U)
\le L_m(c)\prod_{i=1}^m\|U_{i,*}\|_2^2
\tag{3}
\]
automatically yields
\[
|\operatorname{per}A|+c|\det A|
\le L_m(c)\prod_{i=1}^{2m}\|A_{i,*}\|_2.
\tag{4}
\]

**Proof.** For each m-subset J, let J^c be its complement.
Laplace expansion along the first m rows gives exactly
\[
\operatorname{per}A
=\sum_{|J|=m}\operatorname{per}(U_J)
              \operatorname{per}(V_{J^c}),
\]
\[
\det A=\sum_{|J|=m}\varepsilon_J
                 \det(U_J)\det(V_{J^c}),
\qquad\varepsilon_J\in\{-1,1\},
\]
where epsilon_J is the column-shuffle sign. Cauchy–Schwarz
bounds the two absolute values separately by the geometric
means of S_m and W_m for U,V. Cauchy–Schwarz once more
in R^2, with weights (1,c), proves (2). The complement map
permutes all m-subsets because n=2m; no binomial factor is
lost. Equation (4) follows by applying (3) to U and V
and taking the square root. QED.

For m=2, Theorem 3 of the main [four-row paper](PAPER.md)
proves the required rectangular bound with the exact
L_2(c)=max(3/2,1+c), yielding the already published
complete four-row theorem. For m=1 the same statement
holds trivially with L_1(c)=1+c.

For each m, the two explicit rectangular witnesses
suggest the sharp candidate
\[
\boxed{
L_m(c)\stackrel{?}{=}\max\{C_{2m},\,1+c\},
\qquad C_{2m}=\frac{(2m)!}{(2m)^m}.
}\tag{5}
\]
Indeed m normalized identical flat rows of length 2m have
\(\mathcal S_m=C_{2m},\ \mathcal W_m=0\), since there
are binomial(2m,m) equal permanent minors, each of modulus
m!/(2m)^(m/2). And m distinct coordinate rows have
\(\mathcal S_m=\mathcal W_m=1\).
Formula (5) is **proved for m=1 and m=2**, but is **not
proved for m>=3** in this repository. It is stated as an
open target, not a theorem. If it holds at m=3, Theorem 1
would immediately deliver the conjectured full six-row
permanent–determinant tradeoff with critical c=7/3.

## 2. Bosonic Cauchy–Binet identity for arbitrary row frames

The lower-branch endpoint of (5) has an all-dimension
structural identity. It also determines exactly the
orthonormal-row endpoint of its upper branch.

For any complex m-by-n matrix U with row vectors
\(u_1,\ldots,u_m\), define the homogeneous degree-m polynomial
\[
F_U(z)=\prod_{i=1}^m\left(\sum_{j=1}^n u_{ij}z_j\right)
      =\sum_{\alpha\in\mathbb N^n,\ |\alpha|=m}
        c_\alpha z^\alpha,
\qquad \alpha!:=\prod_{j=1}^n\alpha_j!.
\tag{6}
\]

**Theorem 2 (full bosonic coefficient identity).**
For every m<=n and every complex U,
\[
\boxed{
\sum_{|\alpha|=m}\alpha!|c_\alpha|^2
=\operatorname{per}(UU^*).
}\tag{7}
\]
If U has orthonormal rows, then
\[
\boxed{\quad
\sum_{|J|=m}|\operatorname{per}(U_J)|^2\le1,
\qquad \mathcal W_m(U)=1.
\quad}\tag{8}
\]
Equality in the permanent sum in (8) holds **if and only if**
the m row supports are pairwise disjoint, i.e. each column
contains at most one nonzero entry.

**Proof of (7).** Consider the Hilbert tensor product
\((\mathbb C^n)^{\otimes m}\) and the symmetrized row tensor
\[
\Psi_U=\frac1{\sqrt{m!}}\sum_{\sigma\in S_m}
u_{\sigma(1)}\otimes\cdots\otimes u_{\sigma(m)}.
\]
Expanding the inner product over row permutations gives
\[
\|\Psi_U\|^2
=\frac1{m!}\sum_{\sigma,\tau}
 \prod_{i=1}^m\langle u_{\sigma(i)},u_{\tau(i)}\rangle
=\sum_{\rho\in S_m}\prod_{i=1}^m
  \langle u_i,u_{\rho(i)}\rangle
=\operatorname{per}(UU^*).
\]
On the other hand, in the orthonormal standard tensor basis,
the coefficient at an ordered column-index sequence of
multiplicity vector alpha is
\((\alpha!/\sqrt{m!})c_\alpha\), because alpha! row
permutations give the same monomial allocation.
There are \(m!/\alpha!\) such ordered sequences, so their
total squared norm contribution is
\((m!/\alpha!)(\alpha!^2/m!)|c_\alpha|^2
=\alpha!|c_\alpha|^2\).
Sum over alpha to prove (7).

**Proof of (8) and equality.** When rows are orthonormal,
UU*=I_m and per(UU*)=1. For each squarefree
multi-index alpha=1_J, its coefficient c_alpha is
exactly per(U_J) and alpha!=1. All other terms
in (7) are nonnegative. Dropping them proves (8)'s
permanent inequality. Cauchy–Binet gives
W_m=det(UU*)=1.

Equality is equivalent to vanishing of every
non-squarefree coefficient, i.e. to \(F_U\) being
multiaffine in all column variables. Since F_U is
a product of nonzero linear forms over the integral
domain C[z_1,...,z_n], its degree in each variable z_j
is **exactly** the number of factors with u_{ij} nonzero.
Thus F_U is multiaffine if and only if no column
variable occurs in more than one factor, precisely
pairwise disjoint row supports. QED.

The bosonic tensor identity (7) is an elementary
symmetric-tensor formula, not a world-first novelty claim.
Its exact collision-free equality criterion provides a
rigorous high-weight endpoint for rectangular multirow
permanent energies, but is **insufficient by itself**
to establish (5) when rows are not orthogonal.

## 3. Trust boundary and reproducibility

Theorems 1–2 are pure algebraic identities and
Cauchy–Schwarz inequalities with full proofs above,
requiring no floating-point optimization. The
[small-dimension combinatorial checker](check_even_transfer.py)
independently replays the Laplace permutation-sign
bijection for n=2,4,6,8 and tests the tensor identity
on exact rational row frames. The all-dimension
claims rest on the symbolic/combinatorial proofs, not
the finite replay.

The **still-open** step in (5) for m=3 is the
uniform rectangular inequality
\[
\mathcal S_3(U)+\frac73\det(UU^*)
\le\frac{10}3\prod_{i=1}^3\|U_{i,*}\|_2^2
\quad\text{for every complex }U\in\mathbb C^{3\times6}.
\tag{9}
\]
No proof or rigorous counterexample for this inequality
is claimed by the present paper. Numerical optimization
cannot substitute for either. The n=6 global
tradeoff is also not claimed.

**Subsequent partial closure.** The
[three-row collision tradeoff paper](../../research/three-row-collision-tradeoff/PAPER.md)
proves the sharp rectangular critical estimate in (9) when
**any two rows are equimodular** or **one row is a coordinate vector**.
Its Theorem 10 uses the balanced Laplace transfer above to prove the
exact sharp six-row mixed permanent--determinant bound, for all
nonnegative weights, on the class admitting a partition into two
triples each containing two equimodular rows or one coordinate row.
The same paper also supplies a denominator-free three-row
Gram screen and proves the sharp six-row bound on an explicit
full-dimensional open coherence region around the unitary group.
The global unrestricted six-row inequality remains open.

The proof does not imply any sharp bounds for
nonreal determinant weights in four rows, or a
general optimal mixing time for the Thorp shuffle.
