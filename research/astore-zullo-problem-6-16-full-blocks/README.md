# The full-block exception in Astore–Zullo Problem 6.16

Let \(q\ge3\) be any prime power, \(m\ge2\), \(K=\mathbb F_{q^m}\),
and \(F=\mathbb F_q\). Among \(K\)-linear MSRD codes of dimension \(m+1\)
with all blocks of length \(m\), the maximum number of blocks is
\[
 t_{\max}(q,m)=
 \begin{cases}
  3,&(q,m)=(3,2),\\
  q-1,&\text{otherwise}.
 \end{cases}
\]
Thus the answer to [Astore–Zullo, Problem 6.16](https://arxiv.org/abs/2610.23633v1)
is **yes only for their existing example \((3,2)\)**. This settles
that problem's full parameter domain, not the separate MSRD
Conjecture 6.21 of the same paper. At \(t=q\), the same conclusion
holds for the equivalent dual dimension \((q-1)m-1\) by the
source's same-profile MSRD duality (Lemma 6.3(ii)). Conjecture 6.21
concerns different
dimension/profile ranges.

The proof is analytic and independent of the finite-field checkers.
The central step is to lift a product of slope polynomials to
independent Frobenius-coordinate variables. Unique factorization
then forces a saturated disjoint packing on the projective line to
be the norm-fiber packing. The original MSRD system cannot produce
such packings consistently from all its projections.

## 1. The MSRD incidence criterion and the saturated projection

Write \(F\)-linear, \(K\)-linear, and spanning over the specified
fields explicitly. For \(t\) full blocks in dimension \(k=m+1\),
let \(U_i\subset K^k\) be the \(F\)-span of block \(i\)'s generator
columns, of \(F\)-dimension \(m\). The projective MSRD system
formulation in the source uses exactly these dimensions.
For a nonzero message, the block deficits from full rank are
\(\dim_F(U_i\cap H)\) for its \(K\)-hyperplane \(H\), by rank-nullity.
The dimension-\(k\) MSRD condition is equivalently
\[
 \sum_i\dim_F(U_i\cap H)\le k-1=m
 \qquad\text{for every \(K\)-hyperplane \(H\)}.                 \tag{1}
\]
This is also sufficient for full \(K\)-span when the total length is
at least \(k\), since a hyperplane containing all blocks would have
weight \(tm\ge k\); equality of the resulting distance with the
Singleton bound is standard and follows from the Hamming bound as
sum-rank is at most Hamming weight. Were a full block of an MSRD
code \(F\)-dependent, a blockwise invertible \(F\)-change followed
by deleting a zero column would preserve all sum-rank weights and
violate the shorter Singleton bound.

We will use the following consequence of (1): if at most \(k\) vectors
are selected and each block's selections are \(F\)-independent within
that block, then all selected vectors are \(K\)-independent. For if
\(r\le k\) selected vectors were \(K\)-dependent, extend the selection
within blocks to \(k\) vectors, using total capacity \(tm\ge k\).
Their \(K\)-span has dimension at most \(r-1+(k-r)=k-1\) and lies
in a hyperplane of weight at least \(k\), a contradiction.
In particular \(S_i:=\langle U_i\rangle_K\) has dimension \(m\),
so is a hyperplane in \(K^{m+1}\). Distinct blocks have distinct
\(S_i\), since \(m\) basis vectors of \(U_i\) plus one vector of
\(U_j\) cannot lie in an \(m\)-space.

Fix \(i\) and an \(F\)-hyperplane \(A\) of \(U_i\). Put
\(W=\langle A\rangle_K\), of dimension \(m-1\). For each \(j\ne i\),
\(U_j\) maps injectively over \(F\) into \(K^{m+1}/W\): a basis of
\(A\) together with any nonzero \(u\in U_j\) is independent over
\(K\). Moreover any two \(F\)-independent vectors of \(U_j\) remain
\(K\)-independent after projection, by the same argument with \(m+1\)
total vectors. Thus the projected space has \(F\)-dimension \(m\)
and is *scattered*, meaning every \(K\)-point contains at most an
\(F\)-line of it. Its projectivization has
\[
 \theta=(q^m-1)/(q-1)
\]
points. For two distinct indices \(j,\ell\ne i\), one nonzero vector
from each stays \(K\)-independent after the projection, so the
projective sets are pairwise disjoint. Likewise they all avoid
\(S_i/W\): take a vector of \(U_i\setminus A\) together with the
basis of \(A\) and one vector of another block. Here \(W\cap U_i=A\)
because the \(F\)-basis of \(U_i\) is \(K\)-independent.

The quotient is \(K^2\), with \(q^m+1\) projective points. At least
\(S_i/W\) is left over, so \((t-1)\theta\le q^m\), and
\(t\le q\), since \(q^m=(q-1)\theta+1\) and \(\theta>1\).
If \(t=q\), the \(q-1\) projected sets cover \(q^m-1\) points
and leave **two**: \(S_i/W\) and one other, say \(T_A/W\).
Here \(T_A\) is a \(K\)-hyperplane of \(K^{m+1}\) containing
\(W\), and \(T_A\ne S_i\).

## 2. Rigidity of the saturated projective-line packing

We prove a stand-alone lemma valid for all \(q\) and \(m\ge2\).

**Lemma.** Let \(q-1\) scattered rank-\(m\) \(F\)-subspaces of
\(K^2\) have disjoint projectivizations with exactly two uncovered
points. Put the uncovered points at \(0,\infty\) on the line
with coordinate \(z=y/x\). Then the underlying subspaces, not
merely the point sets, have graph forms
\[
 \{(x,a x^{q^s}):x\in K\},\qquad
 a\in K^\times,\quad 1\le s<m,\quad\gcd(s,m)=1.
 \tag{2}
\]
Their point sets are the \(q-1\) distinct nonzero norm fibers.

**Proof.** Avoiding \(0,\infty\) means both coordinate maps
on each \(F\)-subspace are \(F\)-linear bijections onto \(K\), so
that it is the graph of an invertible \(F\)-linear function \(f:K\to K\).
Write \(f(x)=\sum_{r=0}^{m-1}a_r x^{q^r}\). This representation is
unique and exhaustive: the \(m\) coefficients give \(q^{m^2}\)
\(F\)-linear maps without repetitions, since distinct polynomials
of degree less than \(q^m\) cannot agree at all \(q^m\) arguments,
and that is the total number of \(F\)-linear endomorphisms of \(K\).

Use indices \(0,\ldots,m-1\) modulo \(m\) and let the Dickson matrix
be
\[
 D_f[i,j]=a_{j-i}^{q^i},\qquad
 P_f(X_0,\ldots,X_{m-1})
   =\det\bigl(\operatorname{diag}(X_0,\ldots,X_{m-1})-D_f\bigr).
\]
The row formula gives \(D_f (x,x^q,\ldots,x^{q^{m-1}})^\top
=(f(x),f(x)^q,\ldots,f(x)^{q^{m-1}})^\top\).
Consequently every slope \(z=f(x)/x\), \(x\ne0\), is a root of
\(P_f(Z,Z^q,\ldots,Z^{q^{m-1}})\). This is a monic polynomial
of degree \(\theta\): the full variable product has coefficient
one, and all other monomials omit at least one variable.
Scatteredness gives exactly \(\theta\) distinct slopes, so these
are all its roots, with multiplicity one.

Let the \(q-1\) graphs have functions \(f_\ell\). Their slopes
partition \(K^\times\). Therefore
\[
 \prod_\ell P_{f_\ell}(Z,Z^q,\ldots,Z^{q^{m-1}})
      =Z^{q^m-1}-1 .
\]
Both the product of the \(P_{f_\ell}\) in independent variables
and \((X_0\cdots X_{m-1})^{q-1}-1\) have each variable degree at
most \(q-1\). Within that degree window the substitution
\(X_i=Z^{q^i}\) is injective: the exponent of \(Z\) is the unique
base-\(q\) encoding of the exponent vector. It follows that
\[
 \prod_\ell P_{f_\ell}(X_0,\ldots,X_{m-1})
 =\prod_{r\in F^\times}(X_0\cdots X_{m-1}-r).                  \tag{3}
\]
Each factor on the right is irreducible over \(K\): it is a
primitive polynomial linear in \(X_{m-1}\), with coprime
coefficient monomial and nonzero constant \(-r\). Unique
factorization, the individual variable degree bound 1, and
the leading full monomial coefficient 1 force each \(P_f\)
to equal a single right-hand factor, with each \(r\) used
once.

The coefficient of the product of variables off a set \(I\) is
\((-1)^{|I|}\det D_f[I,I]\). Thus every nonempty proper principal
minor is zero and the full determinant is nonzero. Draw a directed
edge \(i\to j\) when \(D_f[i,j]\ne0\), allowing loops. There is
a directed cycle since the full determinant is nonzero. In a
shortest directed cycle, the induced graph on its vertices has
only its cycle edges: any extra edge, together with the return
path along the cycle, produces a strictly shorter cycle.
The principal minor on those vertices is therefore a single
nonzero term. The cycle must use all \(m\) vertices, and its
edges must consequently be the entire graph.

A nonzero coefficient \(a_s\) provides *all* edges \(i\to i+s\).
It follows there is precisely one such coefficient, and the
shift must be a full cycle, i.e. \(\gcd(s,m)=1\). This is (2).
Finally the map \(x\mapsto x^{q^s-1}\) on \(K^\times\) has
image equal to the norm-one subgroup: it lies in that subgroup
and its kernel is \(F^\times\), the fixed scalars of the generating
Frobenius power. The slopes in (2) are accordingly the fiber
of norm \(N_{K/F}(a)\). \(\square\)

This recovers the classical linear-flock fact for \(m=2\)
(Baer sublines are the circles of the classical inversive plane).
For arbitrary \(m\), the **converse** about saturated packings and the
underlying graph spaces is exactly the portion used below. Merely
knowing that the displayed norm-fiber constructions exist would
not suffice.

## 3. Exclusion of \(q\) blocks for \(m\ge3\)

Assume \(t=q\) and use the notation of §1. Fix \(i\) and one
\(j\ne i\). Set \(Q_{ij}=S_i\cap S_j\), of \(K\)-dimension \(m-1\).
Choose an \(F\)-basis of \(U_j\), which is a \(K\)-basis of \(S_j\),
and let \(\sigma_j\) act by \(q\)-Frobenius on the coefficients in
that basis. It is a well-defined semilinear map, unchanged
by any \(F\)-basis change.

For every \(A\) as in §1, send the uncovered quotient points
\(S_i/W,T_A/W\) to the directions \(x=0,y=0\), respectively.
The two coordinate linear forms on the quotient restrict
to \(K\)-linear forms \(x,y\) on \(S_j\) via projection.
They are independent: the image of \(S_j\) has \(K\)-span
the whole quotient because two \(F\)-independent vectors from
its block project to \(K\)-independent vectors. The projective-line
lemma gives \(y(u)=a x(u)^{q^s}\) for \(u\in U_j\) with some
\(1\le s<m\), \(\gcd(s,m)=1\), depending on \(A,j\).
For a vector \(v=\sum_h\lambda_h e_h\in S_j\) in the chosen basis,
\[
 y(\sigma_j^s v)
   =\sum_h\lambda_h^{q^s} y(e_h)
   =a\!\left(\sum_h\lambda_h x(e_h)\right)^{q^s}
   =a\,x(v)^{q^s}.
\]
As \(S_i\) and \(T_A\) are distinct hyperplanes containing the
\((m-1)\)-space \(W\), their intersection is exactly \(W\).
Also \(\ker(y|_{S_j})=\sigma_j^s(\ker(x|_{S_j}))\), namely
\[
 T_A\cap S_j=\sigma_j^s(Q_{ij})\ne Q_{ij}.                     \tag{4}
\]
The inequality follows because the two forms are independent.
The choice of which carrier is \(x=0\) is allowed before the
lemma; interchanging them replaces a monomial graph bijection
by its inverse, with Frobenius index \(m-s\), still in the
specified range.

For each possible \(s\) with \(\sigma_j^s(Q_{ij})\ne Q_{ij}\), the
space \(D_s=S_i\cap\sigma_j^s(Q_{ij})\) is fixed independently
of \(A\) and has \(K\)-dimension \(m-2\): it is the intersection
of the distinct \(K\)-hyperplanes \(Q_{ij},\sigma_j^s(Q_{ij})\)
in \(S_j\). By (4), it is contained in \(S_i\cap T_A=W\).
In fact \(W\cap S_j=D_s\): \(W\) is not contained in \(S_j\)
as projection from \(W\) has rank two on \(S_j\).

Using an \(F\)-basis of \(U_i\) as \(K\)-basis of \(S_i\), the
spaces \(W=\langle A\rangle_K\) are exactly the distinct
hyperplanes with an \(F\)-coefficient normal vector, up to
scaling by \(F^\times\). The \(K\)-space of normal vectors
annihilating a fixed \(D_s\) is two-dimensional. Its
intersection with \(F^m\) has \(F\)-dimension at most two:
\(F\)-independent vectors with entries in \(F\) remain
\(K\)-independent, as seen from a nonzero minor.
Equivalently, the projective line of \(K\)-normals meets the
\(F\)-rational points in at most \(q+1\) points. Thus for each
\(s\) there are at most \(q+1\) eligible hyperplanes \(W\)
containing \(D_s\), and their union over all \(s\) has at most
\((m-1)(q+1)\) members.

But the number of \(F\)-hyperplanes of \(U_i\) is
\(\theta=1+q+\cdots+q^{m-1}\). For \(q\ge2,m\ge3\) it is larger
than \((m-1)(q+1)\): at \(m=3\) the difference is \(q^2-q-1>0\),
and each increase of \(m\) adds \(q^m>q+1\) to the first side.
This is the contradiction.

## 4. Exclusion for \(m=2,\ q\ge4\), and the exception

Now the \(S_i\) are projective support lines \(\ell_i\) in
\(\mathrm{PG}(2,K)\), and the projectivizations \(B_i\) are
Baer sublines, the projective \(F\)-line in each \(K\)-line
coordinatized by an \(F\)-basis of \(U_i\). No point of one block
lies on the other block's support: that would give weight
at least three on that line in (1). Nor are three points
from distinct blocks collinear.

For fixed \(i\) and \(P\in B_i\), \(W\) is the \(K\)-line representing
\(P\). The projected quotient line is the pencil of geometric
lines through \(P\). Its uncovered directions are \(\ell_i\) and
\(T_P\) where \(T_P\) is the unique tangent through \(P\) to the
union of block point sets, i.e. the only line meeting that union
just at \(P\). Indeed every direction other than the two uncovered
ones meets another block, and \(\ell_i\) contains all of \(B_i\);
a line through \(P\) other than \(\ell_i\) contains no other point
of \(B_i\).

We can apply the relation (4) also for \(m=2\), with \(s=1\)
now the only possibility. The induced \(\sigma_j\) on \(\ell_j\)
is the semilinear \(q\)-Frobenius in an \(F\)-basis of \(U_j\);
its fixed projective points are exactly \(B_j\). Thus the
point
\[
 R_{ij}:=\sigma_j(\ell_i\cap\ell_j)
\]
lies on \(T_P\) for **every** \(P\in B_i\).
Tangents for distinct \(P,P'\in B_i\) are distinct,
since their common supporting line through \(P,P'\) is \(\ell_i\),
not a tangent. All points \(R_{ij}\) for \(j\ne i\) are consequently
equal to the unique intersection \(R_i\) of two of those
tangents. The point \(R_i\) is on every \(\ell_j\), \(j\ne i\),
and not on \(\ell_i\): if it were on \(\ell_i\), it would equal
\(\ell_i\cap\ell_j\) and be fixed by \(\sigma_j\), contrary
to \(\ell_i\cap\ell_j\notin B_j\).

Take \(i=1,2\). When \(q\ge4\), both \(R_1,R_2\) belong
to \(\ell_3\cap\ell_4\) and coincide. But \(R_2\in\ell_1\) and
\(R_1\notin\ell_1\), a contradiction.

### \(q=3\): known existence and elementary normal form

For \(q=3,m=2\), the three distinct support lines of any
extremizer form a triangle, since each \(R_i\) is off
\(\ell_i\). For each \(j\), the two other indices show that
\(\sigma_j\) interchanges the two triangle vertices on \(\ell_j\).
After taking the triangle as the coordinate triangle, the
projective \(q\)-semilinear involution on a side with
vertices \(0,\infty\) has form \(z\mapsto r/z^q\), with
\(r\in F^\times\): swapping the vertices forces this shape,
and squaring gives \(z\mapsto (r/r^q)z\).
Its fixed points are \(N(z)=r\). The three sides may thus be
parametrized by \((0:1:z_0),(z_1:0:1),(1:z_2:0)\) with
\(N(z_i)=r_i\).

A transversal triple is collinear precisely if
\(1+z_0z_1z_2=0\), by the determinant.
Such a triple exists if and only if \(r_0r_1r_2=N(-1)=1\):
necessity follows by taking norms; for sufficiency choose
\(z_0,z_1\) of the desired norms and then set
\(z_2=-1/(z_0z_1)\). Therefore valid triples over \(F=\mathbb F_3\)
have product \(r_0r_1r_2=-1\), and do exist.
The source construction (Theorem 6.18) has \(r_0=r_1=r_2=-1\).
A common diagonal coordinate transformation multiplies the
three radii by arbitrary norm ratios with product \(1\);
conversely any such three ratios are obtained by choosing
the three scalar norms consecutively. Hence the associated
*projective configurations* form one \(\mathrm{PGL}(3,9)\)-orbit.
This is a direct algebraic normal form, not a separate novelty
claim: see the computational classification of 12-point
semiovals in Bartoli–Marcugini–Pambianco, cited below. The
assertion is about point blocks, not all notions of sum-rank
code or generator-matrix equivalence.

## 5. The attained \(q-1\) lower bound

For completeness the standard linearized Reed–Solomon
construction gives \(q-1\) full blocks for every dimension
\(1\le k\le(q-1)m\), in particular \(k=m+1\) here.
Here is the short root-count proof.

Take \(q-1\) elements \(a_i\in K^\times\) with distinct
nonzero norms, and set \(D_{a_i}(x)=a_i x^q\).
For \(P(T)=\sum_{\nu=0}^d p_\nu T^\nu\), use the skew
multiplication \(T c=c^q T\), so that substitution of the
operator \(D_a\), with coefficients acting by multiplication,
is multiplicative. If a nonzero \(y\) is killed by
\(P(D_a)\) in any block, put \(b=a y^{q-1}\).
Right division by \(T-b\) has scalar remainder (successive
leading-term cancellation), and evaluating at \(y\) shows
the remainder is zero. Thus \(P(D_{a_i})=R(D_{a_i})
\circ(D_{a_i}-b)\) for a polynomial \(R\) of degree \(d-1\).
The sum of kernel dimensions of \(D_{a_i}-b\) is \(1\):
a nonzero root needs \(N(a_i)=N(b)\), possible for just
one \(i\), and its solution space is a one-dimensional
\(F\)-line since quotients of two nonzero roots lie in \(F\).
Kernel dimension of a composition is at most the sum of
the two kernel dimensions. Induction, with the trivial
case of no roots and the nonzero scalar base, gives
\(\sum_i\dim_F\ker P(D_{a_i})\le d\).

For each block evaluate \(P(D_{a_i})\) on an entire \(F\)-basis
of \(K\), using the \(k\) coefficients of \(P\) of degree less
than \(k\) as the message. The resulting \(K\)-linear evaluation
is injective, since every nonzero message has sum-rank at least
\((q-1)m-(k-1)>0\). The distance attains the Singleton bound.

## 6. Attribution, boundaries, and exact replay

* V. Astore and F. Zullo, [*On the Length of Maximum Sum-Rank Distance
  Codes*](https://arxiv.org/pdf/2610.23633v1), arXiv:2610.23633v1,
  16 October 2026. Problem 6.16 (PDF p. 24) asks the full-block
  existence question for \(q\ge3,m\ge2,k=m+1,t=q\);
  Proposition 6.17 gives the saturated projection description;
  Theorem 6.18 (PDF p. 25) supplies the existing \((3,2)\) example.
  Remark 6.19 gives only three blocks in its extension to other \(q\),
  not \(q\) blocks. The paper's distinct Conjecture 6.21 is not
  answered here.
* The classical case \(m=2\) of the line packing rigidity is
  the linear-flock theorem for the classical inversive plane,
  due to Orr and Thas. See J. C. Fisher and J. A. Thas,
  [*Flocks in PG(3,q)*](https://doi.org/10.1007/BF01214908),
  Math. Z. **169** (1979), 1–11, §3, Theorems 3.1 and 3.2(b)
  for the elliptic case (also [their argument in the odd case,
  p. 4](https://gdz.sub.uni-goettingen.de/fulltext/PPN266833020_0169/00000012?_format=xml)).
  These are elliptic-quadric/ovoid flocks of \(q-1\) pairwise
  disjoint circles with two carrier points, not cone flocks.
  The derivation in §2 does not require the classical theorem.
* G. Lunardon, G. Marino, O. Polverino and R. Trombetti,
  [*Maximum scattered linear sets of pseudoregulus type and the
  Segre Variety*](https://arxiv.org/abs/1211.3604), §4 after
  Definition 4.1, already give the norm-fiber packing
  with two prescribed transversals. B. Csajbók and
  C. Zanella, [arXiv:1506.08875](https://arxiv.org/abs/1506.08875),
  give related projection and representation results for
  pseudoregulus-type sets. P. Santonastaso and J. Sheekey,
  [DOI 10.1002/jcd.21972](https://doi.org/10.1002/jcd.21972),
  develop MSRD and disjoint scattered sets in related dimensions.
  We do not claim novelty of finite-field norms, Dickson
  matrices, or the pseudoregulus construction.
* U. Martínez-Peñas,
  [*Skew and linearized Reed–Solomon codes and maximum sum rank
  distance codes over any division ring*](https://arxiv.org/abs/1710.03109),
  J. Algebra **504** (2018), 587–612, [DOI 10.1016/j.jalgebra.2018.02.005](https://doi.org/10.1016/j.jalgebra.2018.02.005),
  is the source of the lower-bound
  construction used in §5.
* D. Bartoli, S. Marcugini and F. Pambianco,
  [*Semiovals in PG(2,8) and PG(2,9)*](https://arxiv.org/abs/1312.2485),
  Tables 6–7, already record one semilinear orbit of size-12
  semiovals with intersection counts \(28,12,48,0,3\).
  The example here is such a semioval, and its point blocks are
  canonically its three 4-secants. The short normal form in §4
  recovers the corresponding projective statement without
  making a first-classification claim.

Searches on 27 November 2026 for the precise problem, *full blocks*,
*disjoint maximum scattered linear sets*, *pseudoregulus partitions*,
and *Orr–Thas flocks* did not find the application proving the
complete parameter exclusion. This is a bounded literature check.

Finite regressions (Python 3 standard library only; neither imports
the other):

    python3 verify_packing.py
    python3 verify_codes.py

The first checks projective-line packings and independent determinant
polynomials in small fields. The second verifies explicit attaining
codes directly and checks the carrier relations on the \((3,2)\)
configuration, with negative controls. These finite checks illustrate
the arguments only; the general exclusion is the proof in §§1–4.
