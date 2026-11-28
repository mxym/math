# Dyadic multiplication matrices: the exact binary and TU frontier

**Scope.** An explicit family of multiplication matrices over a supplied
finite-dimensional polynomial algebra is considered as a column
configuration. We identify when this configuration can be represented
by a totally unimodular matrix, give a small structural obstruction, and
compute when some special matrices first fail the local minor tests.
This is a statement about the given coefficient matrices, not about
random noisy observations, inference, or any cryptographic scheme.

Write \(R_F=F[X]/(X^n+1)\), with the coefficient basis in increasing
degree, and let \(M_f\) be the matrix of multiplication by \(f\).
Unless otherwise indicated \(n=2^s\), \(s\ge 0\). A monomial is a nonzero
scalar times one power of \(X\) in this basis.

## 1. Classification

**Theorem 1.** Let \(F\) have characteristic different from two with
\(-1\) not a square (including any ordered field). Let the explicitly
given horizontal family
\[
 D=[\,M_{f_0}\mid M_{f_1}\mid\cdots\mid M_{f_\ell}\,]
\]
contain a unit \(f_0\in R_F\). Its column matroid is binary if and only if
each \(f_i/f_0\) is zero or a monomial. Equivalently the column matroid is
regular. If this condition fails, there is an explicit four-element
uniform rank-two minor \(U_{2,4}\). Thus changing the row basis and
projectively rescaling columns cannot make a failing family representable
by a totally unimodular matrix. Over \(\mathbb Q\) the criterion and the
minor witness are deterministic polynomial time in the coefficient
input bit length.

**Corollary 2.** For integral \(f\), \(M_f\) itself is totally unimodular
if and only if \(f=0\) or \(f=\pm X^j\). The same condition on each block
characterizes total unimodularity for a horizontal family of integral
blocks in the original coefficient basis. For any nonmonomial with
entries already in \(\{0,\pm1\}\), the obstruction below gives a
subdeterminant of absolute value exactly 2, not just a determinant
exceeding one in magnitude.

### 1.1 A two-term block extracted by dyadic residues

Let \(h\) be a polynomial of degree less than \(n\) with at least two
nonzero coefficients. Let \(v\) be the maximum 2-adic valuation of
the difference of two distinct positions in its support, and set
\(g=2^v\), \(m=n/g\). Here \(1\le g<n\) and \(m\ge2\) is even.
Choose a pair attaining the maximum, and let \(r\) be its common
residue modulo \(g\), \(0\le r<g\). The chosen residue cannot contain
a third support position, since two of three positions would agree
modulo \(2g\), contrary to the maximum.

In \(M_h\) restrict to rows \(r+gi\) and columns \(gj\),
\(0\le i,j<m\). Only the two selected coefficient positions contribute.
Write them as \(r+g\alpha,r+g\beta\), \(\alpha<\beta\), with values \(a,b\).
The block is
\[
   aP_m^\alpha+bP_m^\beta,\tag{1}
\]
where \(P_m\) is the shift on \(m\) positions with a minus sign at wrap.
Indeed multiplying \(X^{r+g\alpha}\) by \(X^{gj}\) wraps precisely when
\(\alpha+j\ge m\). The difference \(\beta-\alpha\) is odd. Consequently
\(P_m^{\beta-\alpha}\) is one cycle with sign product \(-1\):
its unsigned permutation is transitive and its \(m\)-th power is
\(-I\). After applying the signed row permutation \(P_m^{-\alpha}\),
the block is \(aI+bP_m^{\beta-\alpha}\). Its determinant is
\[
     a^m+b^m.\tag{2}
\]
For example, the determinant expansion has only the identity term and
the full cycle term, the latter positive relative to the \(b^m\)
monomial since \(m\) is even and the cycle sign product is \(-1\).
It is nonzero when \(-1\) is not a square, and equals 2 in absolute
value for two coefficients of magnitude 1 over the integers.
These conclusions concern the isolated block even if \(\det M_h\)
itself is zero or a unit. Over any other field the witness still works
at a given pair whenever (2) is nonzero.

### 1.2 Binary representability and the four-column obstruction

Normalize the reference block of \(D\) on the left by \(M_{f_0}^{-1}\).
The family becomes \([I,M_{h_1},\ldots,M_{h_\ell}]\) with
\(h_i=f_i/f_0\). If all ratios are zero or monomial, every nonzero
column is a scalar multiple of one basis column. After rescaling,
there is a totally unimodular representation with the same column
matroid, and the same parallel classes give a representation over
every field.

Otherwise apply (1) to a multi-term ratio, contract the reference
basis columns outside the selected rows, and delete all columns except
the \(m\) remaining reference columns and the \(m\) chosen ratio columns.
This is the column configuration \([I_m,\text{block }(1)]\) up to
a permutation. Signed row and reference-column permutations, followed
by a common cyclic reorder, put these extra columns in the form
\[
 c_j = a e_j + b\epsilon_j e_{j+1},
 \qquad j=1,\ldots,m,\quad e_{m+1}=e_1,\quad
 \epsilon_j\in\{1,-1\},\quad \prod_j\epsilon_j=-1.
\]
Contract \(c_1,\ldots,c_{m-2}\) (nothing if \(m=2\)). They are
independent. In the quotient the images of \(e_1,\ldots,e_{m-1}\)
are nonzero multiples of one vector, while \(e_m\) is an independent
second vector. Both of the remaining extra columns have nonzero
coefficients in both these directions; their images are independent
because (2) was nonzero. Retain exactly \(e_1,e_m,c_{m-1},c_m\).
All six pairs are independent in rank two. This is the promised
\(U_{2,4}\).

Binary linear representations are closed under contraction and deletion,
and a binary 2-space has only three nonzero lines. Thus \(U_{2,4}\)
itself rules out every binary representation, without needing an
excluded-minor theorem in the other direction. A TU representation
would be binary by reducing its integer entries modulo two: all
nonzero minors are then preserved. This proves Theorem 1. Over
\(\mathbb Q\), every nonzero reference polynomial is a unit since
\(X^n+1=\Phi_{2n}\) is irreducible. Use polynomial-bit exact rational
linear algebra to compute the ratios, search the support for the
largest \(v\), and output the stated deletion and contraction indices.
The powers, matrices, and coefficient vectors here are explicitly
sized in \(n\); no claim is made for a compressed binary encoding of
the dimension itself.

For Corollary 2, an entry of magnitude greater than one fails a
\(1\times1\) test; if the coefficients are already in
\(\{0,\pm1\}\) and not monomial or zero, (1)–(2) supply the bad minor.
The positive family has at most one unit entry in each column, which
directly makes every square determinant \(0,\pm1\). A tuple of
different scalar monomials after changing row and column coordinates
classifies projective representability only; such rescaling is not
automatically an equivalence of integer programs with unchanged
integrality constraints.

### 1.3 Scope of the field and a finite arithmetic frequency

The square-root-of-minus-one hypothesis cannot simply be omitted from
the stated result allowing arbitrary nonreference blocks. For
\(n=2\) and \(i^2=-1\) in characteristic different from two,
\(h=1+iX\) is not a monomial, but \(M_h\) has two parallel nonzero
columns, neither parallel to a reference column. The resulting
three distinct lines in rank two, with one duplicate, form a binary
matroid. This example does not settle the extension over such fields
if every block is required to be a unit.

For \(F=\mathbb F_q\), \(q\equiv 3\bmod 4\), fix a unit \(f_0\) and
draw the other \(\ell\) polynomials independently and uniformly.
Multiplying by \(f_0^{-1}\) is a bijection, so the exact passing
probability is
\[
       \left(\frac{1+n(q-1)}{q^n}\right)^\ell .
\]
If the draws instead range uniformly over units, the exact probability
is \(\bigl(n(q-1)/|R_F^\times|\bigr)^\ell\). The usual CRT count here
is \(|R_F^\times|=q^n\prod_P(1-q^{-\deg P})\), over the distinct
irreducible factors \(P\) of \(X^n+1\); there are no repeated factors
since the characteristic is odd. These are frequencies of the
specified abstract matrix property, not of any sample-based model.

## 2. The witness order can be large even for a unimodular trinomial

Let \(n\ge3\), not necessarily dyadic, and \(P=P_n\). For an integer
\(1<w<n\), put
\[
    W_w=I+P+\cdots+P^{w-1}
        =(I-P)^{-1}(I-P^w).
\]
On the residues modulo \(n\) make a signed multigraph with a step-one
and a step-\(w\) edge from each residue \(j\), oriented in the positive
direction. An edge has negative sign if its positive step wraps.
A cycle is unbalanced if its sign product is \(-1\). Parallel edges,
if any, retain their types. A cycle's step-\(w\) count refers to its
edges of that type, regardless of traversal orientation.

**Theorem 3.** The least order of a minor of \(W_w\) whose absolute
value exceeds one is exactly the least total step-\(w\) count of two
vertex-disjoint unbalanced cycles, interpreted as infinity if no such
pair exists. The maximum absolute minor is \(2^{t-1}\), where \(t\)
is the maximum number of vertex-disjoint unbalanced cycles. In
particular,
\[
 \text{least bad order}\ \ge\ \left\lceil\frac{n}{w-1}\right\rceil .
\]
If \(2(w-1)\mid n\) and \(w<n\), equality holds, achieved by a
principal minor of absolute value 2. For dyadic \(n\) and
\(w=2^a+1,\ 1\le a\le s-1\), the maximum-residue witness from
Theorem 1 therefore has the best possible order for this window.

### 2.1 Completing a minor into a signed incidence determinant

For a \(k\times k\) minor of \(W_w\) indexed by row set \(A\) and
column set \(B\), complete the \(k\) columns from \(W_w\) by using
the reference columns \(e_i\), \(i\notin A\). The resulting absolute
determinant is the absolute minor. Multiplying by \(I-P\) multiplies
its absolute determinant by 2, and the columns become exactly the
signed graph edge columns, \(k\) of type \(w\) and \(n-k\) of type one.
For any \(n\) selected edge columns, if the determinant is nonzero,
every connected component has equally many vertices and edges.
Otherwise some component has fewer columns than rows and the square
matrix loses rank. Each component is unicyclic. Expand off tree leaves;
the remaining cycle contributes absolute determinant 2 for an
unbalanced cycle and 0 for a balanced one. Thus any nonzero minor
equals \(2^{c-1}\) in magnitude, \(c\) the number of selected
unbalanced components. This is also the standard signed incidence
determinant calculation (Zaslavsky, Lemma 8A.2).

Conversely, any collection of vertex-disjoint unbalanced cycles can
be completed to such a full determinant by attaching the other
vertices using only step-one edges and never merging two of the
selected cycles. Start from all cycle vertices. As long as a vertex
is unreached, the connected step-one edge cycle has an edge from
the reached set to an unreached vertex. Include it and add that vertex
to the same component. This adds no cycle and no type-\(w\) edge.
All possible selections of \(n\) distinct typed edges arise from a
minor by setting \(B\) to the tails of selected type-\(w\) edges and
taking \(A\) to be the complement of the tails of selected type-one
edges. Different types may share a tail, which does not matter.
The exact least order and maximum now follow in both directions
by retaining two cycles or as many disjoint cycles as possible.
The step-one full cycle is unbalanced, so \(t\ge1\).

### 2.2 A sharp local witness scale

For an unbalanced cycle, lift its traversal to \(\mathbb Z\), with
steps \(\pm1\) or \(\pm w\). The total signed displacement is an
odd multiple of \(n\): each wrapped edge traversed forward or backward
changes the integer wrap counter by an odd increment, in agreement
modulo two with the edge sign. Thus the sum of absolute step lengths
is at least \(n\) on each unbalanced cycle. In an edge selection
corresponding to a size-\(k\) bad minor, at least two such cycles occur.
The total absolute step length of all \(n\) selected edges is
\(n+(w-1)k\); hence \(n+(w-1)k\ge2n\).

When \(2(w-1)\mid n\), color cyclic runs of \(w-1\) consecutive residues
alternately in two colors. For each color traverse all its vertices
in increasing cyclic order. Within a run take steps of length one;
from the last vertex of a run to the first vertex of the next run of
that color the step is exactly \(w\). The two cycles are disjoint,
cover every vertex, and each wraps once, with total \(n/(w-1)\)
long edges. The tails of all selected edges occur once, so sets
\(A\) and \(B\) coincide. This gives the exact principal minor witness.

For \(n=2^s\), \(w=2^a+1\), the maximal 2-adic support collision
of \(1+X+\cdots+X^{w-1}\) has \(g=w-1\); the upper witness size
\(n/g\) from (1) meets this lower bound. In these examples the full
determinant is 1 in absolute value: \(\gcd(w,n)=1\), so \(P^w\)
has one signed cycle of negative sign product and
\(\det(I-P^w)=\det(I-P)=2\). In particular, for the three-term
window \(w=3\), every proper-order test below \(n/2\) passes while
a principal \(n/2\)-minor fails. This is not an obstruction confined
to matrices with a large full determinant and distinguishes a
total-unimodularity certificate from a unit-norm test.

## References and comparison

* [Tutte, *A homotopy theorem for matroids. I* (1958)](https://doi.org/10.1090/S0002-9947-1958-0101526-0).
  The binary obstruction \(U_{2,4}\) is classical; Section 1 directly
  exhibits its deletion/contraction in the stated coefficient family.
* [Zaslavsky, *Signed graphs*, Discrete Applied Mathematics 4 (1982)](https://doi.org/10.1016/0166-218X(82)90033-6),
  [paper copy](https://davinci.fmph.uniba.sk/~matok1/diplomovka/sources/Zaslavsky-former.pdf),
  Lemmas 8A.2–8A.3. The signed incidence determinant fact is standard;
  the minor-order formula and its sharp window use the particular
  \(I-P\) normalization and step lengths.
* [Beck and Hoşten, *Cyclotomic polytopes and growth series of
  cyclotomic lattices*](https://arxiv.org/abs/math/0508136) treats
  the root-of-unity column configuration, not coefficient matrices
  for arbitrary multiplication blocks. [Williams, *Unimodular
  integer circulants associated with trinomials*](https://repository.essex.ac.uk/1810/1/UnimodularIntCirculants.pdf)
  treats the determinant of ordinary circulants \(X^n-1\), not
  all minors of anti-periodic matrices \(X^n+1\).
  Neither precedent is a claim that projective recognition was
  previously unresolved. This note isolates the exact statement and
  the elementary witness for the specified dyadic setting.

The companion checks use generated integer coefficient arrays, exact
determinants, and finite signed multigraphs. They are finite
cross-checks, not substitutes for the proof.
