# Complete equality classification on the imaginary coefficient axis

This is the equality proof supplement to [PAPER.md](PAPER.md), with the same
author, date, attribution, rights and scope declarations. All matrices below
are actual complex matrices. Put beta = 3/2 - 1/sqrt(3).

## 1. Exact statement

For every real t and complex 4 by 4 matrix A, equality in

    |per A + i t det A| <= max{3/2, |t|+1/sqrt(3)} product_i ||A_i||_2

holds exactly as follows. A zero row always gives equality. Otherwise normalize
each row to unit length and call the resulting matrix B.

* If |t| < beta, B has rank one and every entry has modulus 1/2.
* If |t| = beta, B is either such a rank-one matrix, or a unitary matrix
  equivalent to F_3 direct-sum [1] under row and column permutations and
  multiplication of rows and columns by complex numbers of modulus one,
  with the additional orientation condition

      per B = i sign(t) det B / sqrt(3).                     (E1)

* If |t| > beta, exactly the latter oriented Fourier-block class occurs.

Here F_3 is the explicitly defined normalized Fourier matrix in PAPER Section 5.
The equivalence relation alone does not fix the sign in (E1): an odd row or
column permutation reverses it. The orientation condition is therefore part
of the classification. Arbitrary nonzero complex row scalings of the stated
matrices give the unnormalized equality matrices; the ratio per/det and the
equality are unchanged by those scalings. No restriction to unitary optimizers
is assumed: unitarity in the non-flat class is a conclusion of the proof.

## 2. A consequence of the exact boundary certificate

Assume the rows are nonzero, normalize them, and first take t=beta. Equality
means that the product-vector expectation of the left side of (I3) is zero.
Each summand on its right is nonnegative by (I4); hence every summand is zero.
For the first Gram block the transpose subset is empty, the six basis tuples are

    (0,0,1,1), (0,1,0,1), (0,1,1,0),
    (1,0,0,1), (1,0,1,0), (1,1,0,0),

and N_0 has columns e_1-e_0, ..., e_5-e_0. Its Z_0 is positive definite,
because its LDL factor is unit lower triangular and its five pivots are
strictly positive. Thus zero expectation
forces N_0* g* u(A)=0 for every g in the 288-element group G.

Consequently, for any two distinct columns a,b of A, the six products

    product_(i in J) A_(i,a) product_(i not in J) A_(i,b),  |J|=2,           (E2)

are all equal. To see that every column pair is covered, choose any column
permutation mapping {0,1} to {a,b}; if it is odd, compose with an odd row
permutation. This gives an element of G. Row permutations merely permute the
six expressions in (E2), and complex conjugation in u(A) preserves equality.
This step uses the actual supplied exact matrix N_0, not a numerical nullspace.

## 3. A universal support lemma

**Lemma.** An invertible complex 4 by 4 matrix satisfying (E2) has a row or
a column with exactly one nonzero entry.

**Proof.** Let S_a be the set of nonzero rows in column a. Suppose two columns
have |S_a|,|S_b| >= 2 and S_a union S_b equal to all four rows. One can assign
two rows to a and the other two to b within their supports: the rows absent
from b must be assigned to a, and there are at most two of them; fill this
set to size two with rows of S_a while leaving two available rows of S_b.
Equivalently, choose a two-element J with J subset S_a and J^c subset S_b.
Thus one expression in (E2) is nonzero. Since they are all equal, all six are
nonzero. Every entry in both columns is then nonzero. Writing r_i=A_(i,a)/A_(i,b),
equality says that r_i r_j is independent of the two-element set {i,j}.
Canceling the nonzero factors gives r_1=r_2=r_3=r_4. The two columns are
proportional, contradicting invertibility.

If there is a singleton column we are done. Otherwise every S_a has at least
two elements, and the preceding argument shows |S_a union S_b| <= 3 for
each distinct pair. A four-element S_a is impossible. If some S_a has three
elements, all the other S_b must lie in it; the fourth row is zero, also
impossible. Thus all S_a are two-element sets, and they intersect pairwise.
Any pairwise-intersecting family of two-element subsets is either contained
in a triangle on three vertices or has a common vertex. Indeed, after two
distinct sets are written {v,x},{v,y}, a set not containing v must be {x,y};
the presence of that set prevents any fourth vertex from appearing. The
triangle case leaves a zero row. In the common-vertex case invertibility
requires all three other vertices to occur. Four columns distributed among
the three sets {v,x},{v,y},{v,z} have multiplicities 2,1,1. The two leaves of
multiplicity one give singleton rows. This proves the lemma. QED.

The argument is exact for complex entries, including all possible zero
patterns and cancellations. It uses invertibility to exclude proportional
columns and a zero row; it does not assume generic nonzero entries.

## 4. The three-row boundary has only Fourier equality

We give the needed specialization of the repository's already proved
[full three-row complex pencil](../../notes/complex-permanent-determinant/PAPER.md),
including its equality derivation, so no new optimizer assumption is imported.
For epsilon in {-1,1}, every complex 3 by 3 matrix C obeys

    |per C + i epsilon beta det C| <= (3/2) product_i ||C_i||_2.             (E3)

If its rows are nonzero, equality holds exactly for normalized Fourier
matrices, equivalent to F_3 by row/column phases and permutations, with
per C / det C = i epsilon / sqrt(3).

To prove this, normalize the rows and write them a,b,c. The exact last-row
expansion is c^T M_lambda(a)b, with M_lambda given in the linked note and
lambda=i epsilon beta. Put B=9/4, q=beta^2 and

    h=B-1-q=sqrt(3)-4/3 > 0.

The note proves H=B||a||^2 I - M_lambda(a)* M_lambda(a) is positive
semidefinite; its complete norm formula gives (E3), since the unique dominant
branch at this coefficient is beta+1/sqrt(3)=3/2. More explicitly,
sqrt(1+beta^2)<3/2 and 2/sqrt(3)<3/2.

For X=|a_1|^2, Y=|a_2|^2, Z=|a_3|^2, the note's exact determinant identity
specializes to

    det H = B h^2 (U+3V),                                  (E4)
    U=X^3+Y^3+Z^3-3XYZ >= 0,
    V=(X+Y+Z)(XY+YZ+ZX)-9XYZ >= 0.

The remaining coefficient is zero because
[3(B-q)-1]^2-12q=0. Equality in (E3) forces ||M_lambda(a)b||=3/2;
therefore H has a nonzero kernel vector and det H=0. Since B h^2>0,
(E4) forces U=0. AM-GM gives X=Y=Z, including the zero-coordinate cases;
the nonzero row and its normalization give X=Y=Z=1/3.

Column phases now make a=(1,1,1)/sqrt(3). The matrix M_lambda(a) is a normal
circulant with eigenvalues

    2/sqrt(3), -1/sqrt(3)-epsilon beta, -1/sqrt(3)+epsilon beta.

Exactly one has modulus 3/2; the other two have strictly smaller modulus.
Thus b is, up to phase, its unique Fourier eigenvector. Equality in complex
Cauchy-Schwarz in c^T M_lambda(a)b forces c to be the conjugate Fourier
vector, up to phase. The three rows are mutually orthonormal and have all
entries of modulus 1/sqrt(3). This gives the stated Fourier equivalence.
Their permanent has modulus 1/sqrt(3) and determinant has modulus one;
equality in the triangle inequality then forces per C / det C to be
i epsilon/sqrt(3). Conversely that oriented Fourier matrix attains (E3).

## 5. Boundary equality is flat or an oriented Fourier block

If det A=0, boundary equality reads |per A|=3/2 after row normalization.
The elementary permanent endpoint itself has only flat rank-one equality.
Indeed, for any chosen row pair the inequalities in PAPER Section 2 give
S<=3/2, and equality of the permanent bound forces equality for every pair.
For unit rows,

    3/2 - S = (1/2)(1-eta) + 2(tau-eta/4).

Both terms are nonnegative, so each pair is proportional and equimodular.
Hence all normalized rows are proportional and every entry has modulus 1/2.

If det A is nonzero, the support lemma applies. Suppose first row i is
supported only in column j, with nonzero entry a. Deleting that row and
column gives an invertible 3 by 3 matrix C and exact Laplace identities

    per A=a per C, det A=epsilon a det C, epsilon in {-1,1}.

Applying (E3),

    |per A+i beta det A|
      <= (3/2)|a| product ||C_row||
      <= (3/2) product ||A_row||.

Boundary equality forces both inequalities to be equalities. Each of the
three remaining rows has nonzero restriction to C, so equality in the
product of row-norm inequalities forces its column-j entry to vanish.
Thus A is a 3 by 3 block direct-sum [a], up to row/column permutations, and
the 3 block is precisely the oriented Fourier equality class from Section 4.

If instead a column is a singleton, its three other entries are already
zero. The same Laplace expansion applies; equality now forces the row
containing a to have norm |a|, so that row is a singleton too. The same
Fourier-block conclusion follows. No column-norm estimate is used.

In particular, after row normalization the non-flat class is unitary and
per A / det A=i/sqrt(3). The latter orientation follows either from the
signed Laplace identity or from equality at beta, since the Fourier block
has |per A|=1/sqrt(3), |det A|=1. Conversely every such oriented Fourier
block is an equality matrix at beta. Entrywise conjugation proves the
negative-boundary classification.

## 6. The open branches and the transition

For 0<t<beta, the interpolation in PAPER Section 4 has two strictly positive
weights. Equality at constant 3/2 requires |per A|=(3/2)R(A), hence the
flat rank-one class. At t=0 this is the permanent endpoint itself. Negative
t follows by conjugation.

For t>beta, equality in

    |per A+i t det A| <= |per A+i beta det A|+(t-beta)|det A|
                      <= [3/2+t-beta]R(A)

requires both boundary equality and |det A|=R(A). The flat class has zero
determinant and is excluded; exactly the oriented Fourier-block class remains.
It attains equality because per A=i det A/sqrt(3). Conjugation handles
t<-beta. Section 5 already treats both transition parameters, completing
all directions and all real t. A zero row makes both sides zero and was
separated at the start.

## 7. Verification boundary

The universal analytic proof above uses the already exact boundary identity
and the proved three-row Hermitian identity. The companion checker verifies
the actual first Gram block is the difference matrix used here, exhaustively
checks the finite zero-support implication, and checks (E4), its positive
coefficient, and the distinct Fourier singular values over Q(sqrt(3),i).
The support argument is also proved directly in Section 3, independently of
the enumeration. The checker is neither a substitute model for complex
matrices nor a finite sample of input matrices. This is a complete written
equality proof with exact algebraic verification; no Lean or external human
peer-review claim is made.
