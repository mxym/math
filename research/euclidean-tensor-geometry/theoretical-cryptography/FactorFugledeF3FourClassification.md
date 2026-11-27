# Classification of all spectral non-tiles in the ternary four-space

Let \(G=\mathbf F_3^4\). A nonempty subset \(A\subset G\) is
*spectral* if it has a spectrum \(B\subset G\) of cardinality \(|A|\):
the matrix \((\omega^{a\cdot b})_{a\in A,b\in B}\), \(\omega=e^{2\pi i/3}\),
has orthogonal columns. A set tiles when it has a translational tiling
complement in \(G\).

**Theorem.** A subset of \(G\) is spectral if and only if it tiles or is
affinely equivalent to
\[
          \{0,e_1,e_2,e_3,e_4,-e_1-e_2-e_3-e_4\}.             \tag{1}
\]
In particular, spectral cardinalities are exactly \(1,3,6,9,27,81\).
There is one affine class of spectral non-tiles, comprising exactly
\(2\,729\,376\) actual subsets. The only computer-assisted exclusion
is cardinality \(18\); the exact checker below proves that exclusion
over the whole finite space, not only among algebraic examples.

The six-point counterexample is the classical cubic log-Hadamard
example appearing in [Tao's work](https://doi.org/10.4310/MRL.2004.v11.n2.a5)
and [Aten et al.](https://arxiv.org/abs/1509.01090);
[Ferguson–Sothanaphan](https://arxiv.org/abs/1901.08734) explain that
the implication spectral \(\Rightarrow\) tile fails in dimension four
over every odd prime field. [Fan–Zhang, Corollary 1.11(3)](https://arxiv.org/html/2408.12901)
already prove that every tile in \(\mathbf F_3^4\) is spectral.
The new direction here is a classification of every spectral non-tile
in this particular space, rather than demonstrating a single
counterexample or extending the result to other fields.

## 1. Exact character conditions

For any \(v\in G\), let \(Z(A)\) contain \(v\) if the three counts
\(\#\{a\in A:a\cdot v=i\}\), \(i=0,1,2\), are equal. If \(A\ne\varnothing\)
then \(0\notin Z(A)\); every nonzero point of \(Z(A)\) represents a whole
projective direction \(\{v,2v\}\). The vanishing of the character sum is
equivalent to equality of the three counts, by \(1+\omega+\omega^2=0\)
and \(\omega\notin\mathbb R\). A spectral pair of size \(m\) therefore
has
\[
                  (B-B)\setminus\{0\}\subseteq Z(A).
\]
The condition is sufficient when \(|A|=|B|\), and the pair is symmetric
because a square matrix with columns of equal norm and mutually
orthogonal also has orthogonal rows. Translations in either set preserve
the condition. Applying an invertible linear transformation \(L\) to
\(A\) and \(L^{-\mathsf T}\) to \(B\) preserves it as well.

If \(m>1\) then \(3\mid m\). If \(m>27\), \(B\) has a difference in every
nonzero projective direction: there are just 27 cosets of any line, so
some coset contains two members of \(B\). Then all nonzero Fourier
coefficients of \(A\) vanish and Fourier inversion shows \(A=G\).
For a spectral pair of size \(3^{d-1}\) in a \(d\)-dimensional ternary
space, each member tiles by a line. Indeed, the other member's
indicator is not constant, so there is a nonzero direction at which its
Fourier coefficient is nonzero. The first member has no differences
along that line; it is therefore a complete set of representatives.
Symmetry gives the same conclusion for the second member.
This settles \(m=27\) here. For \(m=3\), select any nonzero difference
from \(B\): the associated scalar projection bijects \(A\) onto
\(\mathbf F_3\), giving a hyperplane tiling complement.

## 2. Quadratic moments and the cases other than 18

Normalize \(0\in A\cap B\). In the field \(\mathbf F_3\) write
\[
       Q_A(v)=\sum_{a\in A}(a\cdot v)^2,\qquad
                 c=2m/3\pmod3.
\]
For every nonzero difference \(v\) from \(B\), \(Q_A(v)=c\).
If \(c\ne0\), the Gram matrix of the \(m-1\) nonzero vectors of \(B\)
for the symmetric bilinear form of \(Q_A\) is
\((c/2)(I+J)\), where \(J\) is the all-ones matrix.
Indeed the diagonal entries are \(c\); polarization of \(Q_A(b-b')\)
gives off-diagonal \(c/2\).
The Gram matrix has rank \(m-2\), since \(3\mid m\) and its kernel
is the constant vectors. As its rank is at most four, \(m\le6\).
This reduces proper non-singleton cardinalities to \(3,6,9,18,27\).

For \(m=6\), any four of the five nonzero vectors of \(B\) are independent:
the principal Gram matrix proportional to \(I_4+J_4\) is invertible
(\(1+4=5\ne0\) in \(\mathbf F_3\)).
Thus \(Q_A\) is nondegenerate, and the sum of the five vectors is
orthogonal to their span and hence zero. A change of basis puts \(B\)
in (1). By symmetry the same classification holds for \(A\). A literal
spectral partner for (1) consists of the six vectors, written in
base-three indexing \(x_1+3x_2+9x_3+27x_4\),
\[
                    0,\ 66,\ 73,\ 34,\ 17,\ 50 .
\]
The accompanying checker verifies all dot-product counts on both
sides. These sets cannot tile since 6 does not divide 81.

Every five points of (1) form an affine basis. This is immediate when
they include 0 by the independence of four nonzero points. When
they exclude 0, the only linear relation among them is proportional
to their sum being zero, and its coefficient sum is \(5\ne0\).
The affine dependence on all six uses equal coefficients, whose sum
is \(6=0\); hence every permutation of the six points extends to an
affine automorphism (map five basis points, then use the relation
for the sixth). An affine map fixing the six points is the identity.
The stabilizer has order \(6!\); the orbit size is therefore
\(81\cdot80\cdot78\cdot72\cdot54/720=2\,729\,376\).

If \(3^2\mid m\) and \(B\) spans the full space, the equal counts give
\(\sum_{a\in A}a=0\) by their linear moment along each \(b\).
Also \(c=0\), and polarization on \(b,b'\) shows that the bilinear
form of \(Q_A\) vanishes on a spanning set of pairs, hence identically.
For \(m=9\), if both members span, the row space of the four-by-nine
coordinate matrix of \(A\) is a four-dimensional totally isotropic
space for the standard dot product on \(\mathbf F_3^9\).
It is orthogonal to the constant vector, which is isotropic and
independent of it because \(A\) includes 0. Adjoining that vector
would give a totally isotropic space of dimension 5. This is
impossible: nondegeneracy gives \(\dim W^\perp=9-\dim W\), and
\(W\subset W^\perp\) for a totally isotropic \(W\).

Thus for \(m=9\) one member, say \(B\), lies in a proper linear
subspace \(U\) after translation. The image of \(A\) in \(U^*\)
is injective, since two points with the same image would give
identical rows in the spectral matrix. It is spectral there with
spectrum \(B\). If \(\dim U=2\), both sets in the reduced pair are
full; if \(\dim U=3\), the codimension-one size argument in §1
applies in both directions. In either case, \(A\) tiles upstairs
by taking the full preimage of a tiling complement in \(U^*\):
the injective projection supplies a single \(A\) representative
for each needed coset. \(B\) tiles upstairs by adjoining a
complementary subspace to any complement inside \(U\).
Dimensions below two are impossible for size 9.

## 3. Finite exclusion of size 18

Suppose \(m=18\). Both members span: otherwise the projection just
described makes a spectral pair of size 18 in dimension at most 3,
excluded by the bound in §1 (or cardinality). Thus the first and
second moments of \(A\) all vanish modulo 3.

Moreover, \(B\) has four points in an affine plane. To prove this,
sum the numbers of point pairs and point triples contained in all
affine planes. Each pair belongs to exactly 13 affine planes, since
after taking the quotient by its line direction there are 13
one-dimensional subspaces of a ternary three-space. Each triple
belongs to at least one. If every plane had at most three points
of \(B\), at most one third as many triples as pairs could occur
in each plane. But \(3\binom{18}{3}>13\binom{18}{2}\).
In a ternary affine plane, four points have a difference in every
direction by the three-coset pigeonhole principle. Thus \(Z(A)\)
contains all nonzero vectors in the direction plane of these
four points.

Send this frequency plane to the first two coordinate directions
and write points of \(A\) as \((a,b,x,y)\) in the dual coordinates.
The full Fourier transform of the fiber counts for \((a,b)\)
then vanishes off zero, so every one of the nine fibers contains
exactly two points. For each of the three anchor fibers
\((0,0),(1,0),(0,1)\), translate the midpoint of its vertical pair
to zero by adding a vertical-valued affine function of \((a,b)\).
Such a function can take arbitrary values on the three anchors and
gives an invertible affine transformation. Every anchor pair is
now \(\{u,-u\}\) for nonzero \(u\in\mathbf F_3^2\).
The spectral condition and the necessary moments are preserved by these
affine changes, or can be rederived from the transformed partner.
An invertible vertical change of coordinates permutes the four
vertical projective directions as the full \(S_4\): its projective
group has order \(48/2=24\) and acts faithfully on these directions.
Thus the three anchor directions reduce to the five labelled patterns
\[
               000,\quad001,\quad010,\quad011,\quad012
\]
in a fixed ordering of the four directions. No interchange of
non-anchor fibers is assumed in this normalization.

In the remaining six fibers there are \(\binom92=36\) choices of
the vertical pair per fiber. Exactly nine moment coordinates
still need to be tested, namely the sums over \(A\) of
\[
                   x,\ y,\ x^2,\ xy,\ y^2,\ ax,\ ay,\ bx,\ by .
\]
All other first and second moments vanish automatically because the
base fibers have uniform cardinality two. The sum of these nine
coordinates, including the anchors, must be zero in \(\mathbf F_3^9\).
The checker divides the six variable fibers into two triples,
enumerates all \(36^3\) assignments per triple, and matches their
nine-coordinate syndromes up to the required anchor offset.
Every candidate \(A\) passing these necessary moments is tested,
whether or not the conditions suffice for spectrality.

For each candidate \(A\), the checker computes its exact 40-bit
mask of projective zero directions. Now form the graph on \(G\)
joining two vertices when their difference lies in \(Z(A)\).
An 18-point spectrum is exactly an 18-clique in this graph.
By translation, any such clique can contain 0. If there are fewer
than nine zero directions, the degree is at most 16 and this clique
is impossible. Otherwise the checker tests each distinct mask in the
current anchor case, using the neighbors of 0 and searching for a
17-clique there. Mask reuse is exact because the spectrum graph
depends only on the mask.

The clique search branches on the presence or absence of vertices.
A greedy proper coloring of the remaining candidates bounds any
clique by its number of colors. The recursion orders the individual
candidates by their greedy color and visits them in reverse, so
the color of the current vertex bounds the clique size in the
remaining prefix. The presence branch restricts to its neighbors;
the absence branch removes it. This proves both pruning rules,
and no numerical relaxations or unverified solver output are used.

The [standalone Node.js checker](verify_factor_fuglede_f3_four_classification.js)
gives these exact counts, in order of the five anchor patterns:

| Anchors | Surviving moment candidates | Tested distinct zero masks | Maximum zero directions |
| --- | ---: | ---: | ---: |
| 000 | 123180 | 115983 | 36 |
| 001 | 113829 | 109203 | 33 |
| 010 | 113829 | 109203 | 33 |
| 011 | 113829 | 109203 | 33 |
| 012 | 105306 | 103612 | 33 |

None has a clique of size 18. Run the checker with no flags or with
`--alternate`; the alternate run uses different triple partitions
and reverses the vertex order in every clique bound. The entries use
only small integers and exact BigInt sets. No Lean proof or
classification in characteristic other than 3 is claimed.
