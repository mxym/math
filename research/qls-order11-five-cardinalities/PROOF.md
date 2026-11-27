# Construction and exact classification of its image

## 1. Square and ray count

All indices below are in \(\mathbb F_{11}=\mathbb Z/11\mathbb Z\),
identified with the integers from 0 through 10. Set
\[
 D=\{1,3,4,5,9\},\qquad d=\mathbf 1_D,\qquad
 \xi=\frac{-5+i\sqrt{11}}{6},\qquad H_{ka}=\xi^{d(k-a)} .
\]
Here \(D\) is the set of nonzero squares and \(|\xi|=1\).
Every two distinct translates of \(D\) intersect in two positions.
Indeed, put \(\chi(0)=0\) for the quadratic character \(\chi\).
For each nonzero \(u\), restricting to \(x\ne u\) allows the
bijection \(x\mapsto x/(x-u)\) onto \(\mathbb F_{11}\setminus\{1\}\).
Because the quadratic character of \((x-u)^2\) is one,
\(\sum_x\chi(x)\chi(x-u)=-1\). Expand
\(2d(x)=1+\chi(x)-\mathbf 1_{\{x=0\}}\) to obtain
\[
 4\sum_x d(x)d(x-u)
 =11-1-(1+\chi(-u))-(1+\chi(u))=8 .
\]
The final equality follows because \(-1\) is a nonsquare.
Therefore the signed difference of the exponents of two distinct
columns has three entries of each sign and five zeros. Their inner
product is \(5+3(\xi+\overline{\xi})=0\). The diagonal column norms
squared are 11, hence \(H^*H=11I\).

For a permutation \(\sigma\) of the 11 coordinates, let
\(K_{kb}=H_{\sigma(k),b}\) and form
\[
 v_{ab}(k)=11^{-1/2}H_{ka}K_{kb}
   =11^{-1/2}\xi^{E^\sigma_{ab}(k)},\qquad
 E^\sigma_{ab}(k)=d(k-a)+d(\sigma(k)-b).
\]
The columns of \(K/\sqrt{11}\) are orthonormal. For fixed \(a\),
multiplying by the unimodular column of \(H\) is a diagonal unitary;
hence the row of vectors \(v_{ab}\) is an orthonormal basis.
Likewise the column condition uses the columns of \(H/\sqrt{11}\).
Thus this array is a quantum Latin square for every \(\sigma\).

The number of distinct rays is exactly the number of distinct exponent
vectors \(E^\sigma_{ab}\). To see this, the phase \(\xi\) is not a
root of unity: otherwise the rational noninteger
\(\xi+\xi^{-1}=-5/3\) would be an algebraic integer. Equal rays require
all integer exponent differences to be the same constant, because
the phase ratio is independent of \(k\). Every exponent vector has
coordinate sum 10, so that constant is 0. Conversely, equal
exponent vectors give equal vectors. No numerical tolerance is used.

## 2. The five missing cardinalities

In the following table each \(\sigma\) is specified by the list of its
images of \(0,1,\ldots,10\), not by the list of its inverse images.
The last column gives each ray-class size followed by the number of
classes of that size. The square itself is the formula in Section 1.

| Cardinality | \(\sigma\) | Class size: count |
|---:|:---|:---|
| 66  | (0,1,2,3,4,5,6,7,8,9,10) | 1: 11; 2: 55 |
| 106 | (0,1,2,3,8,5,9,10,4,6,7) | 1: 95; 2: 10; 6: 1 |
| 113 | (0,1,2,3,5,9,7,6,10,4,8) | 1: 107; 2: 4; 3: 2 |
| 115 | (0,1,2,3,4,5,7,6,10,9,8) | 1: 109; 2: 6 |
| 119 | (0,1,2,3,4,5,8,9,10,7,6) | 1: 117; 2: 2 |

Here is a direct independent way to check the finite counts.
Encode a quadratic-field element \(a+b\sqrt{-11}\) as a pair of
integers, using a common positive denominator as needed. A coordinate of
\(6H\) or \(6K\) has pair \((6,0)\) or \((-5,1)\). Their product
is the corresponding pair for \(36\sqrt{11}\,v_{ab}(k)\).
The norm squared of each of these unnormalized coordinates is \(36^2\).
An exact program multiplies with
\((a,b)(c,e)=(ac-11be,ae+bc)\), conjugates via \((a,b)\mapsto(a,-b)\),
and checks all 22 row/column Gram matrices.
For each cell, multiply this unnormalized vector by the conjugate of
its first coordinate. The resulting vectors are equal exactly on equal
rays, as all original first-coordinate moduli are the same nonzero
number. Comparing all \(\binom{121}{2}=7260\) unordered pairs proves the
listed multiplicities and does not use the non-root-of-unity argument.
An additional 119 witness uses
\(\sigma=(1,10,9,8,4,2,3,0,5,7,6)\) and has repeated ray pairs
\(\{(2,1),(7,10)\}\) and \(\{(4,3),(6,4)\}\), with no other repetitions.
Exchanging the images of 0 and 1 in this last permutation instead gives 121.

## 3. Invariance under two design automorphisms

Let \(\mathcal B=\{D+a:a\in\mathbb F_{11}\}\). A design automorphism
\(g\) is a permutation of the coordinates which sends \(\mathcal B\) to
itself. Since the 11 blocks are distinct, it induces a permutation
\(\gamma_g\) on the column labels, defined by
\(g(D+a)=D+\gamma_g(a)\). In particular
\[
 d(g(k)-\gamma_g(a))=d(k-a).
\]
For design automorphisms \(g,h\), compute
\[
 E^{g\sigma h}_{ab}(k)
 =d(h(k)-\gamma_h(a))
   +d(\sigma(h(k))-\gamma_g^{-1}(b))
 =E^\sigma_{\gamma_h(a),\gamma_g^{-1}(b)}(h(k)).
\]
This only reindexes the cells and coordinates, so the cardinality and
multiplicity partition are invariant. Affine maps \(k\mapsto sk+t\)
with \(s\in D\) are design automorphisms because \(sD=D\). They give a
subgroup \(A\) of order 55 that suffices for an exhaustive computation.

## 4. First exhaustive computation

[The first verifier](classify.cpp) visits all permutations in
lexicographic order. The Lehmer rank of \(w\) is
\(\sum_{i=0}^{10}(10-i)!\#\{j>i:w_j<w_i\}\), an integer bijection
between permutations and 0 through \(11!-1\). It is independent of
the iteration counter in the code. When a permutation \(\sigma\) is
first unmarked, compute its ray count from the exponent vectors and
mark each distinct permutation \(g\sigma h\), \(g,h\in A\), by rank.
The code checks the current permutation's rank, that no newly computed
orbit element precedes its representative, that the number of marked
permutations is \(11!\), and that the seen table is full. These
double cosets partition the symmetric group, so no skipped permutation
can have a different cardinality from the counted representative.
For each cell, two disjoint 11-bit masks encode the coordinates
of exponent 1 and exponent 2; their union's complement encodes 0.
Sorting and counting different masks is exactly counting distinct
exponent vectors. The first method visits 13,228 double cosets
and specifies the lexicographically first permutation for each value.

## 5. Second exhaustive computation with the full design group

[The second verifier](classify_independent.cpp) computes the full
automorphism group \(G\) directly from the incidence matrix
\(B_{ka}=d(k-a)\), not from a group classification. For a partial
permutation carrying coordinates \(0,\ldots,m-1\) to
\(w_0,\ldots,w_{m-1}\), make the multiset of the 11 projected column
words on these \(m\) coordinates and the multiset of the 11 words on
their images in the same order. If the multisets differ, a column
permutation cannot match them, so no extension is a design
automorphism. If the multisets match at \(m=11\), they give a
matching of the entire columns and certify a design automorphism.
Extending each surviving prefix by every unused point therefore
computes exactly \(G\). The verifier finds 660 elements, 60 fixing 0.

Each permutation has exactly one translate of its values that fixes
0, and all 11 translations are in \(G\). Thus the full histogram can
be obtained by classifying the \(10!\) permutations fixing 0 and
multiplying their populations by 11. For a normalized representative
\(\sigma\), all normalized permutations in its double coset have form
\[
 k\longmapsto g_0(\sigma(h(k)))-g_0(\sigma(h(0)))\quad
    (h\in G,\ g_0\in G,\ g_0(0)=0).
\]
Indeed, any left-action element \(g\in G\) is a translation composed
with an element fixing 0, and that translation cancels upon
normalization. This lists all and only the normalized elements of
the double coset. The second verifier traverses inverse permutations
lexicographically, uses a different inverse-rank computation, and
uses base-3 encoding of the exponents rather than signed bit sets.
It visits 126 double cosets and the same population for every value.
The replay checks equality of the two complete histograms.

## 6. Results

| Cardinality | Affine double cosets | Full-design double cosets | Permutations |
|---:|---:|---:|---:|
| 66  | 2 | 1 | 660 |
| 105 | 12 | 1 | 36,300 |
| 106 | 4 | 1 | 7,260 |
| 113 | 24 | 1 | 72,600 |
| 115 | 72 | 1 | 217,800 |
| 116 | 108 | 2 | 326,700 |
| 117 | 144 | 3 | 435,600 |
| 118 | 468 | 6 | 1,415,700 |
| 119 | 576 | 5 | 1,742,400 |
| 120 | 3,780 | 32 | 11,434,500 |
| 121 | 8,038 | 73 | 24,227,280 |
| Total | 13,228 | 126 | 39,916,800 |

The quantum Latin square construction and the five witnesses are
independent of the orbit computations. The computed absences refer
only to this fixed \(H\) and \(K\) a row permutation of \(H\), not to
all mixed-Schur products or all quantum Latin squares at order 11.
