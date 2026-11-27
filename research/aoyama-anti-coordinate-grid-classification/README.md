# Deterministic anti-coordinate grids and the order-four census

## Scope and results

Aoyama, Hasegawa, Hayashi and Sagara, [*Mutually orthogonal anti-Latin
squares*, arXiv:2608.30082v1](https://arxiv.org/abs/2608.30082v1)
(30 August 2026), give an incidence characterization of saturation
(Theorem 5, PDF pp. 12–13), identify the geometric existence question
(§6, PDF p. 36), and explicitly leave the order-four global classification
out of their local analysis (Remark 3, PDF p. 34). These two pieces are
treated separately here:

1. For a **given** affine plane of order \(n\ge8\), its own parallel
   classes admit an anti-coordinate grid. This existence assertion is
   an immediate corollary of the authors' first-moment estimate
   (Theorem 4 and its lemmas, PDF pp. 6–8) and Theorem 5, not a new
   existence method. We give an exact, deterministic polynomial-time
   construction from the incidence data, replacing their random sampling.
   The remaining orders use elementary impossibility or known small
   planes and witnesses.
2. In \(AG(2,4)\) there are 66,960 direction-complete partitions, forming
   17 orbits under the full collineation group. Their compatible ordered
   row/column pairs form 6,662 orbits under that group and 3,371 orbits
   when transposition is also allowed. Two independent exact enumerators
   verify the counts; the first generates complete canonical representatives.

We do not claim a new value of the anti-Latin extremal number or a
classification of compatible pairs in arbitrary orders.

## 1. Incidence formulation

Let \(X\) be the \(n^2\) points of an affine plane of order \(n\), with
its \(n+1\) parallel classes. Each class partitions \(X\) into \(n\)
lines of size \(n\). A grid is a bijection \(\tau:[n]^2\to X\), where
\([n]=\{0,\ldots,n-1\}\). Its row-blocks and column-blocks are the images
of the usual rows and columns. Each forms a partition into \(n\)-sets,
and each row-block meets each column-block in exactly one point.
Conversely, two such compatible partitions become a grid after labeling
the blocks of each.

A block \(B\) is a *transversal* to a parallel class \(D\) if it
meets every line of \(D\) once, and is *direction-complete* if it is
not transversal to any class. A grid is *anti-coordinate* if all its
row- and column-blocks are direction-complete, exactly as in the
authors' Definition 4. If we label the lines of each class, putting the
label of the line through \(\tau(i,j)\) into cell \((i,j)\) yields
one anti-Latin array per direction. These \(n+1\) arrays are mutually
orthogonal, because lines from distinct directions meet at a single
point. No coordinates on \(X\) enter this definition.

## 2. Deterministic construction

Let \(E_{B,D}\) be the event, for a uniform random bijection, that the
image of the coordinate row/column \(B\) is a transversal to \(D\).
There are \(2n(n+1)\) events. A uniform \(n\)-subset is a transversal
with probability \(n^n/\binom{n^2}{n}\), because its points can be chosen
one per line and there are \(n\) choices on each line. This is the
authors' count, applied specifically to the partitions of the given
plane, not to a substituted plane of the same order.

For completeness, the initial expected number of bad events is
strictly less than \(1\) for \(n\ge8\). Indeed,
\[
 \frac{n^n}{\binom{n^2}{n}}
 =\frac{n!}{n^n}
   \Bigg/\prod_{i=0}^{n-1}\left(1-\frac{i}{n^2}\right)
 <\frac{2n!}{n^n},
\]
since \(\prod_i(1-x_i)\ge1-\sum_i x_i\) for \(x_i\in[0,1]\), and the
sum here is \((n-1)/(2n)<1/2\). The resulting upper bound
\(4n(n+1)n!/n^n\) is \(11{,}612{,}160/16{,}777{,}216<1\) at \(n=8\);
its consecutive-term ratio is
\((n+2)/n\cdot(n/(n+1))^n\le(n+2)/(2n)<1\) for \(n\ge8\).

### Exact conditional probabilities

Assign the \(n^2\) cells one at a time. Given any partial injection, let
\(s\) be the remaining number of unused points. For event \(E_{B,D}\),
let \(r\) denote the number of unassigned cells in \(B\).
If two assigned cells of \(B\) already meet the same line of \(D\), the
conditional probability is zero. Otherwise let \(M\) be the \(r\) lines
of \(D\) that contain no assigned point of \(B\), and for each
\(\ell\in M\) let \(a_\ell\) be its number of unused points in the
**entire** partial injection. The number of favorable ordered
injections into the remaining \(r\) cells is
\(r!\prod_{\ell\in M}a_\ell\); the number of unrestricted injections
into these cells is \(r!\binom{s}{r}\). Each injection to those cells
has exactly \((s-r)!\) extensions to all unassigned cells. The
conditional probability is therefore
\[
 \Pr(E_{B,D}\mid\text{partial injection})
   = \frac{\prod_{\ell\in M}a_\ell}{\binom{s}{r}}.
\]
The formula includes \(r=0\), where the empty product is 1 if no
repeat has occurred. It uses the remaining points after every assignment,
not just points unused by that row or column.

For the next cell, calculate the sum of these probabilities for every
possible remaining point. In a uniform completion each candidate is
equally likely, so the arithmetic mean of the candidate sums is the
previous sum. Choose a minimizing candidate (smallest point label
breaks ties). The sum never increases. At termination it is the
actual integer bad-event count, still less than 1, so is zero.
No independence assumption about the events is used.

A direct implementation has \(n^2\) assignment steps, at most \(n^2\)
candidates per step, \(2n(n+1)\) events and at most \(n\) line factors
per event. After computing or maintaining unused line counts it needs
\(O(n^7)\) arithmetic operations. Exact comparisons are polynomial-bit:
every binomial denominator is at most \((n^2)^n\), and a common multiple
can be taken as the product of the at most \(n+1\) possible denominators
\(\binom{s}{r}\) for a fixed step, of bit length \(O(n^2\log n)\).
The implementation uses a least common multiple and updates each
product after trying a point, and independently verifies the exact
averaging equality at every step. This is polynomial time in the
explicit incidence data.

### Small orders

For \(n=2,3\), a block's \(\binom n2\) point pairs cannot determine all
\(n+1\) directions; every pair belongs to only one direction. Thus
no plane of either order admits such a grid. There is no affine plane
of order 6: its projective completion would violate Bruck–Ryser,
since \(6\equiv2\bmod4\) is not a sum of two integer squares.
At \(n=4,5,7\), the projective completion is unique and Desarguesian
by the classical small-order classifications cited below. Its
collineation group is transitive on lines, so removal of the line at
infinity gives the unique affine plane of that order. The source
paper's Examples 1 and 6 already give witnesses for these orders;
our script also verifies three separate explicit grids. Hence, for
any existing affine plane of order at least two, the condition on
its order is exactly \(n\ge4\). Only the \(n\ge8\) **algorithm**, not
the existence of the small grids or classification of their planes,
is asserted as a new constructive part.

## 3. Full compatible-pair classification in \(AG(2,4)\)

### Coordinates, objects, and equivalence

Use \(F=\mathbf F_2[\omega]/(\omega^2+\omega+1)\), in the encoding
\(0,1,2=\omega,3=\omega+1\). Point \((x,y)\) has index \(4x+y\);
a block has integer mask \(\sum_{i\in B}2^i\). A partition is
an increasing tuple of its four masks. An ordered pair
\((R,C)\) is compatible if all sixteen intersections have size 1.
Blocks within a partition are not labeled.

The full plane collineation group is \(G=A\Gamma L(2,4)\) on these
points. To verify fullness without a group library, its semiaffine
maps preserve lines. Conversely, any collineation can be normalized
by a translation and an invertible \(F\)-linear map to fix
\(0,(1,0),(0,1)\): their images are noncollinear. Such a map fixes
both coordinate-axis directions and therefore has form
\((x,y)\mapsto(f(x),g(y))\), where \(f,g\) are permutations fixing
0 and 1. Since it fixes \((1,1)\), it preserves the diagonal through
the origin, so \(f=g\). There are two such permutations of \(F\):
the identity and Frobenius \(x\mapsto x^2\). Therefore
\[
 |G|=16\cdot(16-1)(16-4)\cdot2=5{,}760 .
\]
The involution \(s(R,C)=(C,R)\) commutes with the diagonal \(G\)-action.

This matches the array-side convention of the source paper: common
row and column permutations plus arbitrary permutation of the five
arrays and independent symbol relabelings in each array give
**strong** isomorphism without transposition. Once grid labels are
forgotten, these induce precisely the diagonal collineation action.
In detail, equivalence maps the full line system to itself through
the two grid identifications, and conversely any plane collineation
maps the two partitions to the target two, giving row/column
bijections and permuting the line partitions and their line labels.
Adding simultaneous transposition corresponds to also using \(s\).

### Exact enumeration

There are 720 good blocks. An elementary count uses their unique
doubled direction: each good size-four block has six pairs for five
directions, with one direction appearing twice on disjoint pairs
(three collinear points would contribute three times).
Choose the doubled direction (5 ways), the two parallel lines
(6 ways), and the pair on the first line (6 ways). Of the six pairs
on the other line, four have a different nonzero displacement
along that direction. Such choices, and only those, make all four
cross-pair directions distinct: in coordinates with the parallel
lines \(y=0,1\), the four horizontal differences between endpoints
are a translate of \(\{0,a,b,a+b\}\), where the two displacements
\(a,b\) differ. Thus there are \(5\cdot6\cdot6\cdot4=720\) blocks.

The first enumerator lists all good four-sets by their six pair slopes,
then exact-covers the plane by good blocks. At each step it chooses the
block containing the least uncovered point; every full partition
has exactly one branch at that step, so all are listed once.
This gives 66,960 partitions. For each of the 17 \(G\)-orbit
representatives \(R\), it lists compatible \(C\)'s by applying the
same partition search to good blocks meeting each of the four
blocks of \(R\) once. Taking orbits of these \(C\)'s under \(G_R\)
now classifies ordered pairs: after moving the first partition to
\(R\), the remaining freedom is exactly its stabilizer \(G_R\).
The raw number of compatible ordered pairs is
\(\sum_R |G:G_R|\cdot\#\{C:R\perp C\}=37{,}909{,}440\).
The number of \(G\)-orbits is 6,662. Transposing swaps the two
partitions; compute their new canonical representative by the
same group procedure. There are 80 fixed **orbits**, not pairs
with \(R=C\), so the number of unoriented orbits is
\((6{,}662+80)/2=3{,}371\).

For fixed external row and column labels (the source paper's
*weak* isomorphism, without transposition), there are
\(37{,}909{,}440\cdot(4!)^2\) grid bijections. The target
collineation action is free on these bijections, since fixing a
bijection fixes all points. Equivalently, two bijections yield the
same plane line system on the fixed cell set precisely when their
target relabeling is a collineation. Thus the weak count is
\(37{,}909{,}440(4!)^2/5{,}760=3{,}790{,}944\).

### Independent Burnside count

The second enumerator generates line incidence as cosets of the five
one-dimensional \(F\)-subspaces; it tests each four-set by
line intersections instead of slope counts. It lists each partition
by choosing the block through point 0, then an increasing triple
of other masks, checking the final mask as the complement. The
ordered compatibility count is computed directly over **all**
row partitions rather than through row orbit representatives.

For \(g\in G\), let \(F_g\) be its set of fixed partitions, let
\(a_g=\#\{(R,C)\in F_g^2:R\perp C\}\), and let
\(b_g=\#\{R:g^2R=R,\ R\perp gR\}\). Then \(a_g\) is the fixed-point
count of \((g,1)\) on compatible pairs; \(b_g\) is for \((g,s)\),
since fixedness there says \(C=gR,\ R=gC\). The code groups the
5,760 permutations into their 17 conjugacy classes and computes
the three weighted sums for partitions and the two kinds of pair
action. It obtains
\[
 \sum_g |F_g|=97{,}920,\quad
 \sum_g a_g=38{,}373{,}120,\quad
 \sum_g b_g=460{,}800.
\]
Each sum is constant on a conjugacy class before weighting, since
conjugation transports fixed objects bijectively.
Dividing by 5,760 gives 17 and 6,662 for partitions and ordered pairs;
dividing the sum of the last two by \(2\cdot5{,}760\) gives 3,371.
It also independently recovers the number of fixed ordered orbits
under transposition as \(2\cdot3371-6662=80\).

### Profiles and the source's example

The profile is the multiset of multiplicities of the four doubled
directions of the blocks of a partition, as in Definition 11 of the
source. The counts of **unoriented** classes by unordered profile pair are:

| row/column profiles | classes |
|:--|--:|
| \(4\) / \(4\) | 73 |
| \(4\) / \(2+2\) | 148 |
| \(4\) / \(2+1+1\) | 402 |
| \(4\) / \(1+1+1+1\) | 45 |
| \(2+2\) / \(2+2\) | 129 |
| \(2+2\) / \(2+1+1\) | 827 |
| \(2+2\) / \(1+1+1+1\) | 102 |
| \(2+1+1\) / \(2+1+1\) | 1,306 |
| \(2+1+1\) / \(1+1+1+1\) | 316 |
| \(1+1+1+1\) / \(1+1+1+1\) | 23 |

Thus all ten pairs of the four known individually allowed profiles
are attained. For a single partition the 17 orbits split as
\(4,4,8,1\) in the order of the four profiles above.

For Example 1 of the source, take the first two arrays as candidate
point-coordinate labels and try independent alphabet permutations
on these two coordinates. The verifier checks which labelings
send the complete line system from all five arrays to that of
\(AG(2,4)\); 288 labelings do. The ordered canonical representative
displayed by the enumeration is
\[
 ((53,202,13568,51712),\ (833,3216,20514,40972)).
\]
Its profile pair is \((4),(2,1,1)\); the transpose lies in a different
ordered orbit. The given representative is the lesser one in the
unoriented convention implemented here (lexicographic order of
pairs of increasing mask tuples). The checker prints both.

## 4. Sources and reproducibility

* Aoyama, Hasegawa, Hayashi and Sagara,
  [arXiv:2608.30082v1](https://arxiv.org/pdf/2608.30082v1):
  Definition 4, Theorems 4–5, §5.3.7 Remark 3, §6 last paragraph,
  and Appendix A Example 6. The exact numerical extremal problem
  and order-four single-block orbit are already in that paper.
* O. Veblen and J. H. Maclagan-Wedderburn,
  [*Non-Desarguesian and Non-Pascalian Geometries*](https://doi.org/10.1090/S0002-9947-1907-1500792-1),
  Trans. AMS **8** (1907), 379–388, especially pp. 387–388, for
  the uniqueness of the projective plane of order 4.
* C. R. MacInnes,
  [*Finite Planes with Less than Eight Points on a Line*](https://doi.org/10.2307/2971152),
  Amer. Math. Monthly **14** (1907), 171–174, for order 5.
* M. Hall Jr.,
  [*Uniqueness of the projective plane with 57 points*](https://doi.org/10.1090/S0002-9939-1953-0058986-4),
  Proc. AMS **4** (1953), 912–916, for order 7.
* R. H. Bruck and H. J. Ryser,
  [*The Nonexistence of Certain Finite Projective Planes*](https://doi.org/10.4153/CJM-1949-009-2),
  Canad. J. Math. **1** (1949), 88–93, for the obstruction at order 6.

A 27 November 2026 check of the source and searches for *anti-coordinate
grid*, *direction-complete partitions*, *AG(2,4) anti-Latin orbits*,
and the paper's title paired with *deterministic* and *conditional
expectation* did not find the exact construction or complete census
reported here. This is a bounded literature check. It cannot guarantee
priority; in particular the large-order existence proof is implicit
in the cited source, as explained above.

Run from this directory (Python 3.10+ and a C++20 compiler, no external
data or dependencies):

    python3 deterministic_grid.py
    python3 verify_order4_orbits.py
    g++ -std=c++20 -O3 verify_order4_burnside.cpp -o /tmp/check_anti_grids
    /tmp/check_anti_grids

The first script takes an optional input JSON matrix of line labels:
entry D[d][p] is the integer label of the line through point p in
direction d; there are n+1 rows of length n*n, each containing
labels 0..n-1 n times. For n >= 8, it returns a row-major list of
the points selected for the grid. Demo inputs include field planes
and a derived order-nine spread incidence, to exercise the
coordinate-free interface.

    python3 deterministic_grid.py --input plane.json
    python3 verify_order4_orbits.py --dump /tmp/order4_representatives.json

The one-line unoriented representative JSON (including final LF) has
SHA-256 3259c625d6551ad9b3c74811fc6e358579ea2475b392add25e5b1271a0305b8b.
The finite checks use no downloaded catalogues and include bad
blocks or invalid incidence as negative controls.
