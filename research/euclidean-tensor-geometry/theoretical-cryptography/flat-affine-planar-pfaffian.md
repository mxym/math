# Flat affine planar signatures: a local Pfaffian rigidity criterion

**Scope.** This note concerns a supplied Boolean tensor in a specified cyclic
port order. The tensor is zero off an affine support, and its nonzero values
have the same modulus. The question is whether it is a planar matchgate
signature in this order, with no change of basis. The answer is an exact
partition-and-tree criterion. For a compact phase description, recognition is
deterministic polynomial time in the input bit size, even when the phase
modulus is given in binary. For fixed phase modulus this supplies a sufficient
condition for exact polynomial-time contraction of planar tensor networks.
There are no cryptographic samples, hidden parameters, hardness implications,
or claims concerning any concrete scheme.

## 1. Statements

Use \(x\in\mathbb F_2^k\) both as a bit string and as a set of ports, and choose
a starting point for the specified cyclic order. Suppose the nonzero support
of \(f\) is \(b+C\), where \(C\) is a linear code. Put
\(g(x)=f(b+x)/f(b)\), so \(g(0)=1\). Form the skew matrix \(A\) using
\(A_{ij}=g(e_i+e_j)\) for \(i<j\). Let the **pair classes** be the equivalence
classes of \(i\sim j\) if \(i=j\) or \(e_i+e_j\in C\); include singleton
classes.

In each pair class \(B\), choose the first port \(p\) as pivot. Put
\(d_p=1,\ d_i=A_{pi}\) for \(i\in B\setminus\{p\}\), and
\(B_{ij}=A_{ij}/(d_i d_j)\) on this class. Thus \(B_{pi}=1\) for \(i\ne p\).
Here the symbol \(B_{ij}\) denotes an entry of the gauged skew matrix rather
than the pair class itself. An **ordered tree of labels** is a binary tree
whose leaves have a left-to-right order, and each internal node \(v\) has a
unit complex label \(z_v\). For distinct leaves \(i,j\), the entry directed
from the earlier to the later leaf is \(z_{\mathrm{lca}(i,j)}\), and the
reverse entry is its negative.

**Theorem 1.** The following conditions are necessary and sufficient for
\(f\) to be a matchgate signature in the given port order.

1. \(C=\bigoplus_B \{x_B:\sum_{i\in B}x_i=0\bmod 2\}\).
2. In each class, the gauged skew matrix on the nonpivot ports is represented
   by an ordered tree of unit labels. Equivalently every three- and four-port
   subset of these nonpivot ports has a nontrivial module: a proper subset of
   size at least two whose members have identical entries toward each outside
   port. Empty or one-port trees have no constraints. Attach the pivot as
   a new left leaf with root label \(1\) when that class has at least two ports.
3. Fix any arrangement of the classes, concatenate their tree leaf orders,
   and let \(\pi\) assign each original port its position in that list.
   For all \(x\in C\),
   \[
   g(x)=(-1)^{\sum_{i<j,\,\pi(i)>\pi(j)}x_i x_j}
      \prod_i d_i^{x_i}
      \prod_v z_v^{L_v(x)R_v(x)} .\tag{1}
   \]
   In the last product \(v\) ranges over the internal nodes of all class
   trees (including a new pivot root if present), and \(L_v,R_v\) are the
   two child parities, valued in \(\{0,1\}\).

If condition 1 holds, condition 2 is also equivalent to the unit-modulus
tests on all four-port principal Pfaffians within the classes. Condition 3
still compares the given function to the resulting Pfaffians; magnitude tests
on the skew matrix alone are not a substitute for that comparison.

**Theorem 2 (succinct exact recognition).** Suppose \(b+C\) comes from binary
affine constraints, and the entries on it are
\(\gamma\exp(2\pi i q(x)/M)\), with \(M\ge2\) in binary and \(\gamma\ne0\).
The phase \(q\) is specified as a sum modulo \(M\) of a constant and weighted
products of at most two affine bit parities; this includes ordinary quadratic
bit phases. All weights are integers in binary. Then exact recognition,
including all of (1), is deterministic polynomial time in the description
size. For odd \(M\), embed the phases in order \(2M\).

For a supplied closed plane network of such signatures in their embedded port
orders, all passing recognition, with a **fixed** \(M\) and
\(\gamma\in\mathbb Q(\exp(2\pi i/M))\) given in fixed-basis rational
coordinates, exact contraction is deterministic polynomial time in the input
bit size. Arbitrary positive rational diagonal weights on the wires are
allowed; neither bounded arity nor bounded width is assumed. For variable
\(M\) the recognition statement does not require materializing the
cyclotomic field, and no general polynomial-time bit bound for numeric
contraction in that variable-degree field is asserted.

## 2. Support and the skew-matrix chart

By the planar Pfaffian chart (Cai–Gorenstein, Sections 3 and 5; Meng–Pan,
Lemmas 20–21), complementing ports by a fixed bit string and rescaling by
a nonzero constant preserve matchgate realizability. In the chart with
\(g(0)=1\), the even entries must be \(g(x)=\operatorname{Pf}(A_x)\), where
\(A_x\) is the principal submatrix indexed by the one-bits in the original
order; the odd entries are zero. Conversely these principal Pfaffians are
a matchgate signature. The empty Pfaffian is 1.

The relation defining pair classes is transitive because
\((e_i+e_j)+(e_j+e_\ell)=e_i+e_\ell\) in the code. In each class the weight-two
vectors span its even code and there are no skew entries between classes.
Therefore the right hand side of condition 1 is contained in \(C\). For any
\(x\in C\), if some class meets \(x\) oddly, no pairing on \(x\) uses only
nonzero skew entries, so the Pfaffian is zero, a contradiction. Thus equality
is necessary. Conversely our tree criterion below gives a nonzero Pfaffian
whenever all class intersections are even; singleton classes simply pin
their normalized port to zero.

## 3. Unit Pfaffians force a labeled tree

In one class strip the unit diagonal as in the statement. Gauging does not
change the modulus of any principal Pfaffian. A three-subset of nonpivot
ports \(i,j,\ell\) together with the pivot has Pfaffian, up to the order sign,
\(u+v+w\), where \(u=B_{ij},v=B_{j\ell},w=B_{\ell i}\). For any three complex
units,
\[
 |u+v+w|^2-1=\frac{(u+v)(v+w)(w+u)}{uvw}.
\]
Thus this modulus is one iff two of \(u,v,w\) are opposite, exactly the
nontrivial-module condition on the three-subset.

Now consider a four-subset of nonpivot ports. Suppose each of its triples
has a module. By relabeling the first triple, write, in order \(0,1,2,3\),
the six upper entries as
\[
  A_{01}=A_{02}=a,\quad A_{03}=b,\quad A_{12}=c,\quad
  A_{13}=d,\quad A_{23}=e.
\]
These denote entries after gauging and after this temporary relabeling.
If \(a=b\), \(\{1,2,3\}\) is a module. If \(d=e\), \(\{1,2\}\) is a module.
Otherwise the two triples involving \(\{0,3\}\) force \(d,e\) to be the two
distinct values \(-a,b\). By swapping 1 and 2 if needed take \(d=-a,e=b\).
The last triple forces \(c=d\) or \(e=-c\). In the first case \(\{0,2\}\)
is a module. In the second case \(c=-b\), and the four-port Pfaffian is
\[
  ab+a^2-b^2,\qquad
  \left|\frac{ab+a^2-b^2}{ab}\right|
   =\left|1+a/b-b/a\right|>1.
\]
Indeed \(a/b\) is a unit other than \(1,-1\), and \(a/b-b/a\) is then
pure imaginary and nonzero. Thus unit Pfaffians exclude prime
four-subsets as well.

Treat the entries as arc labels of a finite reversible 2-structure:
reversal negates the label. The small-obstruction theorem for uniformly
nonprimitive 2-structures (Engelfriet–Harju–Proskurowski–Rozenberg,
Theorems 3.6 and 3.25; also Hellmuth–Stadler–Wieseke, Theorem 2.2) now gives
the tree decomposition with no prime node. Each quotient is linear or
complete; a complete quotient with a symmetric label is impossible at any
internal node since no unit is its own negative. Equivalently one may invoke
the binary composition form of their theorem, in which the two labels at
each split must be negatives. A linear quotient with several children can
be refined into binary nodes with the same label. This proves the necessity
of condition 2, and explains exactly which decomposition fact is prior.

For sufficiency, put one class in its tree leaf order and select an even
number of leaves. Collapse the tree from the bottom. A child with even
selected count sends no leaf onward and an odd child sends one; if both
children send a leaf, pair them and multiply by \(z_v\). To check the
Pfaffian step, the two remaining leaves of that node are consecutive among
the currently selected leaves, and have identical entries to every other
remaining leaf, because all such leaves are outside the node. Subtract the
first row from the second and the first column from the second, a congruence
of determinant one. The second is now incident only to the first, and the
Pfaffian expands with positive sign for an adjacent pair. This establishes
the product over nodes with both child counts odd. It works in every
induced subset, including any placement of the original pivot. Conversely,
all size-four tests hold for any tree, so the claimed local equivalence
follows as well.

The skew entries on a class with one port are empty. After concatenating the
class leaf orders, even selections on the distinct classes factor. Undoing
the diagonal contributions and the reordering introduces precisely the two
remaining factors in (1). Changing the concatenation order of whole classes
changes no sign on the even-per-class support. This proves Theorem 1.

## 4. Deterministic bit-size recognition and contraction

Solve the affine constraints by binary elimination and select any \(b\).
An inconsistent system gives the zero tensor, which can be separated before
recognizing nonzero tensors. Evaluate the pair tests to get the classes.
The even-per-class subspace is already contained in \(C\); compare ranks
for equality. Compute the leading pair phase exponents after subtracting
\(q(b)\) and after the pivot gauge; multiplication, division and negation of
unit labels then use addition, subtraction and the half-modulus in an even
phase modulus. Check each three- and four-subset for a proper nonsingleton
module using label equality. A tree can be computed by known 2-structure
algorithms. For a self-contained polynomial extraction from the existence
theorem, grow the least module containing a pair by inserting any outside
port that distinguishes current members. On a set of size at least three,
try all pairs until the closure is proper; such a pair exists in a tree
representable set. Recurse on the module and on its quotient (retaining one
representative). Both smaller problems inherit tree representability; replace
that representative leaf by the module tree. For child sizes \(k_1,k_2\)
one has \((k_1-1)+(k_2-1)=k-1\), bounding the total recursion size.
For sets with at most two ports the tree is immediate. This extraction does
not enumerate the support.

On \(x\in C\), the exponent of the right side of (1) is also a sum of
weighted products of at most two bit parities: the permutation sign uses
coefficient \(M/2\) after using an even phase modulus. Substitute a binary
basis \(x=Ty\) for \(C\) and subtract the two exponents. It suffices to test
whether an explicitly supplied such sum \(Q(y)\) vanishes modulo \(M\) for
every \(y\in\mathbb F_2^r\). The test below works without a bound on \(M\)
or on its 2-adic valuation.

For an affine bit parity \(P\), write \(P=(1-\chi_P)/2\), with
\(\chi_P=(-1)^P\). Expanding \(4Q(y)\) gives a sparse integer sum
\(\sum_{j=1}^s a_j (-1)^{u_j\cdot y}\); signs from affine constants go in
\(a_j\). The desired identity is equivalent to the latter sum being zero
modulo \(m=4M\) on every Boolean string, not modulo \(M\). Put
\(g_h=\big((-1)^{u_j[h]}\big)_{j=1}^s\). The evaluation vector at \(y\) is
the coordinatewise product of the \(g_h\) for which \(y_h=1\). Start with
the integer lattice generated by \(m\mathbb Z^s\) and the all-ones vector.
Add the coordinatewise products of its current basis vectors with each
\(g_h\), and compute the updated Hermite normal form; repeat until stable.
The stabilized lattice modulo \(m\) is exactly the module generated by all
evaluation vectors: every addition stays inside that module, and stability
includes the whole orbit of the initial vector. Each strict enlargement
decreases the integer index by at least a factor of two; there are at most
\(s\log_2 m\) rounds with a change. The reduction can use bases in canonical
Hermite form, of polynomial entry bit size since the lattice always contains
\(m\mathbb Z^s\). Standard polynomial-bit Hermite normal form therefore
makes this a polynomial-time algorithm. Finally check that dot product
with \((a_j)_j\) vanishes modulo \(m\) on a lattice basis. This is a test for
the whole function, not a promise on small-weight inputs.

For contraction, the standard planarization of the skew chart replaces
\(O(k^4)\) crossings by constant-size sign gadgets and realizes the entries
by edge weights. Complementing ports and rescaling can be implemented by
constant-size additions per affected port and vertex. On a wire, add the
matching edge between the two local external ports. If it is used then
both local bits select deletion of the external vertex from the internal
matching, otherwise neither does. A diagonal weight \((w_0,w_1)\) on a
wire is handled by an overall \(w_0\) and joining-edge weight \(w_1/w_0\).
Hence a single plane weighted perfect matching sum equals the contraction
up to the tracked nonzero constants. The Kasteleyn–Temperley–Fisher
Pfaffian algorithm applies, independent of whether the weights are
nonnegative or real. At fixed phase order the field operations have a
fixed rational basis and polynomial bit cost: clear common denominators
with polynomial bit overhead, and use polynomial-size minor bounds and
exact elimination (or fraction-free Pfaffian) to control intermediate
ratios. This is a sufficient recognition-and-contraction method, not a
complexity classification for all compact affine networks.

## 5. Real slice, rarity, and an example outside it

For real signed normalized entries, the gauged entries are \(\pm1\). The
triple test says that the associated nonpivot tournament has no directed
triangle, hence is transitive. Equivalently (1) is the sign of a permutation
on the selected ports times a product of leg signs. This slice uses the
classical switching-to-transitive phenomenon for local-order tournaments,
not a new tournament characterization. If all normalized signs are +1,
each class in its original order has Pfaffian 1 on every even subset by the
alternating expansion. Classes may be combined with no sign iff they
are a noncrossing partition of the original cyclic positions. For necessity
an alternating four-tuple from two classes gives Pfaffian \(-1\). For
sufficiency any crossing between two class-internal pairs would be such
a four-tuple; putting together adjacent selected pairs within each class
gives a noncrossing global pairing, so its permutation sign (and hence the
fixed grouping sign) is positive.

For example, a single class \(0,1,2,3\) in that order with upper entries all
1 except \(A_{12}=i\) gives a genuinely complex local signature. It is equal
on the even code to \(\exp(2\pi i x_1x_2/4)\): its six pair entries and
four-port Pfaffian match this phase (the latter is \(i\)). It is not a
stabilizer phase on the code, since in any binary code coordinates such
a phase has all second finite differences at zero even modulo 4, while
directions \(e_0+e_1,e_0+e_2\) here give second difference 1. No general
affine or quadratic tensor is presumed to pass.

Two elementary counts clarify how restrictive the condition is.

* For a uniform \(r\)-dimensional subspace of the even-sum hyperplane in
  \(\mathbb F_2^k\), the probability that it can support some normalized
  flat matchgate in this order is
  \(\left\{\begin{smallmatrix}k\\k-r\end{smallmatrix}\right\}
/\left[\begin{smallmatrix}k-1\\r\end{smallmatrix}\right]_2\).
  The numerator counts set partitions (the distinct pair classes), and the
  denominator is a Gaussian binomial. A signed matchgate exists for every
  such partition, even when it is crossing.
* For a fixed admissible support, there are exactly
  \(\prod_B 2^{|B|-1}(|B|-1)!\) real signed normalized matchgates.
  The pivot entries and the gauged transitive order on the other ports
  independently determine the skew matrix, which uniquely determines the
  signature. A uniform normalized real quadratic sign in \(r\) code
  coordinates has \(2^{r+\binom r2}\) equally likely possibilities. Summing
  the previous count over all partitions, the joint success probability
  (uniform even subspace and uniform quadratic sign on it) is therefore
  \[
  \frac{\left[\begin{smallmatrix} k\\k-r\end{smallmatrix}\right]_{\mathrm{Stirling}}}
       {2^{\binom r2}\left[\begin{smallmatrix}k-1\\r\end{smallmatrix}\right]_2},
  \]
  where the numerator is the unsigned Stirling number of the first kind
  (partitions with a cyclic order in each block). More generally, for a
  single class of size \(s\ge2\) and independent uniform entries in
  \(\mu_M\) above the diagonal, \(M\) even, normalized pivot gauging leaves
  the \(N=s-1\) nonpivot entries independent and uniform. For \(N\ge1\),
  the chance of passing the flatness criterion on this skew chart is at most
  \(\min\{1,N!\mathrm{Cat}_{N-1}M^{N-1-\binom N2}\}\), by counting
  ordered binary trees with leaf labels and node labels. This last ensemble
  assigns pair phases, not the exponentially many full tensor entries.

## Primary references and relation to this note

* [Cai and Gorenstein, *Matchgates Revisited*, Theory of Computing 10 (2014)](https://theoryofcomputing.org/articles/v010a007/v010a007.pdf),
  Sections 3 and 5: Pfaffian reconstruction and planar sign crossing gadget.
  Planar perfect matching contraction itself is classical.
* [Meng and Pan, *Matchgate Signatures Under Variable Permutations*, ISAAC 2025](https://drops.dagstuhl.de/storage/00lipics/lipics-vol359-isaac2025/html/LIPIcs.ISAAC.2025.50/LIPIcs.ISAAC.2025.50.html),
  Lemmas 20–21 and Theorem 25. Their global permutability condition concerns
  signatures that remain matchgates under every port permutation; this note
  fixes the embedded port order, including signed crossing classes.
* [Engelfriet, Harju, Proskurowski and Rozenberg, *Characterization and
  complexity of uniformly nonprimitive labeled 2-structures*](https://www.sciencedirect.com/science/article/pii/030439759400272X),
  Theoretical Computer Science 154 (1996), 247–282, Theorems 3.6 and 3.25.
  [Hellmuth, Stadler and Wieseke, arXiv:1603.02467](https://arxiv.org/pdf/1603.02467),
  Theorem 2.2 and Definition 6, give the ordered-tree form and the
  small-obstruction theorem explicitly. The complex unit-Pfaffian-to-module
  implication in Section 3 is the bridge used here.
* [Boussaïri, Ezzahir, Lakhlifi and Mahzoum, *Skew-adjacency matrices of tournaments with bounded principal minors*](https://www.sciencedirect.com/science/article/abs/pii/S0012365X23002388)
  discusses switching-equivalent local-order tournaments. [Lami,
  arXiv:2611.05479v1, Proposition 3 and its proof](https://arxiv.org/html/2611.05479v1)
  already gets the parity blocks and the same Stirling factor for the
  Clifford Gaussian perfect-matching ensemble. The real count above is
  included as a comparison, not a new Stirling formula for that ensemble.
  The unit-phase tree criterion does not assume stabilizer phases.
* [Amy and Mosca, *T-count optimization and Reed–Muller codes*](https://www.cs.sfu.ca/~meamy/Papers/reedmuller.pdf)
  already connects parity-phase identities at fixed powers of two to
  Reed–Muller codes. The lattice closure above is a direct sparse identity
  test with arbitrary binary modulus, not a minimum phase-count synthesis
  algorithm. For the integer normal form primitive see [Kannan and Bachem,
  SIAM Journal on Computing (1979)](https://epubs.siam.org/doi/10.1137/0208040).

The companion finite checks independently compare recursive Pfaffians and
tree products on generated exact examples. They do not replace the
2-structure theorem or prove a general absence of equivalent earlier
formulations.
