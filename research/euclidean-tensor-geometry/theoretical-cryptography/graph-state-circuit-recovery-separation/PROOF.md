# Proof

## 1. Exact model

We use the binary graph-state setting of Ganguly, arXiv:2611.27300v2,
§IV and §VI, problem 2. A simple graph has a symmetric zero-diagonal
adjacency matrix \(A\) over \(\mathbb F_2\). The associated labelled
Lagrangian matroid \(L\) is represented by the \(2n\) columns of
\([I\mid A]\), labelled \(j,j^*\) for the two columns at \(j\).
An admissible set contains at most one of each pair, and a circuit
is a minimal dependent admissible column set. Fix a dealer \(d\) and
write \(P=V\setminus\{d\}\). For every circuit meeting the dealer's
pair take its players, dropping the dealer and forgetting the stars.
The upward closure of these sets in \(P\) is
\(\Gamma^{\rm circ}_{L,d}\) (Ganguly, Definition 3). It is a
**quantum access structure** in the sense of Definition 2 exactly
when it is nonempty and any two members intersect. We do not require
the circuit access structure to be the family realized by a specified
encoding merely because it satisfies that abstract axiom.

For \(x\in\mathbb F_2^V\) put \(w(x)=(x,Ax)\) and define its pair
support \(S(x)=\{j:(x_j,(Ax)_j)\ne(0,0)\}\). Call \(w(x)\) admissible
when no pair equals \((1,1)\). Define the subspace
\[
 D_d(U)=\{(x_d,(Ax)_d): S(x)\subseteq U\cup\{d\}\}
     \subseteq\mathbb F_2^2,\qquad U\subseteq P .
\]
For each dealer with a neighbour, the dealer projection is onto:
choosing \(x=e_d\) and \(x=e_v\) for a neighbour gives the two
coordinates separately. Ganguly, Theorem 9 and Corollary 5, give the
operational characterization for the dealer-shortened graph-state
encoding: \(U\in\Gamma^{\rm rec}_d\) iff \(\dim D_d(U)=2\),
and \(U\) is intermediate iff \(\dim D_d(U)=1\). This is a criterion
for that particular encoding, not a statement about another possible
realization of the same abstract access structure.

We will use the following exact form of Proposition 5:
\[
 U\in\Gamma^{\rm circ}_{L,d}
 \quad\Longleftrightarrow\quad
 \text{there is admissible }w(x)\text{ with }d\in S(x)
             \subseteq U\cup\{d\}. \tag{1}
\]
Indeed, coefficients \((Ax,x)\) form a column relation of \([I\mid A]\).
Every relation has this form, since \(u+Av=0\) gives \(u=Av\).
A circuit meeting \(d\) gives such an admissible relation with
nonzero dealer part. Conversely, in an admissible relation with a
nonzero dealer coefficient, choose the unique dealer column in its
support. It lies in the span of the other support columns.
Choose a minimal subset that spans this column; the subset is
independent, and adjoining the dealer column gives a circuit.
This gives (1), including the equality of the minimal **player**
supports obtained by using all admissible relations instead of just
circuits. Taking the minimal sets of (1) is enough to verify
pairwise intersection because every member contains one of them.

## 2. Base graph and its admissible supports

Let \(H\) be the bipartite graph on \(\{0,1,2,3,4,5\}\) with edges
\(03,04,05,13,15,24,25\). Write \(s\) for the indicator vector
of \(S=\{1,2,3,4\}\), and \(B\) for the adjacency matrix of \(H\).
Let \(G_1\) add a vertex \(6\) adjacent exactly to \(S\).
Its adjacency matrix in order \(0,\ldots,6\) is
\[
 A_1=\begin{pmatrix}
 0&0&0&1&1&1&0\\
 0&0&0&1&0&1&1\\
 0&0&0&0&1&1&1\\
 1&1&0&0&0&0&1\\
 1&0&1&0&0&0&1\\
 1&1&1&0&0&0&0\\
 0&1&1&1&1&0&0
 \end{pmatrix}.
\]
Use a string such as 013 to denote the corresponding vertex set.
Here are **all** nonzero admissible relations, grouped by their
pair support. In the right column \(X/Y\) means
\(\operatorname{supp}(x)=X,\ \operatorname{supp}(A_1x)=Y\).
The singleton set \(0\) is different from \(\varnothing\).

| Pair support | \(X/Y\) |
| --- | --- |
| 0125 | 012/5, 5/012 |
| 0136 | 3/016 |
| 0146 | 01/46 |
| 0236 | 02/36 |
| 0246 | 4/026 |
| 0345 | 0/345, 345/0 |
| 1234 | 12/34, 34/12 |
| 1356 | 1/356 |
| 1456 | 45/16 |
| 2356 | 35/26 |
| 2456 | 2/456 |
| 01256 | 06/125, 1256/0 |
| 03456 | 0346/5, 56/034 |
| 12346 | \(6/1234,\ 12346/\varnothing\) |
| 012345 | 23/0145, 14/0235, 0135/24, 0245/13 |
| 0123456 | 136/0245, 246/0135, 02356/14, 01456/23 |

For an explicit way to verify completeness of the table, let
\(a\) be the bit mask of \(X\) (bit \(j\) for vertex \(j\)) and
\(b(a)\) the mask of \(Y\). The seven rows in mask notation are
\(56,104,112,67,69,7,30\); write \(R_i\) for the \(i\)-th
row mask (starting with \(i=0\)). Starting at \(b(0)=0\), for
\(1\le a<128\) use
\(b(a)=b(a-2^i)\mathbin{\rm xor} R_i\) where \(i\) is the
least set bit. Keep precisely the pairs with \(a\mathbin{\&}b(a)=0\).
This checks all \(2^7\) vectors by a short recurrence, without
making any assumption about minimality.

Restrict the table to supports through the dealer, drop that dealer,
and keep the inclusion-minimal sets. For \(d=0\) and \(d=1\) one obtains:
\[
 \begin{array}{c|l}
 d & \text{minimal player sets}\\\hline
 0 &125,\ 136,\ 146,\ 236,\ 246,\ 345\\
 1 &025,\ 036,\ 046,\ 234,\ 356,\ 456 .
 \end{array}
\]
Each row has only triples in a universe of six players. Two triples
can be disjoint only when they are complementary; none of the listed
triples has its complement listed in the same row. Thus both dealers
have a quantum access structure. The permutations
\((1\,2)(3\,4)\) and \((0\,5)(1\,3)(2\,4)\), each fixing vertex 6,
preserve the edge list. The group that they generate has the two
orbits \(\{0,5\}\) and \(\{1,2,3,4\}\) among the old six vertices. Therefore every dealer in \(H\) has a quantum access
structure in \(G_1\). Dealer \(6\) does not, since the disjoint
player sets 013 and 245 each belong by (1).

## 3. The clone clique: all sizes and all dealers

For \(r\ge1\), replace vertex \(6\) in \(G_1\) by a clique \(T\)
of \(r\) vertices, each adjacent to exactly \(S\) in \(H\).
The resulting graph \(G_r\) is connected and simple; \(G_1\) is the
displayed base graph. For any \(x\in\mathbb F_2^6\), \(z\in\mathbb
F_2^T\), put \(t=\sum_{j\in T}z_j,\ u=s^T x\) in \(\mathbb F_2\).
The adjacency action on \((x,z)\) is
\[
    \big(Bx+ts,\ (u+t){\bf1}_T+z\big).                 \tag{2}
\]
On the old six vertices, admissibility thus depends on \(x,t\)
in exactly the same way as in \(G_1\) with old bit \(t\) at vertex 6.
On the new vertices there are the following cases.

* \(z=0\) forces \(t=0\). The clone part has no selected vertex,
  so it is admissible; the support includes all \(T\) if \(u=1\),
  and none if \(u=0\). This is exactly expansion of the old
  pair \((0,u)\).
* \(z\ne0,\ t=0\): a selected vertex has second coordinate
  \(u+1\), so admissibility is equivalent to \(u=1\).
  Then each clone's pair is \((z_j,1+z_j)\), so the support
  includes all \(T\). The same old-six support and expanded clone
  support already occur for \(z=0,u=1\), corresponding to
  the old pair \((0,1)\).
* \(z\ne0,\ t=1\): admissibility is equivalent to \(u=0\).
  The support is all \(T\) by the same complementary coordinates.
  The old pair is \((1,u)=(1,0)\). Conversely every admissible
  old relation with old bit \(1\) has \(u=0\) and is realized in
  every \(G_r\) by taking \(z\) to be a singleton.
  The case \(z=0,t=1\) is impossible.

Thus the **entire family** of admissible nonzero pair supports
of \(G_r\) is obtained from that of \(G_1\) by replacing each
occurrence of \(6\) by all of \(T\), without adding any others.
The inclusion order is preserved and reflected because \(T\ne
\varnothing\). For an old dealer, keeping supports through that
dealer and deleting that dealer commutes with replacement;
so the minimal player supports are exactly the replacements of
the old minima. Intersections of these sets remain nonempty.
For a clone dealer \(d\in T\), keep the former supports through
\(6\) and replace their \(6\) by \(T\setminus\{d\}\).
This gives all player supports; taking their inclusion-minimal
members gives exactly the minimal circuit-induced sets by (1).
When \(r\ge2\) every set contains the nonempty common part
\(T\setminus\{d\}\). There is at least one such set, for example
from the singleton vector selecting \(d\).
Every dealer of \(G_r\) therefore has quantum access structure
when \(r\ge2\).

In every \(G_r\), let the dealer be \(0\) and
\(U=\{1,3\}\cup T\). The singleton vector \(x=e_3,\ z=0\)
in (2) has admissible support \(\{0,1,3\}\cup T\), so
\(U\in\Gamma^{\rm circ}_{L,0}\). For **all** vectors supported
on \(U\cup\{0\}\), the old coordinates outside this set require
\(x_2=x_4=x_5=0\). Their adjacency coordinates must also vanish:
using rows \(2,4,5\) of \(Bx+ts\) in that order gives
\(t=0,\ x_0=0,\ x_1=0\). No other outside coordinates occur.
The dealer part is then exactly \((0,x_3)\), because row 0
has neighbours \(3,4,5\) and is not adjacent to \(T\).
Both values of \(x_3\) occur with \(z=0\).
Thus \(D_0(U)=\{(0,0),(0,1)\}\); this player set is **intermediate**
and is not in \(\Gamma^{\rm rec}_0\). For \(r=1\), \(U=136\);
for every \(r\ge2\), this proves failure of inclusion even
under the stronger all-dealers hypothesis. This is a negative
answer to problem 2, which requires the access-structure axiom
only at the given dealer.

## 4. A bipartite boundary case

For a connected simple binary graph with at least two vertices,
let \(\operatorname{cutrk}(I)\) be the rank of the cross matrix
\(A[I,V\setminus I]\). For \(U\subseteq P\), the space of supported
vectors \(w(x)\) on \(I\) has dimension
\(|I|-\operatorname{cutrk}(I)\), since it requires \(x=0\) off
\(I\) and then \(A[V\setminus I,I]x_I=0\). Taking the difference
at \(I=U\cup\{d\}\) and \(I=U\) gives
\[
  \dim D_d(U)=1+\operatorname{cutrk}(U)-
                    \operatorname{cutrk}(U\cup\{d\}).
\]
By symmetry under taking complementary cuts,
\(\dim D_d(U)+\dim D_d(P\setminus U)=2\).
This also follows from the stabilizer orthogonality identity;
the cut proof fixes the dimension conventions here.

Now assume the graph is bipartite. Every supported vector splits
by the two colour classes into two vectors \(w(x_L)\) and
\(w(x_R)\), where \(x=x_L+x_R\). The second part of \(w(x_L)\)
is supported only on the other class, and conversely for \(w(x_R)\).
Thus both vectors are admissible. Furthermore neither one has
support outside the original support \(S(x)\): in each class
the first and second types come from different summands with no
cancellation. A nonzero dealer part of \(w(x)\) therefore yields
a nonzero dealer part of at least one of these admissible vectors.
By (1), for bipartite graphs the circuit-induced family is exactly
the sets with \(\dim D_d(U)\ge1\).
If a rank-one set exists, its complement has rank one and is
another member, contrary to pairwise intersection. If no rank-one
set exists, the circuit family equals recovery; it is nonempty
by surjectivity, increasing, and pairwise intersecting because
the complement of each rank-two set has rank zero. Consequently
at each fixed dealer the three conditions
\[
 \Gamma^{\rm circ}_{L,d}\text{ is a quantum access structure},
 \quad
 \Gamma^{\rm circ}_{L,d}=\Gamma^{\rm rec}_d,
 \quad
 \text{there are no intermediate sets}
\]
are equivalent.

For the all-dealers equality on a connected bipartite graph,
write \(A=\left(\begin{smallmatrix}0&K\\K^T&0\end{smallmatrix}\right)\)
in the two classes, with row generator \([I\mid K]\) for a binary
linear code \(C\) on \(V\). Swapping the two local coordinates
on each vertex of the second class sends the stabilizer
row space to the direct sum of pure first-coordinate words
from \(C\) and pure second-coordinate words from \(C^\perp\):
the two generator matrices are \([I\mid K]\) and \([K^T\mid I]\),
which are complementary by their ranks and orthogonality.
The swaps preserve pair support and dealer-projection dimensions.
So, for any \(I\ni d\), the existence of a word of \(C\) supported
on \(I\) and nonzero at \(d\), and the analogous existence for
\(C^\perp\), determine the two coordinate directions in
\(D_d(I\setminus\{d\})\). No intermediate set at any dealer
implies the two existences always coincide.

If \(c\in C\) has inclusion-minimal nonempty support \(I\),
take a dealer in \(I\) to get a nonzero \(z\in C^\perp\)
supported on \(I\). If \(\operatorname{supp}(z)\subsetneq I\),
take a dealer in that smaller support and apply the reverse
existence to contradict the minimality of \(I\).
Thus \(z\) has support \(I\) and equals \(c\) over \(\mathbb F_2\).
Every word of \(C\) is a sum of support-minimal words, by
repeatedly removing a binary word with minimal nonempty support
inside the current support. Thus \(C\subseteq C^\perp\).
Interchanging the codes gives equality \(C=C^\perp\).
Conversely if \(C=C^\perp\) the two existences always coincide,
so no dealer has any intermediate set. In systematic form
\(C=C^\perp\) is equivalent to \(K\) square and \(KK^T=I\),
equivalently \(A^2=I\).
This gives the claimed connected bipartite subclass for the
all-dealers equality in problem 3. The sufficiency of the
orthogonal block condition for a perfect bipartite graph-state
encoding was already known (Sarvepalli, arXiv:1202.3433,
Theorem 4); the argument here also provides the converse and
the fixed-dealer equivalence in these circuit-family terms.

## 5. Small sizes and scope of the computation

The family proof above needs only the seven-vertex table.
We also regenerate all simple graphs up to seven vertices
for the minimality statements. Start with one vertex;
augment each isomorphism class on \(n-1\) vertices with a vertex
having each possible neighbour set. Every next class occurs:
delete a vertex of a given graph and relabel its parent to a
representative, then take the corresponding neighbour set.
A canonical key first orders vertices by degree and then takes
the lexicographic minimum of the binary edge mask over all
permutations within equal-degree blocks (the integer order in
the code is just a fixed total order). Two graphs have the same
key iff they are isomorphic: any isomorphism preserves degrees,
and a common mask itself identifies an isomorphism. Thus this
is an exhaustive finite check, not a random graph sample.

For sizes two through six the circuit/recovery counts reproduce
Ganguly v2 Table I, including no failure of inclusion among
quantum access structures. At seven vertices there are 853
connected simple graphs up to isomorphism; eleven have a
fixed-dealer counterexample, with 34 bad dealer positions
when counting vertices on one representative per graph.
This is not a count of rooted isomorphism types.
Six seven-vertex graphs satisfy the all-dealers access axiom,
none a counterexample. In disconnected graphs the observing
sets are determined by the component of the dealer: cut ranks
and supported vectors split by components, and an admissible
witness through a dealer can be restricted to its component.
An isolated dealer does not yield the access axiom, as the
zero column gives the empty player support. Thus the minima
over all simple graphs are seven vertices for a fixed-dealer
failure and eight for an all-dealers failure (with finite
minimality evidence through seven). These computations do not
replace the all-\(r\) support argument, and neither the
counterexample nor the bipartite result is a claim about
nonbinary field representations or about unrelated encodings.
