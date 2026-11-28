# Proof

## 1. Statement and conventions

For each \(t\ge0\), let \(G_t\) replace every edge of \(K_4\) by a path of
length \(3^t\), with different paths internally vertex-disjoint. There is an
\(\mathbb F_8\)-linear isotropic representation of \(\mathcal S(G_t)\) whose
stabilizer code has parameters
\[
[[\,6\cdot3^t,\ 2,\ 2^{t+1}\,]]_8. \tag{1}
\]
The graph used here is Chow's **edge-indexed** graph, not the graph on
qudits used to specify a symmetric adjacency/check matrix.

Write \(e,e^*\) for the two labels of an edge \(e\); the starred label selects
the \(z_e\)-column and the unstarred label the \(x_e\)-column. An **admissible**
set selects at most one from each pair. By Chow's definition the set is
independent exactly when every component of the corresponding spanning
subgraph is a tree (isolated vertices included) or unicyclic with an odd
number of stars on its unique cycle. In a representation, such independence
is exactly independence of the selected columns. The bases are the
independent admissible sets of size equal to the row rank.

For a set of sites \(J\), use the paired coordinate space
\[
E_J=\bigoplus_{j\in J}\mathbb F_q^2,\qquad
\omega(v,w)=\sum_j (x_jz'_j-z_jx'_j).
\]
The weight counts sites with nonzero pairs. An isotropic row space \(S\) of
dimension \(r\) on \(n\) sites yields a stabilizer code with \(k=n-r\).
When \(k>0\), the distance is the minimum weight in \(S^\perp\setminus S\).
This is the standard finite-field stabilizer construction and distance
formula. The \(\mathbb F_q\)-symplectic orthogonal here is also the orthogonal
for the trace-Pauli commutation form: if a pairing with \(S\) is a nonzero
field element, multiplying the row by field scalars produces a pairing of
nonzero trace. Throughout the construction below the field has
characteristic two.

## 2. Local lemma: the chosen cycle columns are a signed-path interface

Let \(L\ge2\), and suppose \(W\) is an isotropic representation of the
Chow matroid of the cycle \(C_{L+1}\), with one distinguished edge \(d\)
and physical sites given by the remaining \(L\) edges in path order. This
is a Lagrangian space of dimension \(L+1\): the cycle has an independent
full transversal and no admissible set larger than \(L+1\).

View the columns as coordinate functionals on \(W\). Write \(c_d,c_{d^*}\)
for the two port functionals. Let \(F\) select at most one physical column
per site. A full physical selection always has rank \(L\) in \(W^*\), since
it selects a path rather than the whole cycle. Likewise every smaller
admissible set is independent. A full selection completed by a port
choice is independent exactly when the total star parity is odd.

* If \(|F|<L\), both port columns are nonzero modulo \(\langle F\rangle\):
  each one by itself extends \(F\) to a proper, independent set. If the
  two images are proportional, extend \(F\) to any full physical
  selection \(F'\). Modulo \(\langle F'\rangle\), the two images are
  either both zero or both nonzero, since the proportionality factor
  was nonzero. This contradicts exactly one of the two full completions
  being independent. Thus in this case the columns of \(F\) and the two
  port columns are jointly independent. In particular, the port map
  \(\pi:W\to\mathbb F_q^2\) is onto.
* If \(|F|=L\), write \(s\in\{0,1\}\) for the parity of physical stars.
  The dependent port completion is \(d\) if \(s=0\), or \(d^*\) if
  \(s=1\). Thus
  \[
  \langle F\rangle\cap P=
  \begin{cases}
  \mathbb F_q c_d,&s=0,\\
  \mathbb F_q c_{d^*},&s=1,
  \end{cases}\qquad P=\langle c_d,c_{d^*}\rangle. \tag{2}
  \]
  Indeed, one port column belongs to \(\langle F\rangle\), the other
  does not, and the port columns are linearly independent.

Set \(U=\{p:(0,p)\in W\}\), the physical part when the port is zero.
Restricting functionals to \(\ker\pi\) is quotienting \(W^*\) by \(P\),
because two independent port functionals span exactly the annihilator
of \(\ker\pi\). It follows that on \(U\) a partial physical selection has
no column relation, and a full selection has a one-dimensional relation
space. Any nonzero relation in the full case, as a functional on \(W\),
equals a **nonzero** multiple of the appropriate port coordinate in
(2); it cannot vanish on \(W\), because the \(L\) physical functionals
are independent there.

## 3. Concatenation, all admissible ranks, and distance

Let an isotropic \(S_0\subseteq E_{E(G)}\) represent the Chow matroid of a
loopless simple graph \(G\). Replace each edge \(e\) with a path of length
\(L_e\ge2\), internally disjoint from other paths. Use a cycle module
\(W_e\) as above at each edge, with shortened space \(U_e\). The rank
signature proved in §2 is for the specified, named \(x,z\) coordinates,
not just for some arbitrary logical basis.

In a module, deleting the port coordinates from \(W_e\) is injective:
a word entirely at the port would pair trivially with every port value
by isotropy and thus be zero by surjectivity. Its physical image is
\(U_e^\perp\). Inclusion follows from isotropy with \((0,u)\in W_e\);
equality follows from
\(\dim U_e=L_e-1\) and \(\dim U_e^\perp=L_e+1=\dim W_e\).
Define the surjection
\(\phi_e:U_e^\perp\to\mathbb F_q^2\) by the actual port values of the
unique lift to \(W_e\). Its kernel is \(U_e\), and
\[
\omega_{\rm phys}(p,p')=-\omega_{\rm port}(\phi_e p,\phi_e p')
                      =\omega_{\rm port}(\phi_e p,\phi_e p'). \tag{3}
\]
Thus these same two port axes give a symplectic pair of logical coordinates
in characteristic two. Identify them, in order, with the actual
\((x_e,z_e)\) of the old edge. In particular there is no interchange of
the two outer columns at this join.

Let \(\Phi=\bigoplus_e\phi_e\) and define
\[
S=\{(p_e)_e\in\bigoplus_e U_e^\perp:\Phi((p_e)_e)\in S_0\}. \tag{4}
\]
This is isotropic by (3). It has dimension \(\dim S_0+\sum_e(L_e-1)\),
inverse image dimension under an onto map, while the number of sites is
increased from \(|E(G)|\) by the same \(\sum_e(L_e-1)\).
One obtains a generator matrix by taking the local shortened generators
individually on each path and one lift of each row of \(S_0\). Lifts can
use any fixed linear section of the stated \(\phi_e\), and different
sections only change rows by local shortened generators.

**Admissible rank.** For an admissible set \(A\) in the new graph, write
\(F_e\) for its selection on the replacement path for \(e\). Define a
signed selection \(B\) on \(G\) by keeping precisely edges whose path is
*fully* selected, as \(e\) for even and \(e^*\) for odd physical star
parity. A putative relation among the new selected columns must
annihilate the shortened rows on **each** path separately. This holds
even when many paths are incomplete, since the shortened generators
are supported on just one path each. By §2 the coefficients on any
incomplete path are all zero; the coefficients on any full path form
one relation line there. Choose its generator normalized so that on
\(W_e\) it evaluates to the correct port coordinate (2). Applying a
relation with these block coefficients to the lifted outer rows is
therefore exactly the corresponding relation on the \(S_0\)-columns
selected by \(B\). This is a linear bijection of relation spaces,
including the converse, since any relation on \(B\) lifts by the same
normalized block generators. The selected-column ranks satisfy
\[
\operatorname{rk}_{S}(A)
 = |A|-|B|+\operatorname{rk}_{S_0}(B). \tag{5}
\]
Here the ranks denote linear column ranks, before claiming
\(\mathcal S(G_{\rm new})\) is represented.

Every unfinished path contributes only segments attached to at most
one old vertex, or disjoint path components. Such segments cannot
change which old vertices are connected, whether a component is a
tree or unicyclic, or a cycle's star parity. The graph formed by the
complete paths is a subdivision of the subgraph on \(B\), and stars on
each cycle add modulo two under contraction to that subgraph. Thus the
Chow test on \(A\) is equivalent to the Chow test on \(B\).
Equation (5) shows exactly that every admissible set, and hence every
basis, is realized as required by \(\mathcal S(G_{\rm new})\).

**Distance.** Any vector in \(S^\perp\) belongs to
\(\bigoplus_e U_e^\perp\), since \(S\) contains each \(U_e\) on its own
path. By (3), orthogonality to \(S\) in this space is equivalent to
having its \(\Phi\)-image in \(S_0^\perp\). Equation (4) then gives
\[
S^\perp\setminus S=\Phi^{-1}(S_0^\perp\setminus S_0)
\quad\text{inside }\bigoplus_e U_e^\perp. \tag{6}
\]
In particular a nonzero label at an old logical support site must be
represented by a nontrivial local logical word. If **every** nonzero
label in every module has minimum physical weight exactly \(\Delta\),
then any such vector has weight at least \(\Delta\,d(S_0)\). For the
upper bound choose a least-weight outer logical word and independently
a minimum representative of each of its nonzero port labels, using the
zero word elsewhere. The resulting vector lies in (6) and has weight
exactly \(\Delta\,d(S_0)\).

## 4. The explicit four-cycle module over \(\mathbb F_8\)

Let \(\mathbb F_8=\mathbb F_2[\alpha]/(\alpha^3+\alpha+1)\), where the
cubic is irreducible because it has no root in \(\mathbb F_2\). Index
the four edge sites of \(C_4\) cyclically by \(0,1,2,3\), with port
\(d=0\). Let
\[
A=\begin{pmatrix}
0&1&1&1\\
1&0&\alpha^2&\alpha\\
1&\alpha^2&0&1\\
1&\alpha&1&0
\end{pmatrix}.
\]
Form \([I_4\mid A]\) and swap its columns \(x_0,z_0\), both still in
their original labeled slots. The explicit matrix of \(W\) is
\[
M=\left[
\begin{array}{cccc|cccc}
0&0&0&0&1&1&1&1\\
1&1&0&0&0&0&\alpha^2&\alpha\\
1&0&1&0&0&\alpha^2&0&1\\
1&0&0&1&0&\alpha&1&0
\end{array}\right]. \tag{7}
\]
The unswapped space is Lagrangian by symmetry of \(A\), and swapping
one pair preserves the symplectic form in characteristic two.

A transversal of \([I_4\mid A]\) with stars at \(T\) has determinant
\(\det A[T,T]\) up to sign, by expansion along the identity columns.
The zero-order minor is 1; each principal minor of order two is the
square of a nonzero entry. The odd-order minors vanish: order one
has zero diagonal, and in order three the only potentially nonzero
permutations are the two 3-cycles, whose products cancel. In order
four the 4-cycles cancel in inverse pairs, leaving the three
disjoint-transposition products, so
\(\det A=(1+\alpha+\alpha^2)^2\ne0\). The inequality follows from the
degree of \(\alpha\) over \(\mathbb F_2\). The swap of the port
therefore makes odd, rather than even, star parity characterize the
independent transversals. Every proper admissible set extends to such
a transversal and is independent. This is precisely the entire Chow
test for \(C_4\).

Every cross-cut submatrix \(A[T,T^c]\) has rank
\(\min(|T|,|T^c|)\). For a singleton cut use any nonzero incident entry.
For a two-versus-two cut its determinant is a sum of two different
members of \(\{A_{01}A_{23},A_{02}A_{13},A_{03}A_{12}\}
=\{1,\alpha,\alpha^2\}\), hence nonzero. Empty cuts impose no condition.
Before the port swap, a row word \((v,vA)\) supported on \(T\) has
\(v\) zero off \(T\), and \(v_T A[T,T^c]=0\). Thus the supported
subspace of \(W\) has dimension \(|T|-\operatorname{rk}A[T,T^c]\),
unchanged by the port swap. In particular, no nonzero word of \(W\)
can be supported on at most two sites. A nonzero port value cannot
therefore have a physical representative of weight zero or one.
For any two physical sites \(P'\), the supported space on
\(P'\cup\{0\}\) has dimension \(3-1=2\). Projection onto the port is
injective there because its kernel is supported on \(P'\), so it is
onto \(\mathbb F_8^2\). This proves that every one of the 63 nonzero
port labels has physical minimum weight exactly two, and can use
**any** pair of physical sites. The shortened code is \([[3,1,2]]_8\).

For implementability, number the rows of (7) as \(m_0,\ldots,m_3\).
Delete the port pair after taking \(m_2+m_1,m_3+m_1\) for the shortened
generators. Delete it from \(m_1,m_0\) to get the lifts of \((1,0),(0,1)\)
respectively. The precise field elements and the order of the two
axes are fixed for every copy of the module.

## 5. The base and iteration

Use edge order \(01,02,03,12,13,23\) for \(K_4\), and \(u=1+\alpha\).
Its root-0 reduced incidence matrix \(D\) and its flow
\(\lambda=(1,\alpha,u,u,\alpha,1)\) give
\[
H_0=\left[
\begin{array}{cccccc|cccccc}
1&0&0&1&1&0&1&0&0&u&\alpha&0\\
0&1&0&1&0&1&0&\alpha&0&u&0&1\\
0&0&1&0&1&1&0&0&u&0&\alpha&1\\
0&0&0&0&0&0&1&\alpha&u&u&\alpha&1
\end{array}\right]. \tag{8}
\]
Each star column is \(\lambda_e(D_e,1)^{\mathsf T}\), with the
unstarred column \((D_e,0)^{\mathsf T}\). The top symplectic Gram
block vanishes because \(D\operatorname{diag}(\lambda)D^{\mathsf T}\)
is symmetric, while pairings with the last row vanish because
\(D\lambda^{\mathsf T}=0\) (each vertex sees \(1,\alpha,u\)). The rows
are independent, since \(D\) has rank three and the last row has zero
\(x\)-part and nonzero \(z\)-part.

For the Chow test, scale selected stars by \(\lambda_e^{-1}\).
The top three rows then form the usual reduced incidence columns
on the selected edges. Their dependencies are the usual cycle
dependencies: for a forest, leaf elimination in the full incidence
matrix gives independence, and omitting the row of vertex 0 changes
no dependency since the omitted row is the sum of the others.
In a unicyclic component, peeling off the leaves leaves just the
all-ones relation on its cycle, on which the bottom row evaluates
to the star parity. \(K_4\) cannot have two vertex-disjoint cycles.
If a component has more than one cycle, its number of edges exceeds
its number of vertices, but the top rank in that component is at most
its number of vertices minus one and the bottom row adds at most
one. The selected columns are then dependent. These cases establish
the full admissible representation.

Each edge pair spans two independent columns, so no nonzero
one-site word is orthogonal to \(S_0=\operatorname{row}(H_0)\):
the restriction of the row space to those two coordinates is onto.
On the two sites \(01,02\), the paired columns have rank three
(their two incidence vectors are independent, and a scaled star
column differs from its unstarred column by the common bottom
coordinate). Thus there is a nonzero normalizer word supported on
these sites, as the solution space of the orthogonality equations
there has dimension \(4-3=1\). The complement \(03,12,13,23\) is
connected unicyclic. Starring just one edge of its triangle gives
four independent columns and shows that no nonzero \(S_0\) word is
supported on \(01,02\). The supported normalizer word is therefore
logical, and \(d(S_0)=2\).

Now apply (4) with the module (7) on every edge at each level. By (5)
the matrices represent the actual subdivided graphs at every level.
Every step triples the number of sites, leaves \(k=2\), and by (6)
doubles the **exact** distance. This proves (1) for all \(t\).
The family has unbounded distance at fixed alphabet and is not a
claim of positive asymptotic rate or a rate–distance classification.
