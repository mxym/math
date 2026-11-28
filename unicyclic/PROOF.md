# Exact support for graph-CMSS on unicyclic graphs

## 1. Model

Let \(G\ne C_3\) be a finite connected simple graph with exactly one
cycle, and let \(D\subseteq\{0,1\}^{V(G)}\) be nonempty. A finite source
\(R\) with arbitrary positive weights is drawn independently of the
input \(x\in D\). Each edge gets a label \(W_e(x,R)\) from a finite
alphabet, and vertex \(v\) sees the ordered tuple of its incident labels.
The view determines \(x_v\) on every input and source state.
Its distribution is equal for any two inputs with the same \(x_v\).
This is the pointwise perfect-correctness, individual-perfect-privacy
model of Marszalik [M], §II Eqs. (1)–(3). There is no coalition or
positive input-probability parameter; the minimization is over the
cardinality of the dealer support, not the entropy of its weights.

Call an edge \(uv\) a *pair edge* when \(x_u\oplus x_v\) is constant on
\(D\). A vertex is active when its own bit is nonconstant on \(D\), and
covered when it touches a pair edge. The cycle has vertices
\(0,\ldots,\ell-1\) in cyclic order, with \(e_i=\{i,i+1\}\).
A cycle vertex is *rigid* if it is active, uncovered, and has degree
two in \(G\), and is flexible otherwise. Fix a base word \(z\in D\)
and write \(u_i(x)=x_i\oplus z_i\).

**Theorem.** Use the first applicable case:
1. If an active uncovered leaf exists, no scheme exists.
2. If every active vertex is covered, the minimum support is one.
3. The minimum support is two if some cycle edge has two flexible
   endpoints, or if there exists a cycle-vertex subset \(B\) containing
   every rigid vertex such that \(\bigoplus_{i\in B}x_i\) is constant on
   \(D\).
4. The minimum support is three if the following test succeeds. Choose a
   set \(E\) of flexible cycle vertices and \(\beta_i\in\mathbb F_3\),
   with \(\beta_i\ne0\) at every rigid vertex, satisfying for every \(x\in D\)
   \[
   \sum_{i\in E}u_i(x)=0\pmod 2,\qquad
   \sum_{i=0}^{\ell-1} (-1)^{\sum_{j\in E,\ j>i}u_j(x)}
                          \beta_i u_i(x)=0\pmod 3.
   \tag{1}
   \]
5. Otherwise the minimum support is four.

The labels and source distribution in this theorem have no a priori
linear or uniform restriction. The case \(G=C_3\) is the separately
known binary three-secret-sharing problem, with no four-state upper
bound claimed here.

## 2. Common edge marginals and at most two states

By privacy an edge marginal depends on its input only through either
endpoint bit. For a non-pair edge, the bipartite support of its occurring
endpoint-bit pairs is connected: if exactly one bit varies it is a star;
if both vary the only disconnected case with all four value nodes present
is a perfect matching, which would make the edge a pair edge. Hence
non-pair edge marginals are the same for every input. A constant edge
law is also pointwise constant because all source weights are positive.
An uncovered active leaf would need to decode from an edge whose
marginal does not vary with its bit, which is impossible.
With one source state, all non-pair edge labels are constant, so every
active vertex must be covered. Conversely send \(x_u\) on a pair edge
\(uv\) (with a fixed choice of \(u\)), and constants otherwise. The
first two assertions follow; pair edge labels, when used below, are
always such deterministic functions of the local bit at either endpoint.

With two source states it is enough to consider uniform weights.
Under unequal weights, equality of two view laws identifies the same
view at each state when the two values are different; when they coincide
it identifies their common value. Replacing by equal weights therefore
preserves privacy. This is [M, Lemma 9].

For sufficiency of the two-state test, first suppose a cycle edge has
two flexible endpoints. Delete this edge and all pair edges and retain
the other edges, which form a forest. Every uncovered active vertex
originally has degree at least two, loses no pair edge, and if it touches
the extra deleted edge it has degree at least three. Thus it has at least
two retained incidences. At each uncovered active vertex assign signs
\(q_v(e)\in\mathbb F_2\) to its local incidences so both signs occur.
There is no constraint at covered or inactive vertices.
If there is no such edge but the parity condition on \(B\) holds,
every cycle edge touches a rigid vertex and therefore is non-pair.
Retain every non-pair edge. On the cycle assign opposite incidence
signs at the vertices in \(B\), and equal signs at the other cyclic
vertices. A cyclic uncovered active vertex not in \(B\) is flexible,
has degree at least three, and can use an additional branch edge with
opposite sign. Off-cycle uncovered active vertices can use any two
incidences with different signs. These assignments are independent
at the two ends of an edge.

For any such selected subgraph and any fixed \(x\), define a phase
\(p_v(x)\in\mathbb F_2\) per vertex solving
\[
p_u(x)+p_v(x)=q_u(e)(x_u\oplus z_u)+q_v(e)(x_v\oplus z_v),
\qquad e=uv\text{ selected}.
\tag{2}
\]
Solve by propagation from zero at one root per component. The graph
is a forest or unicyclic; in the latter case its only possible
cycle is the full original cycle, and (2) is consistent because
the cycle sum of its right side is \(\sum_{i\in B}u_i=0\).
On a selected edge use \(W_e=R+p_v(x)+q_v(e)(x_v\oplus z_v)\)
with the same single fair bit \(R\) for all components. Equation (2)
makes the endpoint expressions agree. At any vertex the \(R+p_v\)
part is a common uniform bit, and the view including pair or other
constant edges has a distribution depending only on \(x_v\).
Any uncovered active vertex gets opposite signs, whose XOR recovers
\(x_v\oplus z_v\). This is the cycle specialization of [M, Theorem 3].

For necessity in the only remaining case, every cycle edge touches
a rigid vertex and is non-pair. At a rigid vertex neither edge is
constant, or the entire view law would be fixed regardless of its
bit. Therefore, with uniform two-state source, every cycle edge
uses both labels, independently of the input as an unordered
pair of values. Relabel each edge's two labels as bits. At any cycle
vertex its pair of cyclic labels always has a deterministic XOR
for a given input: each edge is a bijection on the two states.
The XOR depends only on that vertex's bit by privacy even when
it has other edges. At rigid vertices the two XOR values must
differ, since otherwise the two full-view supports intersect.
Thus the XORs of adjacent cycle labels give constants and terms
\(x_i\oplus c_i\), with the latter occurring at a set \(B\) that
contains every rigid vertex (inactive vertices may be assigned
constants). XORing over the cycle gives the required parity
relation on \(B\). This proves the at-most-two test.

## 3. Three-state necessity

In the residual cases no solution with support at most two exists.
Every cycle edge touches a rigid vertex, and its marginal is fixed.
By [M, Proposition 12], only weights
\(\mathsf U=(1,1,1)/3\) or \(\mathsf Q=(2,1,1)/4\) need be tested,
up to permutation. Here is the reduction. If three weights are
distinct and no weight is \(1/2\), all subset sums differ, so equality
of any two view laws matches each fiber at the same source states.
Fixing one state gives a deterministic scheme. If exactly two weights
agree and the vector is not \(\mathsf Q\), equal-mass subsets agree on
whether they contain the distinctly weighted state, because its
weight is not the sum of the other two and differs from each.
Fix the distinct state. If all weights are distinct and one is
\(1/2\), the only different equal-weight subsets are the singleton
half-state and the pair of light states. A two-block partition of
that form can only be matched to itself or exchange its labels;
otherwise matching all fibers preserves every state-to-label
assignment. Retaining one light state and the half-state, with
equal weights, preserves privacy in both cases and preserves
correctness. This exhausts the reductions.

### 3.1. Uniform three-state source

At a rigid vertex no edge is constant. Two two-atom marginals
each have an atom of mass \(2/3\); their joint pair has positive
mass for every input, contradicting correctness. If one edge
is fine (three distinct equiprobable atoms) and the other has
two atoms, every fine label is paired with exactly one other
label. Disjoint supports across the two bit classes require
switching the binary partner of every fine label, swapping the
unequal marginal masses \(1/3,2/3\), impossible.
Thus both edges of each rigid vertex are fine, and every
cycle edge is consequently fine.

Identify the three labels of each edge with \(\mathbb F_3\).
At each cycle vertex \(i\), the pair of cycle labels has support
the graph of a permutation \(h_i^b\in S_3\) of its left label
to its right label, depending only on its own bit \(b\) by
privacy. This holds also at flexible vertices where this pair
might not suffice for decoding. At a rigid vertex the two
graphs are disjoint, so \(h_i^{1-b}(h_i^b)^{-1}\) is a
derangement, necessarily a nonidentity 3-cycle. For each
input the ordered product \(h_{\ell-1}^{x_{\ell-1}}\cdots
h_0^{x_0}\) is the identity: walking around the cycle returns
the same label for all three possible source draws.

Put \(g_i=h_i^{z_i}\), and \(\Delta_i=h_i^{1-z_i}g_i^{-1}\)
at active vertices; set \(\Delta_i=1\) if that bit value
never occurs. Then \(h_i^{x_i}=\Delta_i^{u_i}g_i\).
Use \(g_{\ell-1}\cdots g_0=1\) and successively expand the
ordered product: it equals the product, in descending order
of \(i\), of \(d_i^{u_i}\), where \(d_i\) is \(\Delta_i\)
conjugated by \(g_{\ell-1}\cdots g_{i+1}\).
Every permutation of three letters is uniquely affine on
\(\mathbb F_3\), of form \(r\mapsto s_i r+\beta_i\) with
\(s_i=\pm1\). At rigid vertices \(s_i=1,\beta_i\ne0\)
because conjugation preserves a nonidentity 3-cycle.
The sign of the composed map is the product
\(\prod_{i:u_i=1}s_i\), giving the first equation of (1)
for \(E=\{i:s_i=-1\}\). Its translation coefficient is the
sum of each \(\beta_i u_i\) with the product of later signs
as multiplier (those indices \(j>i\) in the chosen order).
This gives exactly the second equation of (1).

### 3.2. Half-heavy three-state source

For \(\mathsf Q\), each cycle edge marginal is constant, binary
with masses \(3/4,1/4\), binary with masses \(1/2,1/2\),
or fine with masses \(1/2,1/4,1/4\).
At a rigid vertex a constant edge makes the full law fixed.
An atom of mass \(3/4\) co-occurs with a fixed atom of mass
at least \(1/2\) on the other edge for every input, also
impossible. Thus all cycle edges are balanced binary or fine.
For a fine edge the unique half-mass label occurs on the
heavy source state for all inputs; two fine edges at a rigid
vertex would give a common atom in the two bit classes.

Coarsen each fine edge to the bit zero at the half-mass label
and one at the two other labels, leaving each balanced binary
edge as a bit. At each input both light states give the same
bit on every edge, opposite to the heavy-state bit.
Thus the adjacent XOR at each cycle vertex is deterministic
for a given input and depends only on the vertex bit, by
privacy. At a rigid vertex with two balanced edges, equal
XOR in the two classes gives the same two supports, a
contradiction. At a rigid vertex with a fine and a balanced
edge, equal XOR fixes the same balanced label at the heavy
state, whose fine label was already fixed, also a contradiction.
Therefore the adjacent XOR toggles at all rigid vertices.
Summing the adjacent XORs around the cycle gives the parity
condition on a \(B\) containing all rigid vertices. Such a
condition was excluded. So \(\mathsf Q\) adds no case.

## 4. Sufficiency and attaching the trees

We use a simple extension observation. Suppose a scheme has
been specified on the cycle. For each cycle vertex \(i\),
suppose a uniform element \(Z_i\) of a common finite group
\(H\) can be read from its cycle view, and its cycle view
is a fixed function of \((Z_i,x_i)\).
Use deterministic labels on pair edges off the cycle; the
other off-cycle edges are oriented away from the cycle in
their attached trees. Starting from the corresponding \(Z_i\)
at each cycle root, propagate one full group label on each
non-pair branch edge. At an off-cycle vertex use its incoming
non-pair label as its reference \(Z_v\). If the parent edge
is pair, start a new reference using the original dealer
variable uniformly in \(H\), and note that the vertex is
covered. No independence between these references is needed.

To assign outgoing non-pair labels, normally repeat \(Z_v\).
If \(v\) is active and uncovered and does not already decode
from the cycle, choose one outgoing non-pair edge and
send \(Z_v+a x_v\) on it, where \(a\) is a fixed nonzero
group element and additive notation is used. At an off-cycle
such vertex the parent is non-pair and at least one child is
non-pair, since it has degree at least two and is uncovered.
At a cyclic vertex needing this step it is flexible and
active uncovered, hence has a child non-pair edge.
The incident reference label or cycle-extracted reference
then lets the vertex recover its bit. Every incoming reference
is uniform for fixed input, since it starts uniform and shifts
are translations. At every vertex all its observed labels are
functions of that reference and its own bit, so the entire
view is private. This extension does not add randomness and
works with \(H=\mathbb F_3\) or \(H=\mathbb F_2^2\).

If (1) holds, put \(d_i(r)=s_i r+\beta_i\), with \(s_i=-1\)
on \(E\) and \(1\) otherwise. Choose a single uniform
\(R\in\mathbb F_3\), set the edge from \(\ell-1\) to 0 to
have label \(R\), and apply the transition \(d_i^{u_i(x)}\)
to the left label to specify the right label at each vertex.
The product is the identity by (1), so the cycle closes.
At a rigid vertex the translation is nonzero on the flipped
bit, giving correctness, and every cycle pair distribution
depends only on that bit. Its left label gives the required
\(Z_i\). Flexible active uncovered cycle vertices may use
the attachment procedure even if their own pair fails to
decode (in particular at a reflection); covered vertices
can use their deterministic off-cycle pair edges. This gives
a full three-state scheme for every instance passing (1).

For the four-state upper bound only residual instances with
no at-most-two scheme need treatment. If \(\ell\ge4\), use
a single uniform \(R\in\mathbb F_2^2\) and \(a=(1,0),b=(0,1)\).
As in the cycle-only construction, use increments
\[
t_0=b x_0+a\sum_{j\ge2}x_j,\quad t_1=b x_1,\quad
t_2=a x_2+b(x_0+x_1),\quad t_i=a x_i\ (i\ge3)
\tag{3}
\]
where the indices are cycle vertices and the bits are added
modulo two. The sum is zero. Set \(Y_i=R+\sum_{j=0}^i t_j\).
Edge \(e_0\) sends only its second coordinate, \(e_2\) only
its first, and all others send the full \(Y_i\). These two
edges are disjoint, including for \(\ell=4\). Each vertex
sees at least one complete uniform vector to use as \(Z_i\).
At vertices 0 and 1 the visible second-coordinate difference
is \(x_i\); at 2 and 3 the analogous first difference is
\(x_i\); at other vertices the complete difference is
\(a x_i\). This both decodes and exhibits every cycle view
as a function of \((Z_i,x_i)\). Attach the trees as above.

For \(\ell=3\) the exclusion \(G\ne C_3\) ensures a cycle
vertex has an attached tree and is flexible. In the
residual case no cycle edge has two flexible endpoints,
so there is exactly one such vertex; relabel it 0, with
1 and 2 rigid. In fact the three-state test never succeeds in
this triangular residual case. The only possible reflection
position is 0, and if used, its switch must vanish identically
by the parity equation of (1). Thus (1) reduces to an ordinary
affine relation with both rigid coefficients nonzero. If the
coefficient at 0 is zero, every fiber of the sum or difference
of the two rigid bits fixes their XOR, making their edge pair.
If all three coefficients are nonzero, complementing some bits
reduces the relation to a fixed sum modulo 3. Its fiber is of
weight 1, weight 2, or the two complementary words of weights
0 and 3. These respectively give constant total parity or a
pair edge, contrary to the residual conditions. These tests
remain unchanged in form under the bit complements.

For its four-state construction, use
\(t_1=b x_1,\ t_2=a x_2,\ t_0=t_1+t_2\)
with the same full vectors \(Y_i\) as before, but now send
only the second bit on \(e_0\), only the first on \(e_2\),
and the full vector on \(e_1\). At vertex 1 or 2 one full
reference and an appropriate coordinate difference give
both privacy and correctness. At vertex 0 the two received
bits are different coordinates of the uniform mask, shifted
by deterministic phases, so their ordered pair is itself
uniform over \(\mathbb F_2^2\) and is an available reference
\(Z_0\). The cycle view is that pair; an active uncovered
vertex 0 uses a branch for correctness. This again implements
the extension. The proof of the classification is complete.

## 5. Ordinary signed linear slices do not suffice

Take a six-cycle with one attached leaf at each even vertex.
The three attached leaf bits are fixed to zero. In cyclic
order let the even bits be \(f_0,f_2,f_4\) and the odd bits
\(r_1,r_3,r_5\). Choose the even transitions to be reflections
\(v\mapsto-v\) when their bit is one, and the odd transitions
to be \(v\mapsto v+1\) when their bit is one. Take \(D\) to
contain exactly the cycle inputs for which the ordered product
closes, with the three attached bits zero. Equivalently the
even-bit parity is zero and the translation equation of (1)
holds. The all-zero word is in \(D\).

All cycle bits are active and no cycle edge is pair: the all-zero
word and the word with \(f=000,r=111\) differ only on all three
odd coordinates, toggling each cyclic endpoint XOR, while the
even bits occur in nonzero even-parity patterns with \(r=000\).
All odd vertices are rigid, and the two specified words exclude
any binary parity relation whose coefficient is one at each
rigid vertex. No cycle edge has two flexible endpoints.
Thus the optimum is exactly three by (1).

There is no affine relation over \(\mathbb F_3\) on the cycle
coordinate bits with nonzero coefficients on all three rigid
positions. In the fixed fiber \(f=000\), comparing \(r=000,111\)
gives \(\beta_1+\beta_3+\beta_5=0\). In the fiber
\((f_0,f_2,f_4)=(1,1,0)\), the translation condition is
\(-r_1+r_3+r_5=0\); comparing \(000\) with \(110\) and \(101\)
gives \(\beta_1+\beta_3=0\) and \(\beta_1+\beta_5=0\).
The three equations force all three odd coefficients to zero.
In particular the unicyclic rule is not just the earlier
cycle signed-linear relation with zero coefficients allowed at
flexible positions.
