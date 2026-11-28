# Exact support thresholds for graph-CMSS on every cycle

## 1. Model and theorem

Fix the simple cycle \(C_n\) of length \(n\ge4\), with vertices
\(0,\ldots,n-1\), and edges \(e_i=\{i,i+1\}\) with indices modulo \(n\).
Let \(D\subseteq\{0,1\}^n\) be nonempty. The finite dealer source \(R\)
has positive weights on its support, independent of the input \(x\in D\).
Every edge label \(W_i(x,R)\) takes values in an arbitrary finite
alphabet. For each vertex \(i\) the view is
\(V_i(x,R)=(W_{i-1}(x,R),W_i(x,R))\).
Perfect correctness means that any two equal view values, even from
different inputs and source states, identify the same \(x_i\).
Perfect privacy means that the full distributions of \(V_i(x,R)\) and
\(V_i(y,R)\) agree whenever \(x_i=y_i\).
There is no assumed distribution on \(D\); equivalently one may use any
full-support law on \(D\) and the corresponding conditional privacy.
There is no coalition guarantee. Minimize the support size, not Shannon
entropy, of \(R\). This is Marszalik §II, Eqs. (1)–(3).

Call \(i\) active if \(x_i\) is nonconstant on \(D\), and call \(e_i\)
a pair edge if \(x_i\oplus x_{i+1}\) is constant on \(D\).
An active vertex is covered if it touches a pair edge. The minimum
support is given by the first applicable case:
\[
\begin{array}{c|l}
1 & \text{every active vertex is covered},\\
2 & \text{there is a pair edge, or }\bigoplus_i x_i
       \text{ is constant on }D,\\
3 & \exists(\epsilon_i)\in\{-1,1\}^n:
                \sum_i\epsilon_i x_i\text{ is constant modulo }3\text{ on }D,\\
4 & \text{otherwise}.
\end{array}
\tag{1}
\]
No assumption of linear labels or uniform dealer weights is made in
the lower bounds.

## 2. Edge laws and at most two states

**Edge marginal.** The law of an edge label depends only on either of its
two endpoint bits, by projection of the private views. For a non-pair
edge it therefore has one common marginal law throughout \(D\).
To see this, form the bipartite graph on the occurring values of the two
endpoint bits, with an edge for each occurring pair. Each value node is
incident to an edge. With one active endpoint the support graph is a
star. If both are active, the only disconnected possibility is a perfect
matching, either equal or opposite bits, which is a pair edge. If
neither endpoint is active, the XOR is already constant. Otherwise,
connectivity propagates equality of the edge laws. This is also the
edge observation in Marszalik Appendix A-B.

With one source state, every label is a deterministic function of
each endpoint's bit. Any non-pair label is constant, so correctness
requires every active vertex be covered. Conversely each pair edge
can transmit its first endpoint bit, which is a public bijective function
of the other endpoint bit on \(D\); make all other edges constant.
Each active vertex can decode, and the full view is a function of the
local bit. This is the cycle restriction of Marszalik Proposition 1.

With two source states the weights may be made uniform without changing
the maps, as in Marszalik Lemma 9: for any two equally distributed
two-entry views, equal weights already give matching multisets. For
unequal positive weights the views either are common constants, or
their two unequal atom masses identify the same view value at each
state. Uniformizing preserves privacy and correctness.

If there is at least one pair edge, assign its deterministic label as
above, and use the same fair bit as a phase on every maximal path of
non-pair edges, starting that path with label \(R\) on its first edge.
Along the path, at each interior vertex \(i\), set its outgoing label
equal to the incoming label XOR \(x_i\). Every active uncovered vertex
has both incident edges on one such path and decodes its bit from their
difference, while the full pair is uniform over the correct XOR class.
An endpoint of a path is covered or inactive, and sees at most one
non-pair label, individually uniform, plus deterministic pair labels
which depend only on its own bit. No independence between paths is
required for the stated single-vertex privacy.

If there is no pair edge, every edge touches at least one active
vertex (two inactive endpoints would give a pair edge). At an active
vertex neither incident edge can have a constant label: both edge
marginal laws are globally fixed, so a constant on one side would make
the full view law fixed for both local bits, contrary to correctness.
With uniform two-state source, each edge consequently has two fixed
labels, each of mass \(1/2\). Relabel them as bits independently for
each edge. At every input the pair is uniform on two tuples of a
single XOR, hence the XOR is a deterministic function of the local bit
by privacy; at active vertices it takes opposite values on the two bits
by correctness. At inactive vertices it is a constant, which can also
be written \(x_i\oplus c_i\) for a fixed \(c_i\).
XOR the adjacent-label XORs around the cycle; the total is zero.
Thus \(\bigoplus_i x_i\) is constant. Conversely, fix a base word
\(x^0\in D\), set \(g_i=x_i\oplus x_i^0\), and put
\(W_i=R\oplus\bigoplus_{j=0}^i g_j\).
Then \(W_{n-1}=R\), each pair has XOR \(g_i\), and uniformity of \(R\)
gives the required view distribution. This proves the first two cases,
as a self-contained specialization of the author's one-bit theorem.

## 3. Three arbitrary positive source weights

We only need this step if no pair edge exists and the total binary
parity is nonconstant, so support at most two is impossible. At support
three the only weights that need be considered are \(\mathsf U=(1,1,1)/3\)
and \(\mathsf Q=(2,1,1)/4\), up to permutation. This is Marszalik
Proposition 12; the short proof follows.

When the three weights are distinct and none is \(1/2\), all nonempty
subset masses are distinct. Under equality of the views at two inputs,
a particular atom is then generated by exactly the same source-state
fiber at each, so fixing any source state gives a deterministic scheme.
When exactly two weights agree, outside \(\mathsf Q\) two subsets of
equal mass either both contain or both omit the uniquely weighted
state: otherwise that state's weight would be either equal to the other
weights or equal to their sum. Fix that unique state. In the remaining
case of distinct weights with a half-mass state \(h\), the only distinct
equal-mass subsets are \(\{h\}\) and the pair of light states.
If the joint view partition is that two-block partition, the two
half-mass view labels may exchange between equal-local-bit inputs.
Otherwise every fiber is fixed by its weight, with the possible
ambiguous block fixed by the other blocks of the partition.
Retain only \(h\) and one fixed light state, assigning them both
probability \(1/2\). In either case the resulting two-entry multiset
of views is unchanged by the input comparison. Correctness survives
restricting the support. This proves the reduction for arbitrary weights.

### 3.1. Uniform three-state case

An edge with the common marginal law has either one label, two labels
with masses \(2/3,1/3\), or three distinct equiprobable labels (a fine
edge). We show both edges at each active vertex must be fine. If one
is constant, correctness is impossible by the marginal argument of
§2. With two two-label edges, the two labels of mass \(2/3\) co-occur
with probability at least \(1/3\) at every input, so the bit classes
cannot have disjoint view supports. With one fine edge and one
two-label edge, every fine label is paired with precisely one of the
binary labels in each local bit class. If the view supports were
disjoint, for each fine label its partner would have to switch to the
other label. This would interchange the marginal masses \(2/3,1/3\),
which contradicts that the marginal is fixed. Thus both edges at
each active vertex are fine. Every edge touches an active vertex,
so this holds for all edges, even when some vertices are inactive.

Identify each edge's fixed labels with \(\{0,1,2\}\). For every local
bit value \(b\) occurring at vertex \(i\) there is a permutation
\(h_i^b\in S_3\) sending the left label to the right label within its
view support. This is well-defined because each edge separately
is a bijection of source states at any input, and the joint view law
is fixed within a bit class. At an active vertex, the two permutations
have disjoint graphs by correctness. Consequently
\(h_i^{1-b}(h_i^b)^{-1}\) is a derangement, hence one of the two
nonidentity elements of the alternating group \(A_3\).

For every fixed input, propagating the edge labels around the cycle
returns the same label for each of the three source draws. Thus
\(h_{n-1}^{x_{n-1}}\cdots h_0^{x_0}=1\) as a permutation identity.
Fix a reference word \(z\in D\); set
\(g_i=h_i^{z_i}\) and \(u_i=x_i\oplus z_i\in\{0,1\}\).
At active vertices write \(h_i^{x_i}=d_i^{u_i} g_i\) with
\(d_i=h_i^{1-z_i}(h_i^{z_i})^{-1}\) a nonidentity 3-cycle.
At inactive vertices \(u_i=0\), so choose any 3-cycle \(d_i\).
Expanding the product of the \(d_i^{u_i}g_i\), and using
\(g_{n-1}\cdots g_0=1\), gives the product of the \(d_i^{u_i}\)
conjugated by the reference suffixes \(g_{n-1}\cdots g_{i+1}\).
The conjugates are nonidentity elements of the common normal cyclic
group \(A_3\); they commute. Choosing a generator, the product
condition is \(\sum_i \eta_i u_i=0\pmod3\) with all \(\eta_i=\pm1\).
Since \(u_i=(1-2z_i)(x_i-z_i)\), this is a signed-sum relation
as in (1). No assumption about the parity of \(n\) is needed.

Conversely suppose that signed relation holds. Fix \(z\in D\) and
put \(t_i(x)=\epsilon_i(x_i-z_i)\pmod3\). Use a uniform independent
\(R\in\mathbb Z_3\), and give edge \(e_i\) the label
\(W_i(x,R)=R+\sum_{j=0}^{i}t_j(x)\) modulo \(3\).
The complete sum is zero and \(W_{n-1}=R\).
Every adjacent pair is uniform over the graph of translation by
\(t_i(x)\); its law depends only on \(x_i\), and its difference
determines \(x_i\) because the shifts for 0 and 1 are distinct.
This supplies a uniform three-state scheme.

### 3.2. Weights \(\mathsf Q=(1/2,1/4,1/4)\)

Write \(h\) for the half-mass state and call the other states light.
Each globally fixed marginal is one of: constant; unbalanced
binary with masses \((3/4,1/4)\); balanced binary with masses
\((1/2,1/2)\); fine with masses \((1/2,1/4,1/4)\).
At an active vertex a constant edge cannot occur. If one edge
has an atom of mass \(3/4\), choose a fixed atom of mass at least
\(1/2\) on the other (every one of the displayed types has one).
The chosen pair occurs with probability at least \(1/4\) at
every input, contradicting disjointness. Every edge touches an
active vertex, hence all edges are balanced or fine. Two fine
edges cannot meet at an active vertex, because each has its
label at state \(h\) uniquely determined by the same fixed
half-mass atom at every input. The heavy-state tuple would occur
in both bit classes.

Coarsen every fine edge to a bit, mapping its unique half-mass label
to 0 and its other labels to 1; keep each balanced edge as a bit.
For any input the two light states have the same bit on every
edge, and it is opposite to the bit at \(h\). So the adjacent
bit XOR is deterministic at each input, and by privacy it
depends only on the local secret.
At an active vertex with two balanced edges, equal XOR in the two
classes would give identical two-tuple supports (uniform on
that XOR class), impossible. At an active vertex with one
balanced and one fine edge, equal XOR would give the same
balanced bit at \(h\), since the fine bit there is always 0.
The original tuple consisting of that balanced label and the fixed
fine half-mass label would again occur for both local secrets.
Thus the adjacent XOR toggles with \(x_i\) at all active vertices.
As in §2 the cyclic sum of these XORs forces constant total parity.
That contradicts our residual case. The nonuniform three-state
weights therefore do not add any domain to case 3.

## 4. Four-state construction for the full cube

Use a uniform independent \(R=(r_1,r_2)\in\mathbb F_2^2\).
Let \(a=(1,0)\), \(b=(0,1)\). In the following all arithmetic is
over \(\mathbb F_2\):
\[
\begin{aligned}
t_0&=b x_0+a\sum_{j=2}^{n-1}x_j,  & t_1&=b x_1,\\
t_2&=a x_2+b(x_0+x_1), & t_i&=a x_i\quad(3\le i<n).
\end{aligned}
\tag{2}
\]
The sum of all \(t_i\) is zero. Put \(P_i=\sum_{j=0}^{i}t_j\)
and let the full edge vector \(Y_i=R+P_i\).
Transmit all of \(Y_i\) except that edge \(e_0\) sends only
its second bit, and edge \(e_2\) sends only its first bit.
These truncated edges are disjoint for all \(n\ge4\), including
the square. Since \(Y_{n-1}=R\), the cyclic difference
\(Y_{i-1}+Y_i=t_i\) holds for every vertex.

At vertices 0 and 1 the two second bits are visible and their
XOR equals \(x_i\); at vertices 2 and 3 the analogous statement
holds for the first bits. Each of these vertices sees one complete
uniform vector and one bit equal to the corresponding component of
that vector XOR its own secret. The joint law therefore depends only
on that secret. Every remaining vertex sees two full vectors,
one uniform and the other equal to it plus \(a x_i\).
Again this gives both correctness and perfect privacy. Restrict
the construction to any nonempty \(D\). Together with §§2–3 this
proves (1). No step computes or bounds the minimum Shannon
entropy. The triangle \(C_3\) is outside the theorem: the two
disjoint truncated edges need not exist there and its complete
binary classification is known separately.
