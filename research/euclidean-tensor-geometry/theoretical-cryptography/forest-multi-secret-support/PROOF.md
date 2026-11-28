# Exact graph-CMSS source support on forests

## 1. Model

Let G=(V,E) be a finite simple forest and let D be a nonempty subset of {0,1}^V. A scheme has a finite source R with positive probabilities independent of x in D, and an edge label W_e(x,R) in an arbitrary finite alphabet.

Vertex v sees the tuple of all incident labels. Correctness means that equal view values, even at different inputs and source states, imply equal x_v. Perfect privacy means that inputs with equal x_v give the same distribution of the complete view at v.

A vertex is active if x_v is nonconstant on D. An edge uv is a pair edge if x_u XOR x_v is constant on D. An active vertex is pair-covered if it is incident to a pair edge. A terminal vertex has degree at most one.

Let m_G(D) be the minimum finite source support, with value infinity when no scheme exists.

## 2. The theorem

For every finite forest G and every nonempty binary D,

1. m_G(D)=1 if every active vertex is pair-covered;
2. m_G(D)=2 if every active terminal vertex is pair-covered but some active vertex is not pair-covered;
3. m_G(D)=infinity if some active terminal vertex is not pair-covered.

No linearity, uniform-weight, or bounded-alphabet assumption is made.

## 3. The terminal obstruction works for arbitrary source support

An isolated active vertex has the empty view at every input and source state, immediately contradicting correctness.

Now let v be an active leaf, let e=vw be its unique edge, and suppose e is not a pair edge. Projecting privacy of the complete view shows that the law of W_e depends on an input only through x_v. Projection at w shows that it also depends only through x_w.

Form the bipartite support graph whose left nodes are the occurring values of x_v, whose right nodes are the occurring values of x_w, and whose edges are the occurring endpoint pairs. It has no isolated nodes. It is connected:

- if w is inactive, it is a star;
- if w is active, a disconnected binary bipartite graph with no isolated nodes is one of the two perfect matchings, which would make x_v XOR x_w constant and e a pair edge.

The two endpoint descriptions of the edge law therefore propagate equality along this connected graph. Hence W_e has one common distribution on every input in D.

Because v is active, choose x,y in D with x_v different from y_v. Correctness at the leaf says that the supports of W_e(x,R) and W_e(y,R) are disjoint: a common label would be an equal complete leaf view for different local bits. But the two distributions are equal and nonempty. This is impossible. Thus an active terminal vertex must be pair-covered in every finite-support scheme.

## 4. Zero randomness

If every active vertex is pair-covered, orient each pair edge arbitrarily and label it by the bit at its tail. The bit at the head is that label XOR the public pair constant. Label every non-pair edge by a constant. Every active vertex recovers from one incident pair edge, and its entire deterministic view is a function of its own bit. This is correct and private.

Conversely, the standard deterministic argument says that every active vertex must see a nonconstant incident label. Privacy at both endpoints makes that label a function of each endpoint bit, so for binary bits it forces their XOR to be constant. Hence every active vertex is pair-covered. This is Marszalik's Proposition 1.

## 5. One fair bit whenever all active terminals are covered

Assume every active terminal vertex is pair-covered. Let H contain all non-pair edges. Since G is a forest, H is a forest.

Choose an incidence sign q_v(e) in {0,1} for every end v of every edge e of H. At each active vertex v which is not pair-covered, all incident edges are non-pair edges. The terminal assumption gives degree at least two, so choose its incidence signs to include both 0 and 1. At other incidences choose signs arbitrarily.

Fix x^0 in D. For e=uv in H put

    g_e(x)=q_u(e)(x_u XOR x^0_u) XOR q_v(e)(x_v XOR x^0_v).

Root each component of H. Since H is a forest, define h_v(x) as the XOR of the g_e(x) along the unique root-to-v path. Then h_u(x) XOR h_v(x)=g_e(x) on every e=uv.

Take one uniform bit R. On e=uv in H define

    W_e(x,R)=R XOR h_u(x) XOR q_u(e)(x_u XOR x^0_u).

The path identity gives the equal expression from endpoint v, so the shared edge label is well-defined. On a pair edge use the deterministic label from Section 4.

At vertex v all H-labels have the form

    U_v XOR q_v(e)(x_v XOR x^0_v),  where U_v=R XOR h_v(x).

For fixed x, U_v is uniform. Thus the complete view distribution depends only on x_v; incident pair labels are also deterministic functions of x_v. Privacy holds. A pair-covered active vertex recovers deterministically. Every other active vertex sees both incidence signs, so XORing two corresponding H-labels reveals x_v XOR x^0_v. Correctness holds.

This proves m_G(D) at most 2. If some active vertex is not pair-covered, Section 4 excludes support 1, so the minimum is exactly 2.

Together with Section 3, the three cases are exhaustive.

## 6. Scope and attribution

Marszalik, arXiv:2610.10002 / ePrint 2026/2395, proves the arbitrary-graph deterministic criterion and a signed-subgraph characterization of support at most two. On a forest the cycle-flatness condition is automatic. The additional point here is that the only obstruction left at a terminal vertex is not merely an obstruction to two states: the connected endpoint-support argument excludes every finite source. Combining it with the explicit forest construction gives the full values 1, 2, and infinity.

The result does not address graphs with cycles beyond the neighboring cycle classification, Shannon entropy, approximate privacy, coalition privacy, or nonbinary secrets.
