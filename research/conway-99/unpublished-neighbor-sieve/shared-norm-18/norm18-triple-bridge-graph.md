# At most one edge in each signed difference of a shared norm-18 triple

Assume N16=N20=0, with unrestricted affine shells and rank. Any true triple at a positive root o and its four negative neighbors Q is [all-seven](norm18-triple-one-nine.md). Let L_i be the two pair centers omitted by i, P_i the four private positive singleton leaves, and N_i the five private negatives. These are respectively groups of sizes two, four and five; all groups are mutually disjoint and disjoint from o,Q. For i≠j put r_ij=t_i−t_j; it has signed-unit norm22 with positive sign P_i∪L_j∪N_j and negative sign P_j∪L_i∪N_i. Each sign has the same number e_ij of internal edges. We prove **e_ij∈{0,1}**, and that e_ij counts exactly the true positive-leaf edges between the four-sets P_i and P_j. At least one such bridge exists by the [independent-sign triple obstruction](norm18-triple-exterior.md).

First, each center in L_i already sees its two negative parents of t_i. Its required positive i-neighbors can only be the private leaves: o is not a neighbor and all pair centers are mutually nonadjacent. It cannot see three such leaves. Each has a triple of neighbors among the five N_i, and any two sharing the center must have private-negative intersection ≤1. As triples on a five-set their complements would be disjoint two-sets. Three such two-sets cannot fit in five sites. Thus every omitted center has **exactly two i-leaf neighbors, no i-private negative neighbor**. For p∈P_i put l_i(p)=|N(p)∩L_i|. Their total is four. In t_j, balance at p states
```
|N(p)∩P_j| = 1−l_i(p)+|N(p)∩N_j|.
```
Indeed p sees one negative parent, and the only other j-positives it can meet are in P_j or L_i. Since L_j misses N_j, the sole possible kind of positive edge of r_ij joins P_i to N_j. Summing the last equation yields
```
e_ij=E(P_i,N_j)=E(P_j,N_i)=E(P_i,P_j).
```
Here E(X,Y) counts actual unordered graph edges across two disjoint sets Y,X.

Recall the [norm-22 height budget](norm18-u230-edge-pressure.md#charging-all-seven-triples-through-edged-differences): for a zero site x let H(x) be its common number of neighbors of either sign of r. The sum across the 77 zero sites of (H−1)(H−2)/2 is 11−5e−J_P−J_N, where J is the sum of binomial(internal sign degree,2). Since o has height zero, this also gives the usual e≤2. If e=2, the budget is at most one and is already spent at o, so every other zero site has H=1 or 2.

Fix i,j and denote the third field by k. For the four k-positive leaves p, which are zeros of r_ij, H(p)=d_Pi(p)+d_Nj(p): the additional r-positive centers L_j cannot meet p since they too are k-positive. Their combined height is e_ik+e_jk. On a private k-negative n, a zero of t_j, its t_j-balance gives d_Nj(n)=d_Pj(n)+d_Li(n); it misses o,Q and L_k. Consequently
```
Σ_(p∈P_k) H(p) = e_ik+e_jk,
Σ_(n∈N_k) H(n) = e_ik+e_jk+8.
```
For the second equation, H(n)=d_Pi(n)+d_Lj(n)+d_Nj(n), and the four centers of L_i∪L_j are used in t_k, each seeing two private k-negatives besides its parents. If e_ij=2 then all nine sites have heights one or two: the first sum would be at least 4 and the second at most 10. These bounds on two integers differing by eight are incompatible. Thus no pair in this configuration has e_ij=2.

In particular the extra-debit variables K1,K2,H2 in the [weighted triple bound](norm18-triple-one-nine.md#a-single-edged-pair-cannot-use-a-two-edge-positive-marking-cheaply) need not be charged anything for triple incidence: keeping the same definitions, the e=2 terms contribute zero instead of (5/2)H2 in the first displayed bound there. The event-level description is simpler than this small coefficient improvement: the actual edges between P_i and P_j are either absent or a **single edge**, and each r_ij with such a bridge is a one-edge-per-sign field even if two-edge norm-22 fields exist elsewhere. There is no claim of a triple-free graph.

Here is the entire list of per-group choices before checking the 38-site layout. A balanced group has l_i=1 on all four leaves. Otherwise the two two-site center neighbor-sets intersect in one leaf B; they cannot coincide since two leaves already have a common site in N_i. A unique leaf E then has l_i(E)=0 and the other two have l_i=1. In that group B needs a neighbor in every N_j by the leaf balance, so both incidents e_ij equal 1. The entire j-bridge uses E as its positive-leaf endpoint, whereas the unique j-private negative contact is at B. In a balanced group incident to a bridge, its single positive-leaf endpoint is exactly the leaf carrying the private-negative contact into N_j. Thus among the three groups the nonempty simple bridge graph has one edge, a two-edge path, or a triangle; unbalanced groups may occur only at its degree-two vertices.
