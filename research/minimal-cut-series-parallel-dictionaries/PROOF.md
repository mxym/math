# Minimal vertex cuts in finite two-terminal series/parallel dictionaries

All graphs below are finite, simple and undirected. A global cut is inclusion-minimal among vertex sets whose deletion leaves at least two components. A minimal terminal separator avoids the two designated terminals and is inclusion-minimal among sets separating them. It is **clean** when precisely two components remain.

Let F be any finite list of finite connected simple two-terminal graphs with distinct roots, and include the bare edge as an allowed atom. Series (A∘B) identifies the sink of A with the source of B, keeping the two external roots. Parallel (A∥B) identifies corresponding pairs of roots. The two copies are disjoint prior to the specified root identifications; in particular they have no common internal vertices. Duplicate edges in the output are collapsed. For a two-terminal graph X, put p_X=|V(X)|−2 and write h_X for the count of clean minimal separators of the designated terminals, c_X for all global minimal vertex cuts, and X⁺=X plus the terminal edge (if absent). Put
  ρ=max({3^(1/3)} ∪ {h_B^(1/p_B) : B∈F, p_B>0}).
Let M_n be the maximum c_X over assembled cells X with n vertices, and H_n the analogous maximum h_X. Then limsup M_n^(1/n) is **exactly ρ**; in fact [the padding construction](ALL-ORDERS.md) gives limits for M_n^(1/n) and H_n^(1/n). The same exponential bound/achievability holds for the designated h_X. In particular ρ<β, where β is the unrestricted asymptotic global-cut constant, by [the preceding finite parallel-template nonattainment theorem](../minimal-cut-parallel-nonattainment/PROOF.md) applied also to the three-interior path. Single-edge atoms give rate exactly 3^(1/3) in the two-terminal series-parallel class. We do not equate this class with all bounded-treewidth classes.

## Rooted arithmetic

For A∥B with A,B connected, h=h_A h_B exactly. This holds even if a factor has adjacent terminals. For A∘B, h≤1+h_A+h_B: separating the exterior roots either deletes their unique join (then the singleton suffices), or separates designated roots within at least one factor so inclusion minimality confines the cut to that factor. If there were an extra component disjoint from the separated factor's roots, the other factor cannot reconnect it, so a clean output requires a clean factor. The internal orders are p+q and p+q+1 respectively.

These recurrences show h_X≤ρ^(p_X) by induction. For clarity, at an arbitrary connected base with p=0,1,2 the rooted counts are bounded respectively by 0,1,2 (nonempty separators form an antichain on the p points). With p≤q, η=3^(1/3) and ρ≥η, the needed series bound is:
* p=0: for q=0,1,2, use 1,2,3≤ρ,ρ²,ρ³; for q≥3, (ρ−1)ρ^q≥3(η−1)>1.
* p=q=1: 3≤ρ³.
* p=1, q≥2: (ρ²−1)ρ^q ≥ (η²−1)η²>2, so 2+ρ^q≤ρ^(q+2).
* p,q≥2: ρ^p+ρ^q+1 ≤2ρ^q+1≤ρ^(p+q+1) since ρ^(p+1)≥3.
These hold even when an atom has h=0.

## Bounding unrooted cuts under compositions

Let d_X=max(c_X,c_{X⁺}). For a parallel composition, including when the output is capped,
   d_{A∥B} ≤ d_A+d_B+h_A h_B+4.                         (P)
To prove this, first ignore the cap. If both roots survive in different components, a further component lives in one factor and has no neighbor among internal vertices of the other; every global cut vertex must touch every component, so no cut vertices could belong to the other factor. That other factor would therefore connect the roots. Thus in this case the cut is clean and is counted by the product. This case is impossible for a capped output.

Otherwise, cuts contained entirely in the roots give at most four choices. For a cut meeting the interiors, choose a component D disjoint from the surviving roots, which exists also when neither root survives. It belongs to the interior of just one factor. Because every cut vertex touches D, the cut S is contained in the vertices of that factor, say A. Then S is a global minimal cut of A⁺. Details: since S meets the interior of A, no component in the full deleted graph can contain only interior vertices of B (it could not be adjacent to that cut vertex). Thus every component has a surviving vertex in A. Adding the terminal edge in A⁺ cannot join separate components since surviving roots, if both present, are together. Hence A⁺−S is disconnected. Whenever a proper subset S'⊊S is deleted, the full graph is connected by global minimality. Any path between surviving vertices of A in the full graph restricts to a walk in A⁺ by short-cutting excursions through B between the terminals. So A⁺−S' is connected (it contains surviving vertices). This proves the claim and its version with the cap already present. The symmetric case is counted by d_B. This proves (P).

For a series composition without the cap,
   c_{A∘B} ≤ c_A+c_B+1.                                  (S)
The join w alone is a cut vertex (both exterior roots are distinct). Any global minimal cut containing w is its singleton. A cut avoiding w must disconnect one of the two factors because they intersect at w; it is therefore confined to that factor by minimality. It is a global minimal cut there.

For a capped series composition, rearrange X=(A∘B)⁺, with A(s,w), B(w,t). The same underlying graph is A in parallel with C formed by B in series with the single edge t−s, between its terminals w,s. Here h_C≤h_B+1. Underlying C has c_C≤c_B+1 by (S), while C⁺ is B in parallel (between w,t) with the two-edge path via s. The two-edge path Y itself has h_Y=1 and d_Y=1. By (P),
   d_C ≤ d_B+h_B+5.
Then (P) applied to A∥C gives
   d_{A∘B} ≤ d_A+d_B+h_A h_B+h_A+h_B+9.                 (S+)
This dominates (S). Thus, at each binary composition, departure from the sum of the children's d-values is ≤12 ρ^(p_X). A capped unary node X↦X⁺ never increases d and has h=0.

When all atoms have positive internal order, there are at most p_X leaves, hence O(p_X) nodes. Bare-edge leaves can be handled as follows: recursively replace any zero-order subtree by a single edge (the only possibility). Replace a parallel node with a zero-order child by a unary cap of its other child; no d error is charged there. Collapse consecutive caps since adding an existing edge changes nothing. Every series node contributes one to the final internal order, so there are ≤p_X series nodes. The positive-order leaves consume ≥1 distinct internal vertices each. Every surviving zero-order leaf is either the entire expression or a child of a series node, hence at most 2p_X+1 such leaves. After suppressing unary caps the binary tree has O(p_X+1) nodes; caps incur no error. All descendant orders are ≤p_X. Summing (P),(S+) on this reduced tree, with bounded leaf d-values, gives
    c_X ≤ d_X ≤ C_F (p_X+1)ρ^(p_X).
A clean terminal separator is globally minimal: each cut vertex touches both surviving components, so restoring any nonempty subset reconnects the graph. For the lower bound, any positive-order atom can be run in parallel with itself (h_B^r clean cuts); the 3-interior path built from four bare edges gives rate 3^(1/3). Taking the largest establishes the exact limsup. If the edge is not permitted initially, the same expression gives an upper bound, but equality at 3^(1/3) need not be attainable.

The bare edge also allows padding to every sufficiently large order; see [the full-limit statement](ALL-ORDERS.md). The elementary rooted sum/product rules are not claimed as new. See [prior results and the planar specialization](SOURCES.md). This does not determine the unrestricted constant.
