# Single-point Hoffman overlaps, four-color completion, and the 42-site bisection

These are graph statements for an arbitrary SRG(99,14,1,2). Fix a vertex p and let D=Γ₂(p). There are 84 sites in D and its induced graph is 12-regular: each site has exactly two neighbors in Γ(p). Every independent 22-set C meets the Hoffman bound. Each outsider has exactly four neighbors in C, by equality in that bound (equivalently A 1_C=4(1−1_C)). If p∈C, the 21-set C−{p} is independent in D, and every site of D outside it has four neighbors there.

## Exactly when two such sets complete

Suppose C₁∩C₂={p}. Delete their disjoint 21-sets X₁,X₂ from D, leaving R of size 42. G[R] is 4-regular; it is connected, since a disjoint union of two or more 4-regular components would have second-largest eigenvalue 4, exceeding the 3 allowed by principal interlacing in G. The following are equivalent:

1. There exists a third independent 22-set C₃ with C₃∩C₁=C₃∩C₂={p}.
2. R is bipartite.
3. The two 21-sets at p complete to a partition of D into four independent 21-sets.

For (1) an independent 21-set in a 4-regular graph of order 42 sends its full 84 edges to the other 21 sites, leaving no edges there. Conversely a connected regular bipartite graph has its two shores of equal size. Adjoining p to either shore gives a 22-set. Connectivity makes the completion unique, up to exchanging the two new cocliques. Thus in the graph on maximum cocliques through p, where adjacency means intersection only at p, every triangle is contained in a unique K₄, and every edge in at most one K₄.

Here is the exact seven-class implication. Use c_i=−1_Ci and d_p=3e_p−Ae_p. The fourth field is
```
c₄=−c₁−c₂−c₃−d_p−1.
```
The pre-fold charge is −7, so the subtraction of 1 folds to charge +2 and does not affect the centered vector. Directly, its values on p, Γ(p), the three old 21-sets, and the fourth new 21-set are respectively −1,0,0,−1. The site shift d_p has trivial seven-component since 3u_p is in the original lattice. Therefore its seven-class is β₄=−(β₁+β₂+β₃). Each original coclique class is isotropic: the squared norm of the centered field is 154/9. The centered inner product for a pair is |C_i∩C_j|−44/9, giving −35/9 at overlap one. Thus in this configuration the β_i are pairwise orthogonal and together span a totally isotropic subspace, contained in some maximal H. The fourth class also belongs to H. No assumption is made that the individual classes vanish.

On the two-type face at ranks 40/42 every maximal H has at most three eligible cocliques by [the short-population theorem](two-type-short-counts.md). Therefore **every actual single-point overlap pair on this face has nonbipartite R**: any four-completion would be wholly eligible for at least one H, even if two of the original classes are zero. This excludes a configuration, not the entire M=3 case.

## A graph-theoretic size/density cut on either shore

More generally take any nonunit charge-four norm-46 labeling b with a −2 at p. It has b=−2e_p−1_T, with T of size 42, by its charge and squared cost. The eigenvalue equation A b=−4b−8·1 shows that T⊂D and T induces a 4-regular graph, its complement T'=D−T also 4-regular (sites in T' see 8 of T). Translation and folding give the partner b'=−b−d_p−1=−2e_p−1_T'. Both seven-classes are opposite; consequently both are eligible for the same H, if either is. When C₁,C₂ meet only at p, b=c₁+c₂ corresponds to their two 21-sets, and b' corresponds to the remainder R. Thus the following cut applies with no maximum coclique assumed, to either shore of any marked bisection.

For F⊂T let n=|F| and e=e(F). For 5≤n≤9 the graph marking
```
h = b + Σ_(i∈F) d_i + 1
```
has folded charge n−5 and squared evaluation cost 57+n+2n²−14e. At a vertex i∈F it is 3−deg_F(i); at any other site it is at most 1. Indeed d_i²=23, d_i·d_j=2−7A_ij for i≠j, and b·d_i=7b_i+8=1 on F, giving the displayed norm after the charge fold. The seven-class of h is the class of b. The following consequences are independent of rank:

* A six-set spans at most eight edges (nine edges would give a charge-one labeling of norm nine, below |Σh|=11). An eight-edge six-set has minimum degree at least two: on five sites at most six edges occur, since a degree-four center has its four neighbors inducing a matching, and if maximum degree is three a seven-edge five-set has a vertex of degree at most two whose removal leaves at least five edges on four vertices, impossible by λ=1. In this argument for maximum degree three, seven edges imply degree sequence (3,3,3,3,2), as required. A labeling from an eight-edge six-set has t=23 and no entry >1. It cannot have an entry ≤−2 either: translation by d_i gives charge two of cost at most 22; equality requires the new i-entry +1, impossible at charge two and norm 22. Thus each such set gives a **unit** (1,23) field in the same original seven-class as b. Two distinct six-sets of eight edges on a fixed side cannot give the same field. Otherwise the signed difference of their indicators lies in the 3-eigenspace, since their added site marks agree. Each vertex in the positive support must then have at least three positive neighbors. With at most six positive sites, the four- and five-site edge caps rule out sizes at most five, and six would require at least nine edges on this same shore, already excluded above. Consequently every individual bisection shore has at most as many eight-edge six-sets as the number of (1,23) unit fields in its actual seven-class.
* A seven-set spans at most nine edges. Eleven or more give charge two of norm ≤8. Ten give norm 22, hence h would have to be nonpositive at every site. But some site of the seven-set has internal degree at most two, giving h_i≥1.
* An eight-set spans at most eleven edges and a nine-set at most thirteen, directly from the absolute charge minima at 12 and 14 edges respectively.

In an extension on the two-type face with M=3, the [exact tuples](two-type-short-counts.md) have S=0,3 or 6 unit charge-one norm-23 fields. In each eligible overlap-one remainder the number of eight-edge six-sets is at most S, and in particular is zero on the S=0 slice. These estimates are per fixed shore: different six-sets on different shores have not been proved to give different field images.

Finally there is a literal small-cycle count in a single-point remainder. At p, label each site of D by its unique two neighbors in Γ(p). Edges of D whose triangle cap lies in Γ(p) are selected by seven pairs of neighbor arms at each root neighbor: after the edge from p to its mate, the other twelve D sites in that neighborhood are matched. Let l be the number of such matched X₁–X₂ edges, summed over the fourteen root neighbors. Exactly 84 edges join X₁ to X₂. A noncap edge between them has its third triangle site in R. Write a,b,c,d for triangles of D contained in R, with one X₁ and two R, with one X₂ and two R, and with one of each X₁,X₂,R. Each site of D belongs to precisely five triangles wholly in D (of its seven incident triangles the two others contain its two nonadjacent Γ(p) neighbors). Thus a+b+c+d=140 and b+d=c+d=105. Since d=84−l, this gives a=14−l, in particular l≤14. Nonbipartite need not mean a>0: an odd cycle of greater length is possible. No rank exclusion follows.
