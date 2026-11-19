# Which pairs stabilize earlier? Two decorated leaf blocks

Use the notation of AFFINE.md with M=4. Write A_j for the eventual slope of D(n,n+j−1). The six proposed secondary representatives in CLÚV §5.2 all have A_j=0 for all j. The remaining five representatives have nonzero first slopes as in the table below, hence stabilize at the tertiary but not the secondary level. Inverse and reverse complement preserve inversions, size, and 1324; their orbits, along with 1234 and 1324 itself, cover all 24 patterns. No assertion of inversion monotonicity follows.

## 1. Canonical form for every contributing core

Only cores with two expandable regular-leaf families contribute to a slope, by the last paragraph of AFFINE.md. Denote the two increasing leaf blocks A,B from left to right, of lengths at least four; their unique parents are U,V respectively. Inversion means incomparability in the coordinatewise order. U is strictly southwest of B: it is comparable to each B, and northeast of even one B would imply it was northeast of A, impossible. Likewise V is northeast of A. Every ordinary vertex (apart from the two parents and the two leaf blocks) is comparable to all these leaves, and by consecutiveness must lie before A, between A and B, or after B in **both** orders. Call the three parts X,W,Y. There are no inversions between distinct ordinary parts.

Each point of X must invert U: if comparable it is southwest of U (the opposite would imply U<A), and then the U–A inversion is bracketed by this point and a B leaf. Such a point has no neighbor outside X other than U, since X<A<V. If it has no inversion neighbor in X, it would be a leaf of U, contrary to maximality of A. Thus X has no singleton component internally. It avoids 132, since a B leaf follows any such occurrence. A nonempty decomposable 132-avoider must have a final singleton component (any earlier point and any inversion in the final component would give 132). Hence X is empty or an indecomposable 132-avoider of length at least two. Similarly Y is empty or an indecomposable 213-avoider of length at least two, and each of its points inverts V only outside Y. The part W is an increasing block: an inversion within it is bracketed by A,B. Every point of W must invert both U and V, since it has no other possible neighbor and is neither isolated nor a regular leaf. Thus arbitrary endpoint decorations X,Y genuinely matter, unlike a bare two-star model.

Conversely, take an increasing chain of blocks A,W,B, with W of length t≥0, and insert U,V in each axis so that their inverted chain vertices are respectively exactly A∪W and W∪B. Write e=1 if U,V are inverted, 0 otherwise. Insert a permitted indecomposable decoration X just before the first A in both orders and Y just after the last B in both orders. (When a parent occupies an immediately adjacent slot it remains outside the inserted block.) This gives exactly the two-family structures just described before pattern filtering. All newly added points have their required parent and have an internal neighbor. Both parents keep at least four leaf neighbors, the middle vertices have degree two, and the two leaf families are unchanged. Every representation is unique by reading the families, parents and three ordinary parts from the inversion diagram. The constructed graph has two components exactly when t=e=0; otherwise it has one. If two components, U,X,A form the first and V,B,Y the second.

Neither an initial nor a final singleton gap can be nonempty in a 1324-avoider of this form: U–A is followed by B, and V–B is preceded by A. Only in the two-component case can there be any singleton gap, of length g between the components. Cap it at 4 as before, taking g=0 on a connected core. Let f be 1 if g=4 and 0 otherwise. Write u=inv(X), v=inv(Y), and L=|A|+|B|. The core has h=L+2+t+|X|+|Y| and k=L+2t+e+|X|+|Y|+u+v. By the signed formula of AFFINE.md its slope contribution is +1 at j=t+e+u+v−g, and −1 at the preceding j if f=0. This is the eventual slope of m+1, not a point count at finite n.

## 2. An explicitly finite cancellation independent of endpoint lengths

For a fixed X,Y and their two subpattern profiles, drop the common power y^(u+v). The resulting Laurent series S(y) of slope contributions is determined entirely by the finite diagram menu below. To find its numerator (1−y)S(y), take |A|=|B|=4; hereditary feasibility on any expansion is then identical. Use t=0,1,2,3,4. For t≥1 the same two parent insertions are available as for four middle points up to increasing inflation of the middle block: parents cannot interleave the W points in either axis, since each parent inverts all W. The tests for length-four patterns stabilize at four. Thus a surviving menu element contributes
* y^(t+e−g) times (1−y^(-1)) if f=0, or y^(t+e−g) if f=1;
* multiply this by (1−y) for t=0,1,2,3, and by 1 for t=4 (the latter covers the whole geometric tail).

The full sum over endpoint pairs is coefficientwise well-defined: u,v are nonnegative, every nonempty endpoint has length at most 1 plus its inversion count by connectivity, and g≤4. This permits coefficientwise linear combination of the fixed-endpoint numerators.

For reproducibility here is the complete finite test behind the table, also implemented literally by the standalone Python verifier. Use two initial labeled representatives per leaf block, insert both parents in every possible slot in both axis orders, and filter by the required chain incidences. Inflate the first representative of each leaf block to three copies, giving length four total. (Nothing can split either block in a valid diagram.) Include g=0,...,4 exactly in the two-component case, otherwise g=0. Put distinguished placeholders for X,Y at the specified positions, even when their profiles will disallow any use. To test a pattern z (1324 or p), enumerate disjoint consecutive position intervals I,J of z in that order, either possibly empty, each with consecutive values. These are the portions of an occurrence inside X and Y. Collapse each nonempty interval to one distinguished point with its relative rank, and test whether the shorter colored permutation occurs in the skeleton with the prescribed placeholders exactly and all other points ordinary. The criterion is necessary because X and Y are intervals in both orders, and sufficient by independent choice of witnesses in their interiors. The internal patterns std(I),std(J) must be present in the corresponding profiles (empty is always present).

For each p let P consist of the internal interval patterns used by these tests for z=p or 1324, together with the empty pattern, 1,21,132,213 and p. For each side enumerate the empty-endpoint profile, and all subsets of P which contain empty,1,21, omit p,1324 and the local forbidden triple (132 on the left, 213 on the right), and contain every subpattern of every retained member that belongs to P. This deliberately includes some nonrealizable formal masks, which only strengthens the cancellations. An endpoint containing p cannot contribute. For each pair of masks sum the finite numerator above over diagrams that pass both avoidance filters.

The table gives (number of left masks, number of right masks); all possible values for the numerator divided by (1−y), i.e. S itself; and the value for the two empty endpoints. Each zero or monomial here is a Laurent-polynomial identity, not an initial-coefficient check. The full numerators and their multiplicities are checked by integer arithmetic in verify_profiles.py.

|p|mask counts|possible S(y)|empty/empty|
|---|---|---|---|
|1324|3,3|0|0|
|1243|4,4|0|0|
|1342|6,6|0|0|
|1432|5,5|0|0|
|2341|6,6|0|0|
|3421|6,6|0|0|
|4321|5,5|0|0|
|2143|3,3|0, −2|−2|
|2413|3,3|3|3|
|2431|3,3|y|y|
|3412|4,4|2y|2y|
|4231|10,10|0, y², 2y²|2y²|
|1234|6,6|0|0|

For the zero rows, summing all endpoint decorations yields zero on every diagonal. For each of the other five rows, every nonempty decoration has u+v≥1, hence cannot affect the first displayed nonzero coefficient arising from empty endpoints, since no mask has a lower-degree term. The five (index j, value A_j) are (0,−2), (0,3), (1,1), (1,2), (2,2), in row order. The sign in the 2143 example is a moving diagonal slope, not a decrease assertion at a fixed inversion number from this argument alone; however a strictly negative slope does eventually make D itself negative on that moving diagonal.
