# The contacts at a triangle already distinguish its wing sites

In a hypothetical Conway graph, fix the three vertices of any triangle individually and retain the entire graph except for the edges among its 60 exterior vertices. The automorphism group of this partial information cannot act transitively on the twelve sites of any wing. The obstruction therefore applies even to contact designs whose symmetries are allowed to disappear in the full graph.

## Equivariant contact bijections

Transport labels between wings $P,Q,R$ along the first two cross matchings, so these are identities and the third matching from $P$ to $R$ is a permutation $t$. At a transitive action on $P$, the group acts by the same permutations on each wing. This action on twelve labels is faithful after quotienting by its kernel. An element fixing all wing labels fixes all exterior vertices, since the exterior vertices are uniquely identified by their nonmate pairs in any one wing. Thus the action is among the 301 transitive permutation groups of degree twelve in the [GAP TransGrp library](https://docs.gap-system.org/pkg/transgrp/doc/manual.pdf).

For a fixed permutation group, each of the mate matchings $a,b,c$ is a fixed-point-free involution commuting with its generators. The cross matching $t$ also commutes with them. Enumerate commuting permutations by prescribing the image of label zero and propagating along generator edges, rejecting inconsistent images.

For two wings let $d$ be the direct cross matching and $e$ the map along the alternative two-edge route through the third wing. For first-wing label zero and second-wing label $j$, the required number of exterior common neighbors starts at two. Subtract one for each occurrence of $j$ in the list
$$d(0),\quad d(a(0)),\quad b(d(0)),\quad e(0).$$
The first entry is the adjacency adjustment. The other three list all possible shell common neighbors with multiplicity, as three distinct potential sites in the first, second and third wings. A negative capacity rejects the chart. Transitivity and equivariance make the twelve capacities at label zero sufficient for testing all ordered cross-wing pairs.

Every exterior contact array is specified by consistent bijections of the 60 nonmate pairs in its three wings. For two wings, enumerate equivariant bijections from source pair orbits to target pair orbits of equal size. An orbit bijection is fixed by one basepoint image and is tested by the same propagation. For each image add the contributions to the twelve capacities from the source pairs containing zero. Enumerate unused target orbits until all source orbits have images and all capacities are exhausted. Finally require that a map from $P$ to $Q$ composed with one from $Q$ to $R$ is among the admissible maps from $P$ directly to $R$. For the first two wing pairs $(d,e)=(1,t)$, and for the last $(d,e)=(t,1)$.

## Integer replay

Of the 301 groups, 182 allow a mate matching. The resulting list of $(a,b,c,t)$ contains 7,574 charts, counting named actions and charts without isomorphism reductions. Only 135 charts admit at least one candidate pair map for each of the three wing pairs. None admits three maps that compose. This excludes transitive action on the partial design. It leaves open the contact arrays with intransitive stabilizers.

Run the [standard-library checker](contact_transitivity.py) with the path to the [pinned group-generator file](https://github.com/hulpke/transgrp/blob/978c26c0e158387ea6550412cb38c9eb8b820cea/data/trans12.grp) as its argument. It checks the file's SHA-256, parses every generator record, and enumerates the equivariant maps. As a separate check for the first five groups, normalizing their regular actions by left multiplication and enumerating pair-orbit translations produced 4,788 charts and the same zero compatible triples.
