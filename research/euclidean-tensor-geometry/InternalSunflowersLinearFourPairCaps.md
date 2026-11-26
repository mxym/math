# Linear hypergraphs and the gap-free all-pair-capped rank-four regime

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.


## Linear nonempty extraction lemma

For fixed k≥2, let H be a finite simple k-partite k-uniform hypergraph in which any two distinct edges meet in at most one vertex. Then H has a subfamily F of size Ω_k(|H|m^(−k+1)) in which every realized nonempty intersection is internally witnessed by an m-petal sunflower.

This proof uses the weighted bipartite graph nonempty lemma already proved for rank three (Appendix A of the [full rank-three theorem](InternalSunflowersTriplesUnrestricted.md)): every weighted simple bipartite graph has a subgraph retaining Ω(1/m) total weight whose nonzero degrees are one or at least m. Only the unit-weight case is needed here.

In a linear hypergraph, a vertex link is automatically a matching, so it is enough to have each positive degree one or at least m. More precisely, at stage j in a host E_j, let j designated sides have cap at most B_j m^j for a constant B_j depending only on k and j. Initially j=0 and no cap. At j<k−2, peel any remaining side vertex of current positive degree below C_j m^{j+1}. Charge every deleted edge to the deleting vertex's side; the original capped sides are not considered. If the remaining core has at least half the mass, use the core extraction next. If not, the largest owner piece has at least E_j/(2k) edges, with old caps still in force and a new designated cap ≤C_j m^{j+1}. Set B_{j+1}=max(B_j,C_j) and continue. Thus a bounded number of steps loses at most a k-dependent constant.

Core extraction: if j=0 then all positive degrees already at least m. Otherwise sample each core edge independently with p=1/[16k(B_j+1)m^j], and delete all edges sharing any capped-side label with another sampled edge. Conditional on an edge being sampled, probability of conflict is at most jB_jm^j p<1/16. Now iteratively peel any positive uncapped-side vertex with degree below m. For each such side the initial core had at most |core|/(C_j m^{j+1}) vertices, so this further loss is at most k |core|/(C_j m^j). Choosing C_j≥256k²(B_j+1) makes it less than p|core|/8. The expected output is Ω_k(|core|/m^j). Capped labels are unique and every uncapped positive degree is at least m. The upper bound on losses does not assume survival events independent.

At j=k−2 (including initial step for k=2), form the graph on host edges adjacent when sharing any of the k−2 capped labels. Its maximum degree is ≤(k−2)B_{k−2}m^{k−2}. A largest greedy color class keeps Ω_k(E_j/m^{k−2}) edges and makes all these labels unique. The projection onto the two remaining coordinates is a simple bipartite graph because projection onto any pair is injective in the linear family. Apply the bipartite graph nonempty lemma and lift. This keeps Ω_k(E_j/m^{k−1}); both remaining labels have degree one or at least m and the already unique labels remain unique. Together with the alternative core exits this proves the lemma.

A full-kernel variant retains Ω_k(E/m^{k−1}) for k≥3: either reserve an m-matching with ≥E/2 left after deleting its vertices, then run the nonempty lemma on the residual and add back the matching, or some vertex has degree ≥E/(2km) by the endpoint-count argument. Its star is already a sunflower in a linear hypergraph. If the largest star degree is <m in this latter case, E<2km² and a singleton suffices for the claimed bound since k≥3. The k=2 full variant is only Ω(E/m²), as the standard complete bipartite obstruction indicates (not Ω(E/m) in general).

## Rank-four theorem without degree gaps

Suppose a finite simple 4-partite family has ALL six pair-projection multiplicities ≤Lm, for fixed L. Then it contains a fully valid family of size Ω_L(E/m⁴).

For nonempty witnessing apply greedy conflict coloring to the graph of edges sharing any two labels: maximum degree ≤6Lm. A largest color class retains Ω_L(E/m) and is linear. Apply the linear lemma for k=4 to retain Ω_L(E/m⁴). This works on any residual host. To handle the empty kernel, either reserve an m-matching leaving ≥E/2 edges and restore it after nonempty extraction, or a vertex of degree ≥E/(8m) exists by the usual matching cover/endpoint argument. In the latter case apply the verified unweighted full rank-three theorem to its link and lift, which retains Ω_L(E/m⁴). Alternatively the linear full-kernel lemma already yields the same bound directly on the largest pair-conflict color class, without needing rank three. For nonpartite 4-uniform inputs of global pair cap Lm, take a random four-partition first (constant fraction) and then apply this theorem.

This removes all richness/gap assumptions when every pair projection is bounded; it does not treat arbitrary triple caps with large pair codegrees, hence not the full [Janzer–Jin–Sudakov–Wu §6 question](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6).
