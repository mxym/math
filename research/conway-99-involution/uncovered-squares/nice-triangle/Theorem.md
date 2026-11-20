# The 54-grid endpoint forces a triangle whose three roots all have one of five diagrams

Assume an SRG(99,14,1,2) with n3=1602. Write g for the number of rook grids, U for squares in no prism, D for the squares in two prisms outside any grid. A vertex x is nice if all its squares are covered and h(x)=0, where h counts the three-center motif H=0xf67e0000 as in the [covered-root inequality](../covered-root/Theorem.md). An actual existence or impossibility assertion for any of the following necessary charts is not claimed.

## At least 50 nice points

The preceding exact exclusions leave g=54. There are 2079 squares (4158 nonedges, two diagonals per square), 852 prisms, and a prism has three square faces. Consequently the number in two prisms is 3·852−2079+U=477+U. A grid has nine squares; no two grids share a square since its adjacent lines at a corner determine the entire grid. Therefore D=U−9, so 9≤U≤15.

At any point x let u_x,d_x count the uncovered and nongrid doubly-covered squares through x. For each nongrid four-cell with f≤2 flips, subtract the number of its points of flip degree 2 from the number of degree 0: the result is 4−2f. Summing shows u_x−d_x is nonnegative and even. A point not covered either has d_x≥1 or costs at least two in the latter sum. Therefore their count is at most 4D+4(U−D)/2=4U−18.

The [published two-star charging argument](../README.md) allocates at least (136/195)U from the positive identity to uncovered diagonals alone. For the H motif it allocates equal mass 2/13 to each of the three pairs of its degree-four centers (and no other pair): these are exactly its eligible nonedge marks, its total unlabeled mass is 6/13. A pair touching a covered point is not an uncovered diagonal, so its allocated mass was not used in that argument. If a copy has t covered centers, at least t of its three pairs touch a covered center (t=0,1,2,3 give respectively 0,2,3,3). Reserving those unused shares shows
 (2/13) sum_(x covered) h(x) + (136/195)U ≤ 144/13.
Hence there are at most 72−68U/15 covered vertices with h(x)>0. The count s of nice points satisfies s≥45+8U/15≥49.8, hence s≥50. This reservation does not double-spend the motif mass on uncovered diagonals. It uses the specific marks of the published certificate, not merely its scalar conclusion.

The integer covered-root bound also gives (2/3)(1593−14·99−7(4U−18)) ≤ sum_(covered x) h(x), since the 99-cell dirty sum at g=54 is 2079−486=1593 and each noncovered root has d≤21. This contradicts the upper bound 72−68U/15 if U=9 or U=10 (respectively 54>156/5 and 106/3>80/3); thus in fact 11≤U≤15. These bounds do not exclude any larger U by themselves.

## Exactly five remaining orientation containers, not five graphs

The [uniform grid-defect theorem](../../partner-regular-kg/GridDefectVectors.md) (at least 24 percolating partners per root) implies d≥6. If d≥15 the preceding integer certificate already gives h>0. The supplemental replay uses the same constitutive equations, motif lower bounds and arithmetic as that certificate on d=6,…,14. It regenerates 2,101 orientation representatives after the same necessary tests. On 2,096 it verifies a strictly positive integer numerator, hence h>0. The five omitted diagram codes are decoded by the following convenient representatives on seven axes (disjoint named parts):
* d=8: all arcs from four sources to two sinks, plus one isolated axis.
* d=10: all arcs from five sources to two sinks.
* d=11: complete four-sources-to-three-sinks diagram with one arc removed.
* d=12: all arcs from four sources to three sinks.
* d=14: four sources point to each of two sinks and to a middle axis, which itself points to both sinks.

For reference their canonical codes, in this order, are 42991782400, 10747945640, 45141371392, 45141371520, 45141371560. Bit field at positions 2(j(j−1)/2+i), for i<j, equals 0=no arc,1=i→j,2=j→i. Completeness does not imply that these remaining diagrams can occur. Run python3 verify.py. No assumptions about global symmetries, solver libraries or external downloads are used.

## A forced fully nice triangle

For a triangle/line L write p_L for its number of prism-neighbor triangles (when L is a base of a prism) and b_L for its number of containing grids. At any covered x∈L the b_L axes forming clean cells with L contribute two prism partners each. Each dirty arc into L contributes two, each arc out contributes zero, by the rooted flip/prism correspondence. Thus
 p_L=2(6−out_x(L)), b_L=6−out_x(L)−in_x(L).
Both are intrinsic line statistics, independent of the chosen point of L. In particular a pure-rich line here means p_L=2b_L with b_L=3 or 4. A full line means p_L=12. Each of the five diagrams has at least four pure-rich lines through its nice root and at least two other full lines with b_L≥1: the four/five pure sources have outdegree two or three; there are always at least two pure sinks of indegree at most five. The two line types counted are disjoint.

If every pure-rich line had at most two nice vertices, at least 4s/2 distinct pure-rich lines would be needed. Since each has b_L≥3, they would use ≥6s grid-line incidences. The full lines account for ≥2s/3 other distinct lines (each line has only three points), each with b_L≥1, hence ≥2s/3 additional incidences. But the total is 6g=324<(20/3)·50. Thus some line T is pure-rich and all three of its points are nice.

## Four possible 39-vertex triangle shells

Write T={a,b,c}. At each t∈T, the 12 neighbors outside T form a wing of six disjoint matched pairs. Across two wings the links form a perfect matching: for each point in the first wing its two common neighbors with the other T-point are its own T-parent and exactly one point of the second wing. Composing the three cross-wing matchings gives a permutation π of a twelve-point wing. Fixed points are exactly the p_T triangles matched to T. Its b_T grids contribute disjoint two-point pairs of fixed points, matched inside all three wings; they account for all p_T=2b_T fixed labels.

There remain m=6−b_T=2 or 3 matched pairs in each wing. The cross-wing maps preserve these pairs: at t∈T each nongrid axis L on its wing is oriented T→L since T is pure (indegree zero), so the two cell points of either fixed sign on T are flip mates. These are just the two images of L's wing pair under transfer to the corresponding other wing, where their link is a wing-matching edge. Therefore π permutes the m pairs. A fixed pair would either fix both points (contrary to the accounted fixed labels), or interchange them. In the latter case these six points in three wings give the six-cycle of transfers with its three antipodal mate edges, namely a K_(3,3), which violates the bound on common neighbors. The pair permutation is a derangement, hence one m-cycle. Relabel all pairs consecutively and choose signs around the cycle. All signs can be aligned except possibly the last, which is either preserved or reversed. Thus the induced 39-point shell has only the four necessary charts (m=2 or 3, with either twist). The choices of the three local nice diagrams and the 60-point extension remain to be made jointly; the four charts alone are not graphs on 99 vertices.

The compressed [`bounds.txt.gz`](bounds.txt.gz) has SHA-256 `100786484a93db6104f9cf6ae364f3535e4db9b8b79c28151cb24257c983de8a`. In the [clean replay](replay.txt), the least positive numerator is 24,692 at scale 100,000. The two C++ sources and evidence file must be in the same directory as `verify.py`.

[Subsequent exact reduction](../four-grid-shell/Theorem.md) excludes both four-grid shells and two individual nice-root diagrams. The two three-grid shells remain open.
