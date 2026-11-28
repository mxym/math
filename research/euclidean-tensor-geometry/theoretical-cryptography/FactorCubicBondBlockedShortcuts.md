# A cubic-lattice bond percolation lower bound from blocked shortcuts

Research note, 28 November 2026. We give a deterministic lower bound for the critical probability of nearest-neighbor **bond** percolation on \(\mathbb Z^3\):
\[
                             p_c> 0.215805.
\]
All edges are independently open with probability \(p\). This is not a statistical confidence bound, does not refer to site percolation, and does not estimate the critical value exactly.

A published benchmark is the self-avoiding-walk bound from Pönitz–Tittmann, whose upper bound on the cubic-lattice connective constant is about \(4.7387\), giving \(p_c\gtrsim0.21103\) by the usual union bound over open self-avoiding walks. See their [primary paper](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v7i1r21/pdf/) and the corresponding application discussed in [Ashton's notes](https://kaust-a-laut.github.io/). [Yu–Wierman's \(0.347297\)](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/abs/an-upper-bound-for-the-bond-percolation-threshold-of-the-cubic-lattice-by-a-growth-process-approach/C1FB01EDD1DB4B08DA84153F79FF2B20) is an **upper** bound. [Ball's interval](https://arxiv.org/abs/1312.0961) is a confidence statement, not a deterministic inequality. For method context, [Ashton's site-percolation work](https://kaust-a-laut.github.io/pdfs/z3-site-lower-bound-0.263376-proof.pdf) uses canonical breadth-first paths and disjoint obstructions on sites; our calculation instead uses edges of blocked one- and two-edge shortcuts, partitioned into blocks with a parity rule.

## 1. Path constraints

For each site with finite open distance from the origin, pick its predecessor among open neighbors with distance one less, preferring axes in the fixed order \(x,y,z\), then resolving the two opposing directions arbitrarily. A canonical path means a path obtained by following these predecessors to the origin and reversing. For a canonical path \(v_0,\ldots,v_t\), the distance of \(v_j\) from the origin is exactly \(j\), and the path is simple.

A chord between \(v_i,v_j\) at distance one in the lattice, with \(|i-j|>1\), must be closed, or the open distance of the later vertex would be smaller. Moreover, suppose a vertex \(z\) is adjacent to \(v_i\) and \(v_j\) for \(i<j\). If \(j-i\ge4\), the two edges \(v_i z,zv_j\) cannot both be open, since they would yield a shorter route to \(v_j\). If \(j-i=2\) and the axis of \(zv_j\) has priority over the axis of \(v_{j-1}v_j\), they also cannot both be open: with both open either the distance of \(z\) is less than \(i+1\), giving a shortcut, or it is \(i+1\) and \(z\) is the preferred predecessor. This uses no assumption about the distance to \(z\) in the actual configuration.

## 2. Separate all the tested edge sets

Choose an even positive integer \(N\). Consider a candidate canonical path of length \(1+bN\), with an unrestricted first directed edge and \(b\) consecutive blocks of \(N\) edges thereafter. A block beginning at index \(i\) uses the \(N+2\) vertices \(v_{i-1},v_i,\ldots,v_{i+N}\), where \(v_{i-1}\) is its one memory vertex. Its chord count \(C\) includes each chord whose later endpoint is one of \(v_{i+1},\ldots,v_{i+N}\) and both endpoints lie in the displayed vertex set.

The anchors of the block are \(v_{i+2},v_{i+4},\ldots,v_{i+N-2}\). For each lattice vertex \(z\) *outside the displayed vertex set* adjacent to two anchors forming either kind of forbidden pair in §1, choose one such pair and require that its two edges are not both open. Let \(K\) count such centers \(z\); there is one constraint per center. Which pair is chosen can be fixed deterministically and does not affect the count or weight. All anchors of all blocks have the same bipartite vertex parity because \(N\) is even.

On a globally simple path these edge constraints and the open path-edge constraints are disjoint in their underlying edges:

* Each path edge is counted open once, and a counted chord cannot be a path edge. Chords from different blocks have different later endpoint indices or different earlier edges and so are not repeated.
* Within a block the centers are outside its vertex set, and the anchors are strictly internal. Consequently the two-edge constraints use no path edge and no same-block chord. A different block's chord also cannot use one of these edges: the anchor is internal and is not in the vertex set of any other block, even with the memory vertex.
* Centers are all on the opposite parity from the anchors. Thus an edge occurring in a two-edge constraint has a uniquely determined anchor endpoint, and constraints belonging to different blocks cannot share an edge. Within each block there is just one constraint at each center, and different centers likewise give disjoint pairs.

This is why one cannot simply multiply penalties for every observed shortcut without checking parity and boundary overlap. Product edge independence now bounds the probability that the path is canonical by
\[
        p^{1+bN}\prod_{\text{blocks}}(1-p)^C(1-p^2)^K .
        \tag{1}
\]

## 3. Exact finite transfer

In a block, use as state the axis of the remembered edge \(v_{i-1}v_i\); the sign does not matter by coordinate reflection. For each of the three states, enumerate every simple \(N\)-step continuation of a fixed positive directed edge on that axis, rejecting visits to the two initial vertices. This ignores self-intersections with older blocks, which only increases the upper bound. For each continuation record its chord count \(C\) and the outside-center count \(K\) defined above; the exit state is its last-step axis. Set \(M_{s,t}(p)\) equal to the sum of \(p^N(1-p)^C(1-p^2)^K\) over those continuations from state \(s\) to state \(t\). If its maximum row sum is below one, (1) and an ordinary union bound show that the probability of a canonical path of length \(1+bN\) decays geometrically. An infinite open cluster containing the origin would have canonical paths of each length: its graph distances are unbounded since graph balls are finite. Thus no such cluster occurs at this \(p\). Since the entries are finite polynomials and the row test is strict, the test still holds for a slightly larger \(p\), proving the strict bound on \(p_c\). This reasoning only uses multiplication of the probabilities for the fixed global path event, not a claim of probabilistic independence of the successive canonical choices.

For \(N=12\) and \(p=0.215805\) the exact upper rounded row sums in parts per million are \(999945,,999972,,999999\). The first factor \(6p\) from the unrestricted first edge has no effect on the contraction. The replay uses integer enumerations and exact rational evaluation; it does not need a spectral approximation, simulation, or an infinite-cluster search.

The common unweighted count is \(157\,329\,085\) per row, since fixing a directed first edge leaves one sixth of the \(943\,974\,510\) length-13 self-avoiding walks. For replay run `node verify_factor_cubic_bond_shortcuts.js`; individual rows can be checked with `--axis=0`, `--axis=1`, or `--axis=2`. The optional `--small-test` compares every histogram entry at \(N=8\) with a separate leaf algorithm that explicitly tests all path chords and every pair of anchors for common-neighbor obstructions, rather than maintaining the online center masks.
