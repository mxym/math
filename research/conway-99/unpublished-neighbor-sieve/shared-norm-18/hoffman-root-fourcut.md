# A four-edge-connected graph at every point of a Hoffman coclique

Fix any actual 22-coclique C in a hypothetical Conway 99-graph and any o in C. On the fourteen neighbors W=N(o), write M for the true mate matching (the actual edges inside W). Each of the 21 other C-points has exactly two W-neighbors, which cannot be an M-pair because that pair already has o as its unique common neighbor. No two such points give the same pair, since three common neighbors are impossible. They form the edge set of a simple cubic graph H on W: every i in W sees three other C-points besides o. In particular H and M are edge-disjoint. The weighted graph H+3M is **four-edge-connected** (edge weights count as multiplicities).

Consequently the 14 closed-root wing marks inside the rank-22 negative residual at C span exactly 13 real dimensions; their lattice has minimum squared norm at least four. The space of real minus-four fields vanishing on C and on N(o) has dimension exactly nine. This is a graph-side statement, independent of any mod-seven rank, field palette, or transitivity.

## Two incidence dictionaries

Use the [unscaled graph and projected rank-22 marks](hoffman-residual-theta.md): outside C, the four C-neighbors are the block of a 2-(22,4,2) incidence matrix D, and the projected marks have Gram Q=9I-3A_B+J-D^tD and frame constant 21. For two W vertices their C-blocks share o and share one other point exactly when they are joined in H. Their true adjacency is M. Thus the principal Gram on W is precisely the weighted Laplacian 6I-3M-A_H.

Every one of the 63 exterior sites outside C and W has exactly two W-neighbors, as it is nonadjacent to o; these are a pair in K=K14 minus (H union M). Each K edge occurs exactly once, since it has o already as a common neighbor and no other C point. Equivalently K is nine-regular and labels these 63 sites. For an exterior site b, write e_b for its K edge and F_b for its block of four points of C minus o, regarded as four H edges. Each H edge p lies in exactly 12 exterior blocks, since its C-point has two of its 14 neighbors in W. Two H edges p,q occur together in exactly 2-|p intersect q| exterior blocks: any shared endpoint in W is one already-used common neighbor.

## Excluding cuts zero and two

Weighted degree is six, so every cut has even size. For a zero cut a smallest component has even size (it is M-closed), at least five (its simple underlying graph has minimum degree four), and at most seven. Thus its vertex set S has size six. It spans nine H edges Z. Since the W-Laplacian kills 1_S, the sum of its six projected marks is zero and hence its evaluation at any exterior block is zero. The Gram formula above gives

    0=6-3|e_b intersect S|-2|F_b intersect Z|.

In fact o does not lie in F_b, while each point of Z is incident twice to S and all other H edges zero times. Hence |F_b intersect Z| is zero or three. There are 12·9=108 single incidences, needing 36 triples and thus 108 pairs; but the total pair slots among Z are at most 2 binom(9,2)=72. This excludes a disconnected component.

In a cut of weight two M cannot cross, and exactly two H edges cross. The smaller side S has even size at most six. Size two cannot have four required internal endpoint incidences in H. At size four it would need (12-2)/2=5 internal H edges while the six possible edges lose the two internal M pairs, leaving at most four. Thus |S|=6, and its internal H edge set Z has size eight. K has exactly 15-3-8=4 edges inside S, and sum_{b}|e_b intersect S|=9·6=54. Therefore k_b=|e_b intersect S| has multiplicities (13,46,4) for k=0,1,2 respectively.

Put h_b=|F_b intersect Z|. Then sum h=8·12=96 and

    sum binom(h,2)=2 binom(8,2)-sum_{i in S} binom(deg_{H[S]} i,2) ≤42.

Indeed the six internal degrees sum to 16 and each is at most three, giving the subtracted sum at least 14. Also sum k h=64. To see this, take one fixed p=uv in Z. The site of C it represents is adjacent to u,v and not to the other four W sites in S. The former each require one common neighbor with p; the latter each require two, making ten incidences. Inside W, the M mates of u and v realize exactly two of those incidences, since S is M-closed; no common neighbors lie in C. So exactly eight incidences remain with exterior b, giving 8·8=64 when summed over p.

Finally x(x-1)/2 is nonnegative for *every* integer x, also negative integers. Yet these true counts give

    sum_b binom(h_b+k_b-2,2)
      = sum_b binom(k_b-2,2) - 2 sum_b h_b + sum_b k_b h_b + sum_b binom(h_b,2)
      ≤ 3·13+46 - 2·96 +64+42 = -1.

This contradiction rules out weight two. The weighted Laplacian consequently has rank 13. For integer coefficients z its quadratic form is the sum over edges of the multiplicity times (z_i-z_j)^2. Any nonconstant z has a nontrivial integer level cut carrying at least four, proving the lattice minimum claim; the constant vector generates the sole relation. The common residual dimension is 22-13=9.
