# Large-palette extremizers for proper colorings of cubic graphs

Count the proper vertex colorings of a finite simple graph with $q$ labeled colors, and take the $|V(G)|$th root to compare graphs of different sizes. This note proves two ranges of [Cambie and Jooken's Conjecture 5.2](https://arxiv.org/html/2311.05542v2):

| Cubic graph class | Extremizer | Range proved here |
|---|---|---|
| No triangles | Petersen graph minimizes | Every integer $q \ge 37$ |
| No 4-cycles (triangles allowed) | Heawood graph maximizes | Every integer $q \ge 88$ |

In each row equality holds precisely for disjoint unions of copies of the stated graph. The thresholds are sufficient, not claimed sharp. This does **not** settle the full conjecture, nor does it concern Jaeger's edge-coloring conjecture.

The proof compares the short-cycle terms in the logarithm of the chromatic polynomial. A graph component not isomorphic to the proposed extremizer has a local short-cycle deficit. A published chromatic-root bound controls the rest of the logarithmic series for graphs of every order. The explicit palettes use an eighth-order finite calculation; a weaker uniform large-palette statement has a paper-only proof.

[Proof](PROOF.md) · [Prior work and scope](SOURCES.md) · [Independent mathematical review](REVIEW.md) · [Reproducibility and exact output](CHECKS.txt).

AI-assisted research with independent internal AI review, not external peer review or formal verification. No claim of priority. Referenced publications and third-party material remain subject to their respective rights.
