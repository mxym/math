# Which integers count the cycles of a simple 3-connected graph?

Every positive integer occurs except **1–6, 8–12, 16–20, 27, 30 and 32–34**. This is precisely §6(a) of McCulloch, McKay, Salahshoori and Zaslavsky. Cycles are undirected simple cycles, not their lengths, and the host has at least four vertices. No regularity or planarity condition is imposed. The 3-connected cubic questions §6(c,e) are not addressed.

The main step is an infinite realization construction with no gaps. A family of hub-and-path graphs has a quadratic cycle polynomial. Four pairs of branch lengths encode a sum of four squares, and 87 small cores together cover every required residue. This gives an explicit tail starting at 23,342,160. An exact finite bridge reaches the tail from below. All 2,624 residual graph witnesses can be regenerated and individually counted. The upper endpoint is an internal proof parameter; the last actually missing count is 34.

The 21 exclusions are **not** claimed as new: an earlier order-dependent lower bound combined with a publicly reported order-nine enumeration already implies them. Here two small-budget censuses independently verify the negative direction without assuming that data. See [scope and primary sources](SOURCES.md), the [full proof](PROOF.md), and the [internal review](REVIEW.md).

## Reproduce

Use Python 3.10+ (standard library), a C++17 compiler, and a few minutes. Run in a writable copy of this directory:

```sh
sh reproduce.sh
```

This reconstructs two graph streams from the small template/mask files and checks their digests rather than requiring a precomputed collection of graphs. The C++ checker inspects the literal edges, connectivity after up to two vertex deletions, and the cycles. The final independent Python replay counts cycles by enumerating elements of the binary cycle space, not via the incremental ear formula. No external third-party graph dataset or installed graph library is used.

AI-assisted mathematical research and internal adversarial review. Neither a claim of external peer review nor a guarantee of priority.
