# Sharp line-graph signature at fixed rank for graphs of treewidth at most two

Let $G$ be a finite simple connected graph, $c=|E|-|V|+1$ its cycle rank, and $s(L(G))$ the number of positive adjacency eigenvalues of the line graph minus the number of negative ones. **Among all $K_4$-minor-free graphs of rank $c$, the maximum of $s(L(G))$ is $\lfloor(c+1)/2\rfloor$.** Equivalently, the upper bound in Paone–Paone Conjecture 5.4 holds for every graph of treewidth at most two. The matching lower examples are **already due to Paone and Paone**, even among cacti.

The new step is a two-terminal inequality that survives arbitrary series and parallel compositions. Eighteen possible bounds, or 36 after choices of terminal order and sign, are closed under the operations needed to build every biconnected block. Allowing arbitrary one-vertex attachments then handles bridges, cut vertices, pendant trees and isolated root vertices. The 2,916 finite comparisons are part of the proof, **not** a census of small graphs.

The [earlier cactus result](../line-signature-cactus-simple-kernel/README.md) is a proper subclass; its separate simple-suppressed-kernel theorem includes graphs outside treewidth two. The present result proves **no unrestricted graph bound** and does not classify equality cases. AI-assisted working paper, independently checked internally but not externally peer reviewed; no priority claim.

- [Proof and explicit state table](PROOF.md) · [constraint/pullback argument for arbitrary hosts](BOUNDARY.md)
- [Primary sources and overlap with earlier work](SOURCES.md) · [independent internal review](REVIEW.md)
- [Standard-library proof checker](verify.py) · [exact output](CHECKS.txt)
- [Alternate symbolic checker](symbolic.py) · [exact output](SYMBOLIC.txt)

To reproduce, run `python3 -B -O verify.py` from this directory. The independent implementation of the finite algebra uses different elimination machinery and requires **SymPy** (tested with 1.14.0): `python3 -B -O symbolic.py`. For a third comparison, `python3 -B -O crosscheck.py` checks that both implementations emit the same cost, domain and quadratic form **before** rounding on all 2,916 operations ([output](CROSS-CHECKS.txt)). Both are author-side implementations; the written internal mathematical review is separate. `sha256sum -c SHA256SUMS` checks the package files. No third-party paper, dataset or library source is incorporated here.
