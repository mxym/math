# How order and average degree jointly force cycles

Count undirected simple cycles by edge set. Write $n$ for the order and $d$ for the average degree of a finite simple graph.

* **Large average degree.** For each $k=2,3$ and each fixed $0<η<k$, every $k$-vertex-connected graph of sufficiently large average degree has at least `n^(k−η) · floor(ηd/(8k))!` cycles. The threshold depends only on $k,η$. Taking $η=1$ answers the quadratic-order and 2-connected questions of Alahmadi et al. (2015, §7, Problems 2 and 3) at the factorial scale specified there. The proof uses Knor's three-extra-edge lemma for the order bound, Mader's connectivity theorem for the degree bound, and interpolation. The exact endpoint $n^k$ **with** a growing factorial factor is not asserted.
* **Minimum degree four.** For each sufficiently large $n$, the minimum cycle count among 3-connected $n$-vertex graphs of minimum degree at least four is of order $n^3$, without a maximum-degree cap. Knor (1994) gave the upper construction and lower bounds under stronger hypotheses. When there is a vertex of large degree, count cycles through it via paths between its neighbors after its deletion; otherwise use Knor's construction of cycles through disjoint triples.

[Order and density proof](PROOF.md) · [Degree-four proof](KNOR.md) · [Precedents and scope](SOURCES.md) · [Internal review](REVIEW.md).

The mathematical arguments are independent of the computation. To check the elementary path and disjoint-triple ingredients on all labeled simple graphs on three through six vertices, run from this directory:

```sh
sha256sum -c SHA256SUMS
python3 check.py | diff - CHECKS.txt
```

This AI-assisted research note was independently reviewed by another AI workflow, not externally peer-reviewed. No priority guarantee, sharp factorial constant, wheel threshold, or result on Knor's separate general fixed-maximum-degree conjecture is claimed.
