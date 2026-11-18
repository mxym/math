# The star and the entropy of a connected graph

For a finite simple connected graph on a fixed number of vertices, this
draft proposes a proof that the star uniquely minimizes the von Neumann
entropy of the **combinatorial Laplacian divided by its trace**. The
underlying question goes back to [Passerini and Severini](https://arxiv.org/abs/0812.2597);
it is Conjecture 1.2 in the [arXiv version of Dairyko et al.](https://arxiv.org/abs/1609.00420).
The result concerns all connected graphs, not only almost all graphs.

The proof compresses the graph without losing connectivity, obtaining
a threshold graph with no greater entropy. On that graph it identifies
the part of the spectrum contributed before the last vertex arrives
with endpoint degrees of an auxiliary graph. Shannon subadditivity
then gives a bound uniform in the order and edge count, leaving only
nine explicit integer inequalities.

Two consequences are included with their dependencies:

* At every finite real Rényi order greater than one, the same star is
  the unique minimizer (Dairyko et al., arXiv Conjecture 3.3).
  The order transfer is an application of **Sakai–Iwata**, not a new
  general entropy inequality. Order two was proved by Dairyko et al.;
  orders above two already follow from that case and Sakai–Iwata.
* Among trees, the path uniquely maximizes von Neumann entropy
  (arXiv Conjecture 1.3). This follows from **Zhou–Gutman/Mohar**
  Laplacian coefficient extremality and known entropy monotonicity.

[Proof](PROOF.md) · [Internal review](REVIEW.md) · [Prior work and search limits](SOURCES.md)

**Status:** AI-assisted mathematical draft, independently checked internally
by AI, not externally peer-reviewed or formally verified. The search does
not guarantee priority. This note makes no claim for orders below one.

## Reproduce the checks

With Python 3.9 or later (standard library only), from this directory:

```sh
python3 -B -O verify.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```

The two programs use exact integers and explicit failure conditions,
not Python assertions. [Recorded outputs](CHECKS.txt) supplement the
proof; the finite graph runs are not substitutes for it.
