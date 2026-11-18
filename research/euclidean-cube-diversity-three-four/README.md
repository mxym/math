# When do the corners maximize diversity in dimensions three and four?

For a solid Euclidean cube of side length $s$, give the vertices equal mass and use the similarity kernel $e^{-\lVert x-y\rVert_2}$. In dimensions three and four, this probability measure maximizes Leinster–Roff diversity **up to and including** the following thresholds:

| Dimension $D$ | Critical side $s_D$ | Consequence for larger cubes of the same dimension |
|---|---|---|
| 3 | $0.83811<s_3<0.83812$ | If $s>s_3$, no maximizing measure is supported only on the eight vertices. |
| 4 | $1.16444<s_4<1.16445$ | If $s>s_4$, no maximizing measure is supported only on the sixteen vertices. |

The numbers are defined by exact scalar equations in the [proof](PROOF.md), not by the decimal enclosures. For $0<s\le s_D$ the corner measure is the unique simultaneous maximizer of all diversity orders. The same sufficiency holds in **every dimension $d\ge D$**. Sharpness in dimension $D$ makes $s_D$ the largest bound valid simultaneously in all those dimensions. It does **not** make $s_4$ the threshold in each individual dimension above four.

This continues the [square result and first dimension-uniform bound](../euclidean-cube-diversity-vertex-phase/README.md). It gives neither the maximizing measure above the stated transitions nor a complete cube phase diagram.

## Reproduce the edge inequalities

With Python 3.8+ (standard library), in this directory:

```sh
python3 -O verify.py
python3 -O independent.py
sha256sum -c SHA256SUMS
```

The two programs prove inequalities on closed intervals, not only at sampled points. The first uses alternating exponential series and three subintervals of the edge. The second uses elementary exponential bounds, interval squaring and a different concavity argument. Expected outputs are in [CHECKS.txt](CHECKS.txt). The analytical reduction to these tests is in [PROOF.md](PROOF.md).

**Status:** AI-assisted research note with an independent internal AI [review](REVIEW.md), not external peer review. [Prior work and scope](SOURCES.md) are documented; global priority is not asserted.
