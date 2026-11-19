# Packing 1324: the unique layered limit optimizer

Among all layered permutons there is exactly one that maximizes the density of the classical pattern 1324. It has a central decreasing block. The layers on the left and right form mirror images, each with infinitely many blocks accumulating only at the outer endpoint. Their ratios approach the geometric ratio for packing 132, but are **not** eventually constant. A contraction and one scalar maximization determine both the layer lengths and the density.

This gives the unrestricted limiting packing density because the finite layered-replacement theorem guarantees the existence of a layered maximizer at each order. It does **not** rule out other nonlayered maximizing permutons, classify finite maximizers, or settle algebraicity. Packing asks for the *largest proportion of occurrences*, not the number or growth rate of permutations avoiding 1324.

[Sliačan and Stromquist's PP2017 abstract](https://pp2017.github.io/assets/pdf/abstracts/talks/walter_stromquist.pdf) already announced a 100-digit calculation. The contribution here is the proof characterizing all layered equality cases, with a reproducible upper and lower certification, not priority for that number. Its value begins **0.2440545239294233295868733…**.

* [Proof and defining equations](PROOF.md): equation (3) identifies each successive block; equation (6) gives the global density.
* [Sources and scope](SOURCES.md), including the earlier symmetric lower construction and the status of the published bounds.
* [Independent internal review](REVIEW.md), [expected output](CHECKS.txt), and [file hashes](SHA256SUMS). This is AI-assisted mathematical research with independent internal AI review, not external peer review.

Run from this directory, with standard Python 3; no external libraries are used:

```sh
sha256sum -c SHA256SUMS
( python3 -B -O check.py && python3 -B -O digits.py ) | diff -u CHECKS.txt -
```

The first script verifies inequalities on continuous rectangles by outward-rounded integer arithmetic, not just at grid points. The second uses numerical proposals, then accepts them only after proving rigorous interval bounds.
