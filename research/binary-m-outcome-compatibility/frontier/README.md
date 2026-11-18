# Which binary and many-outcome measurements remain incompatible longest?

One measurement has two outcomes and the other has $m\ge2$. Give each its own visibility: a fraction $a$ or $b$ of the original measurement, with the remainder replaced by a uniformly random outcome. In every finite complex dimension $d\ge2$, **every** such pair can be measured jointly exactly in the region
$$
a\le (m-2)e+2\sqrt{e(e+b)},\qquad e=(1-b)/m.
$$
The curve follows pointwise from [the common-visibility proof](../PROOF.md), using the padded qubit example already supplied by Bluhm and collaborators. The curve for two binary measurements and the same scalar function for two mutually unbiased bases are prior results.

**Equality is more restrictive.** If a particular pair has its largest compatible $a$ exactly on this curve for even one $0<b<1$, it does so at *every* interior point, and it is also worst for a common visibility. This happens precisely when the pair has a nonzero common reducing subspace on which the binary observable is a Hermitian involution $S$, the other effects are projections $P_j$ resolving the identity, and $P_j S P_j=0$ for every label. Outside that subspace the measurements can be arbitrary.

With two or three labels on the second side, such a pair must contain a reducing qubit block carrying complementary measurements. Four labels are enough to avoid **every** reducing qubit block: the proof gives a rational irreducible example in dimension four, also valid after padding with further zero labels. The incremental equality question concerns $m\ge3$; there is no priority claim for the two-binary case.

[Theorem and proof](PROOF.md) · [Sources and prior boundaries](SOURCES.md) · [Internal review](REVIEW.md). To reproduce exact example and scalar checks, from this directory:

```sh
python3 -O independent.py
sha256sum -c SHA256SUMS
```

[Expected output](CHECKS.txt). This is AI-assisted work with independent internal AI review, not external peer review or formal verification. Global priority is not asserted.
