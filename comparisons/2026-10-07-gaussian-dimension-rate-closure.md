# Gaussian centroid dimension-rate programme — sharp order checkpoint

*7 October 2026 · public research status; historically novel priority not claimed.*

## Core theorem — optimal dimension order now proved for all large integers

Let
[
 F_d(k)=sup_{(A_i):\gamma_d(A_i)=1/k}
       \sum_{i=1}^k\left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2
]
and (F_\infty(k)=F_{k-1}(k)). Define (D_C(k)) as the least
dimension in which (F_d(k)\ge F_\infty(k)-C/k).

The current completed project theorems imply, **for all sufficiently large
integers (k), with no power-of-two restriction,**
[
 \boxed{\frac{(\log k)^2}{108}\le D_{92}(k)
       \le\lceil(\log k)^2\rceil+1.}
]
Thus (D_{92}(k)=\Theta((\log k)^2)).

The constants 92 and 108 are explicit proof constants, not known optimal.
The finite-(k) Standard Simplex question is **not** resolved.

## Proof modules and chronology

1. [All-mass Gaussian envelope](../research/gaussian-centroid-mass-envelope/README.md):
   exactly prescribed mass partitions; one-cell halfspace envelope with
   (0\le U(p)-M_d(p)\le2\sum_i p_i^2); squared upper-tail Gaussian
   hazard globally 2-Lipschitz in log tail mass.
2. [First constructive dimension-rate theorem](../research/gaussian-centroid-dimension-rate/README.md):
   balanced Gaussian threshold trees give (O_\varepsilon(\log k)) dimension
   for each fixed relative accuracy and cyclic Gaussian orbits
   give (8(\log k)^3+2) dimension for additive (14/k) accuracy.
   This cubic bound is now superseded as the **best dimensional order**
   by the new quadratic theorem; its independent quantitative
   constructions remain correct and useful.
3. [Spherical-cap dimension converse](../research/gaussian-spherical-cap-converse/README.md):
   for every fixed additive (C/k), necessity
   (d\ge(\log k)^2/(C+16)) at all sufficiently large (k).
4. [Quadratic all-integer construction](../research/gaussian-quadratic-dimension-all-k/README.md):
   binary linear-code Gaussian score orbits handle dyadic block sizes,
   a single independent Gaussian selector glues the binary expansion of
   arbitrary (k); binary-expansion entropy obeys the *sharp*
   (H(w)<2\log2) bound. The full score gap is (<92/k)
   relative even to the halfspace envelope.

## Verification

Each mathematical claim has written analytic proofs. The quadratic
construction imports only the classical non-identically distributed
Berry–Esseen bound; the primary quantitative locator is I. S. Tyurin
(2012), DOI 10.1137/S0040585X9798572X, with published constant
(0.5591<1). The quadratic-order directory contains separate exact
rational finite-field tests and binary entropy checks; a frozen
publication commit and SHA256 integrity manifest enable remote replay.

Finite checks are not asserted to certify the probabilistic all-k
existence theorem. Its conclusion follows analytically from the
probabilistic method and the stated independent-summand Berry–Esseen
theorem.

## True remaining research questions

- Improve or identify the leading coefficient of (D_C(k)/(\log k)^2)
  for specified fixed (C), including possible limits and stability.
- Determine minimal permissible additive accuracy constant and the
  dimension-accuracy tradeoff when (C\to0).
- Find efficient explicit full-rank code generators with certified
  expected Gaussian maximum properties.
- Extend to arbitrary unequal target masses and classify exact
  finite-(k) Gaussian partition optimizers.
- Carry out comprehensive specialist originality review of Gaussian
  quantization, random coding and partition geometry before any
  journal or priority claim.
