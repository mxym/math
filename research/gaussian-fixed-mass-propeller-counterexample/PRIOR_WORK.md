# Prior work and attribution

This note records the directly relevant statements and their scope. It is a finite literature comparison, not a proof review, exhaustive citation search, or priority claim.

## Heilman’s Conjecture 1.16

Steven Heilman, “Stable Gaussian Minimal Bubbles,” arXiv:1901.03934v1 (submitted 13 January 2019), §1.4, Problem 1.15 and Conjecture 1.16, printed p. 8:

- [arXiv abstract and version history](https://arxiv.org/abs/1901.03934)
- [v1 PDF](https://arxiv.org/pdf/1901.03934v1)

The v1 record is the only arXiv version listed. No DOI for this manuscript was verified. The similar title *The Structure of Gaussian Minimal Bubbles*, arXiv:1805.10203v3, is a separate Gaussian-perimeter paper; its journal version is *Journal of Geometric Analysis* 31 (2021), 6307–6348, DOI [10.1007/s12220-020-00531-x]. It is not a later version of 1901.03934.

Here is the setup of Heilman’s equation (1), which he calls a cone over a regular simplex. Let \(z_1,\ldots,z_m\) be the vertices of a regular simplex centered at the origin in \(\mathbb R^d\). For a translation vector \(w\), set
\[
\Omega_i=w+\{x\in\mathbb R^d:\langle x,z_i\rangle
                    =\max_{1\le j\le m}\langle x,z_j\rangle\},
\qquad \gamma_d(\Omega_i)=a_i.
\tag{1}
\]
The masses \(a_i>0\) sum to one. The vector \(w\) in Problem 1.15 is the translation associated with this regular-simplex cone family at those masses, and \(w^{(i)}=w/a_i\).

**Problem 1.15** asks, for fixed \(a_i>0\), to maximize over all measurable partitions \((\Omega_i)_{i=1}^m\) with \(\gamma_d(\Omega_i)=a_i\) the objective
\[
\sqrt{\pi/2}\sum_{i=1}^m
\left\|\int_{\Omega_i}(x-w/a_i)\,d\gamma_d(x)\right\|^2.
\]
**Conjecture 1.16** says that if \(m-1\le d\), the sets maximizing Problem 1.15 are simplicial cones over a regular simplex. The paper states \(m>3\) in Problem 1.15 and explains that \(m=3\) was already solved in references [KN09, KN13]. Thus the conjecture as printed includes \(m=4,d=3\) and arbitrary positive four-cell masses; it ranges over all measurable partitions and asserts that an optimizer is in the regular-simplex-cone family.

For any competing partition with the same prescribed masses, writing \(m_i=\int_{\Omega_i}x\,d\gamma_d(x)\), one has
\[
\sum_i\left\|\int_{\Omega_i}(x-w/a_i)\,d\gamma_d(x)\right\|^2
=\sum_i\|m_i-w\|^2
=\sum_i\|m_i\|^2+m\|w\|^2,
\]
because \(\sum_i m_i=\int_{\mathbb R^d}x\,d\gamma_d(x)=0\). The centering therefore changes the objective by a constant on the fixed-mass class. At equal masses the centered regular-simplex cone has \(w=0\). The present manuscript’s unequal-mass counterexample concerns the arbitrary-mass assertion of Conjecture 1.16; it does not establish a result for \(a_i=1/4\).

Heilman’s §1.4 calls this the “Propeller Conjecture” and relates Problem 1.15 to the \(\rho\to0\) endpoint of noise stability. His introduction (printed p. 4) says that the \(m>3\) first-moment quantity is expected to be maximized by the regular-simplex cones and that this is still open. The source citation should be preserved when stating the counterexample: it contradicts this arbitrary-mass conjectural claim if the proof in paper.md is accepted.

## Unequal-mass positive-noise counterexamples are different

Steven Heilman, Elchanan Mossel, and Joe Neeman, “Standard Simplices and Pluralities are Not the Most Noise Stable,” *Israel Journal of Mathematics* 213 (2016), no. 1, 33–53, DOI [10.1007/s11856-016-1320-y], arXiv:1403.0885v3:

- [arXiv abstract and version history](https://arxiv.org/abs/1403.0885)
- [v3 PDF](https://arxiv.org/pdf/1403.0885v3)

The abstract and Theorem 2.6 state that for \(k\ge3\), unequal prescribed masses, and \(0<\rho<1\), a shifted flat (in particular shifted standard-simplex) partition is not optimal for the positive-\(\rho\) Gaussian noise-stability functional. The theorem also states the corresponding strict non-minimality for \(-1<\rho<0\). This is prior work on the unequal-mass **noise-stability** problem.

Theorem 2.6 does not assert strict improvement of
\[
\left.\frac{d}{d\rho}\sum_i\int 1_{\Omega_i}T_\rho1_{\Omega_i}\,d\gamma_d
\right|_{\rho=0}
=\sum_i\left\|\int_{\Omega_i}x\,d\gamma_d(x)\right\|^2.
\]
An improvement for each fixed \(\rho>0\) is not, by itself, a strict improvement of the derivative at zero. Heilman 2014, arXiv:1211.7138, likewise distinguishes the positive-noise unequal-mass failure (its p. 37, citing HMN Theorem 2.6) from its separate question about the optimizer at fixed positive noise. Heilman 2019 explicitly leaves the \(m>3\) first-moment problem as a separate open problem. We found no statement in these sources giving the present strict first-moment comparison.

The full HMN16 proof was checked, not just its abstract. Its normal-variation argument uses the value \(\rho=0\) to verify that the perturbation preserves volume to first order (around printed p. 7); its strict improvement conclusion is for fixed \(\rho\in(0,1)\) in Theorem 2.6. It does not derive or state a strict comparison of the derivative in \(\rho\) at zero. This distinction is relevant because the present manuscript compares precisely that derivative/first-Hermite objective.

## OpenAI Gaussian propeller bound (result 096)

OpenAI Mathematics, “The Gaussian Propeller Bound in Every Dimension,” result family 096, 24 September 2026, pinned PDF at [the OpenAI math repository](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf), was checked in full. Its introduction defines the unnormalized-centroid objective over all finite measurable partitions, explicitly says cell probabilities are unrestricted and empty cells are allowed, and proves the universal bound \(9/(8\pi)\), attained by three planar sectors extended by an orthogonal factor. This is a global, unconstrained-mass propeller theorem. It neither fixes a positive mass vector nor compares a translated regular tetrahedron with another partition having the same four masses. It does not state the unequal-mass first-Hermite counterexample in this manuscript.

## Equal-mass scope and search boundary

This manuscript treats only mass vectors \((p,(1-p)/3,(1-p)/3,(1-p)/3)\) with \(0<p<1/4\), including values arbitrarily close to \(1/4\). It neither refutes nor proves the equal-mass four-cell tetrahedral first-moment optimization problem. The equal-mass Standard Simplex Conjecture for positive noise is a separate statement; it is not the claim refuted here.

The comparison checked Heilman 2019 v1, Heilman–Mossel–Neeman 2016 v3, Heilman 2014, and the related 2018 Gaussian-perimeter manuscript/version. It was a targeted search of these primary sources and their cited statements, not a comprehensive search of all later literature. Accordingly, no “first,” priority, or worldwide-novelty claim is made. The earlier unequal-mass positive-noise theorem is cited as related prior work and distinguished by its objective and parameter range.
