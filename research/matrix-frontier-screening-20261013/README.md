# Matrix-frontier screening, October 13, 2026

The root repository was checked at `8353cff72`. No repository AGENTS.md was
present. Existing four-row work proves every nonnegative absolute determinant
weight and every **real** pencil coefficient; it explicitly leaves nonreal
coefficients unclassified. Existing three-row work already proves all complex
coefficients, so it was not repeated.

Primary inputs checked: Carlen–Lieb–Loss, math/0508096 (sharp permanent row norm)
and OpenAI/math's September 26 strict four-row permanent manuscript. Broader
searches did not establish priority or the openness of every possible equivalent
formulation. The archived exploratory script performs alternating row maximization
over **actual complex 4×4 matrices**, with 160 random initializations at eight
coefficients. Its output agrees with the **unproved candidate**

    max{3/2, |1+λ|, |1−λ|, |λ+i/√3|, |λ−i/√3|}.

The extra two branches come from a 3×3 Fourier witness direct-summed with 1.
Numerical maximization is not a global proof. The existing radial tradeoff loses
the relative permanent/determinant phase and does not imply this candidate;
restricting a putative optimizer to unitary matrices is also unproved. No
four-row nonreal exact-norm theorem is asserted by this screening artifact.

An independent ECQC equality route then produced the substantive new
[critical-rank classification](../ecqc-critical-rank-equality/PAPER.md).
Classical parity/phase-point machinery was checked in Gross quant-ph/0602001v3
and Durt et al. 1004.3348v2, and was credited. The new target is the necessity,
all-phase classification and congruence obstruction at r=(p+1)/2, rather than
claiming the familiar parity construction or a small numerical witness as new.
The smaller-rank ECQC problem and four-row complex norm remain open in this repo.

This screening records a changed research target, not a proof of historical
novelty. No external funding or human referee review; AI-assisted work.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.
