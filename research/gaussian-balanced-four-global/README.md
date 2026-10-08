# Complete equal-mass Gaussian four-cell theorem

The [eleven-page paper](paper.pdf), [editable manuscript](paper.md), and
[TeX source](paper.tex) prove the complete global inequality

$$
\sum_{i=1}^4\left|\int_{C_i}x\,d\gamma_d\right|^2
\le\frac{12(\arctan\sqrt2)^2}{\pi^3}
\qquad(d\ge3,\ \gamma_d(C_i)=1/4).
$$

Equality holds exactly for central regular tetrahedral winning cones,
extended cylindrically, modulo null sets, orthogonal maps and relabeling.
The statement also covers fractional partitions. This settles Heilman's
2014 Conjecture 3 in dimension three, with a regularity classification,
and the equal-mass four-cell case of his broader 2019 Conjecture 1.16.
[The precise prior statements and search limits](LITERATURE_STATUS.md)
distinguish this from perimeter, unrestricted propeller, unit-variance
maximum and positive-noise results. No worldwide priority claim is made.

中文：这里给出四个等质量高斯单元的一阶矩猜想的完整全局证明及等号分类。
它覆盖任意可测分割及分数分割、所有 d≥3，不是只有局部极值或数值证据。
不涉及任意质量、更多单元或正相关噪声稳定性。

The proof combines the established Gaussian multi-bubble perimeter theorem
with a new covariance deformation argument. A smooth regularization and a
normal-cone residual estimate prevent singular-boundary escape in the
constrained mountain-pass proof. The manuscript includes every required
rank obstruction and local calculation; readers need not recover them
from earlier repository versions. The two imported Gaussian isoperimetric
theorems and ordinary finite-dimensional analysis are named explicitly.

No computer calculation is a premise of the global theorem. Eight partial
Lean exports check scalar algebra, with a fresh empty-kernel replay of
7,286 dependency declarations and a rejected false weakened-profile
control. They do **not** formalize the Gaussian integrals, imported
perimeter theorem, deformation flow or complete endpoint. Two independent
internal model reviews are in [review/](review/); they are not external
human peer review.

Reproduce the exact diagnostics and verify the bound package:

```sh
python check_exact.py
python verify.py
```

The exact diagnostic covers 720 rational matrix cases and 3,087 local
Hessian identity cases, and detects two intentionally false variants.
These counts describe finite algebra checks, not a global Gaussian search.
See [formal/README.md](formal/README.md) for a fresh pinned Lean replay.
Rebuild the PDF/TeX/text with Pandoc, XeLaTeX and Poppler using:

```sh
python build.py
```

`MANIFEST.json` and `SHA256SUMS` bind every package file except themselves.
They do not recursively hash themselves. Immutable release assets add a
commit/tag binding and GitHub release attestation. Later corrections must
be disclosed in a new version. The earlier [rank-rigidity note](../gaussian-balanced-four-rigidity/README.md)
and its numerical discovery data remain a historical partial checkpoint;
covariance concavity is still unproved and is unnecessary here.
