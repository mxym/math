# A sharp Gaussian first-moment inequality for every prescribed mass vector

**Author:** Yongxian Zhang, School of Computer Science and Engineering,
South China University of Technology. Correspondence:
[mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).
[ORCID 0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536).
No external funding; actual AI assistance is disclosed in the paper.

For every integer `k>=2`, every positive mass vector `p`, and every
ordinary or fractional Gaussian partition with those masses, we prove

```
tr(B^T H_p^+ B) <= I(p).
```

Here `B` is the cell-moment matrix, `I(p)` is the established Gaussian
`k`-cell perimeter profile in dimension `k-1`, and `H_p` is the
interface-area Laplacian of its translated regular-simplex model. The
equivalent Hessian form is

```
-sum_coordinate b_a^T Hess I(p) b_a <= I(p).
```

For dimension at least `k-1` the inequality is sharp, with equality
exactly at the model winning indicators extended cylindrically. Below
that dimension it is strict; no sharp fixed-lower-dimensional value is
claimed. This is a bound for **all** functions of the given mean, not
only perimeter minimizers. At equal masses it recovers our prior
sharp ordinary squared-centroid theorem. At unequal masses it is a
matrix-metric inequality, and does not assert the false unweighted
Euclidean prescribed-mass conjecture.

Read the complete **seven-page [paper](paper.pdf)**,
[Markdown source](paper.md), or [TeX source](paper.tex).
The covariance tangent bound, exact nonnegative deficit integral and all
boundary/equality cases are proved there. Its core geometric input is
the published Milman–Neeman multi-bubble perimeter theorem; their profile
Hessian identity is explicitly credited. This is a generalization of the
same method as the [equal-mass immutable release](https://github.com/mxym/math/releases/tag/gaussian-balanced-simplex-all-k-v1),
not a separate counting of its equal-mass corollary.

## Reproduction and scope

```sh
python check_exact.py
python verify.py
python build.py
```

The first command uses standard-library rational arithmetic for finite
diagnostic controls. It is not the proof of the Gaussian statement.
The second checks package integrity, recorded provenance and PDF text,
and needs Poppler. The third needs Pandoc and XeLaTeX; its fixed metadata
date is not a priority timestamp.

[Partial Lean proofs](formal/README.md) include the general finite
weighted Cauchy inequality and the complete abstract real differential
comparison with an arbitrary initial derivative. The nine proved exports
are replayed with official Lean 4.34.1 from an empty kernel, with their
full used declaration closure and a deliberately false control.
The entire Gaussian analytic endpoint is not formalized.

See [audit](AUDIT.md), [internal model reviews](review/),
[source versions](SOURCES.md) and [limited literature screen](LITERATURE_STATUS.md).
No external human peer review, worldwide priority, full covariance
concavity, full functional multi-bubble inequality or positive-noise
stability conclusion is claimed.
