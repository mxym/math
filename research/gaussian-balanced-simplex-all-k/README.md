# Equal Gaussian cells: the sharp simplex first-moment theorem

For every integer `k >= 2`, every measurable standard-Gaussian partition
of `R^d` into `k` cells of probability `1/k` satisfies

```
sum_i || integral_{C_i} x d gamma_d ||^2 <= (E max_{i<=k} Z_i)^2/(k-1),
```

where the `Z_i` are independent standard normals. For `d >= k-1` the
bound is attained precisely by central regular simplex cones in a
`(k-1)`-dimensional subspace, with an unrestricted orthogonal complement.
For `d < k-1` every partition satisfies strict inequality; no sharp
fixed-lower-dimensional value is claimed. Fractional partitions are
included, with the same equality classification.

Read the expanded **seven-page [paper](paper.pdf)** or its editable
[Markdown](paper.md) and [TeX](paper.tex). This proves the equal-mass
subcase for all cell counts of Heilman's 2019 first-moment conjecture,
and the full four-cell dimension-three question of his 2014 Conjecture 3.
The proof derives a global covariance comparison from Gaussian flux,
the established Milman–Neeman multi-bubble perimeter theorem, weighted
Cauchy–Schwarz, and a radial differential inequality. It also gives an
exact nonnegative deficit integral. The earlier eleven-page four-cell
proof is a historical companion, not a dependency.

[Literature status](LITERATURE_STATUS.md) records the primary sources and
the limits of the prior-result check. No worldwide priority claim is
made. This does not establish positive-correlation noise stability, the
false arbitrary-mass Euclidean statement, or full covariance concavity.

## Verification

- [Audit and scope](AUDIT.md): dependencies, boundary/equality cases and
  the explicit limits of machine checking.
- [Current derivation review](review/INDEPENDENT_MATHEMATICAL_REVIEW.md)
  checks the full proof chain against the published theorem.
  [Revision provenance](review/REVISION_PROVENANCE.json) binds the expanded
  manuscript; the two archived reviews retain their original six-page
  source scope. These are internal reviews, not external human peer review.
- [Partial Lean proofs](formal/README.md): general finite weighted
  Cauchy, scalar identities, and the abstract real differential
  comparison. Eight exports were checked with official Lean 4.34.1,
  including an empty-kernel replay of 18,013 used declarations. Gaussian
  measure, flux, balancing prices and the imported geometric theorem
  remain in the written proof.
- [Separate Lean development](https://github.com/mxym/math/pull/3):
  136 modules with exact-byte incremental compilation, including actual
  Gaussian analytic interfaces. The perimeter lower bound remains an
  explicit premise. Its earlier independent empty-kernel audit covers
  only 53 matching modules, and is not a certificate for all 136.
- `check_exact.py`: finite rational diagnostic controls, not a proof of
  the infinite-dimensional mathematical statement.
- `verify.py`: package integrity and recorded verification provenance.

From this directory:

```sh
python check_exact.py
python verify.py
python build.py
```

Python 3.10+ suffices for the rational controls; `verify.py` also needs
Poppler (`pdfinfo`, `pdftotext`). Rebuilding requires Pandoc and XeLaTeX.
The fixed build date is reproducible PDF metadata, not a priority record.
For fresh Lean replay, follow [formal/README.md](formal/README.md).

`MANIFEST.json` and `SHA256SUMS` bind every package file except themselves.
They provide integrity, not independent verification of the written
Gaussian analysis. The earlier immutable Release binds its original frozen Git commit and
attachments. This expanded manuscript is a separate draft revision and
does not change the identity or review scope of that release.
