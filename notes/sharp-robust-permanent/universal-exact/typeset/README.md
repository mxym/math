# Typeset universal finite-parameter exact determinant theorem

The [10-page A4 PDF](paper.pdf) and [editable Markdown source](paper.md) present the universal maximal-minor exact formula, its binomial-product full-rank identity, sparse circuit extremality, sharp support example, finite-group action generalization and a purely polynomial finite-difference proof.

The PDF was compiled using Pandoc and pdflatex, with sample pages rendered and inspected. The source is edited for typesetting only; the canonical complete mathematical draft remains [the main proof](../paper.md).

## Rebuild

From this directory, with Pandoc and pdflatex:

    pandoc paper.md --from markdown+tex_math_dollars -s --toc --toc-depth=2 --pdf-engine=pdflatex -o paper.pdf

The published PDF has SHA-256:

    d349387be3c0f5f2cdb731a14e4a3882484c49758c92a2b343b7af8417192b82

The typeset source SHA-256 is:

    dcaa2c28eb3c224aaca31f97112eff7ff0026f620e4edf0356b75956c87d5a00

Git blob SHA for the PDF: aa48d74dbe52de45a559f806c7c377d616bae8aa.

TeX output binary hashes may vary across environments due to metadata, engine versions or fonts; mathematical source content is fully public.

## Verification and limitations

- [Solver-free exact formula checker](../../code/check_universal_max_minors.py)
- [Independent elementary rank-recurrence replay](../../code/check_finite_difference_rank.py)
- [Sharp six-contact witness](../../code/check_sparse_support_sharpness.py)
- [Generic circuit audit](../../code/check_generic_circuit_audit.py)
- [Verification report](../VERIFICATION.md)
- [Lean formalization plan](../LEAN_ROADMAP.md)

The theorem is proved mathematically for every finite (n,k), but has **not** been fully formalized in Lean or externally peer-reviewed. The formula still contains an explicit **finite maximum**; a much shorter elementary piecewise-rational expression without this maximum remains an unsolved strengthening.
