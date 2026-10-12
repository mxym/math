# October 2026 arXiv preparation

The combined Bapat manuscript and reproducible source package:

- [Paper and source package](bapat-q-permanent-counterexamples/README.md)
- [PDF](bapat-q-permanent-counterexamples/paper.pdf)
- [Uploadable TeX ZIP](bapat-q-permanent-counterexamples/bapat-arxiv-source.zip)
- [Submission metadata](bapat-q-permanent-counterexamples/SUBMISSION_METADATA.json)
- [Audit record](bapat-q-permanent-counterexamples/AUDIT.md)

This directory provides a portable paper and source package. The combined
paper preserves two previously certified mathematical results; it does not
present their editorial consolidation as a separate breakthrough. Its exact
proof and archive scope is recorded in the linked audit. Submission license,
classification and platform compilation should be checked for the actual
submission.

Rebuild from a fresh extracted source archive with Python 3, TeX Live,
`pdflatex`, `pdfinfo`, `pdffonts`, and `pdftotext`:

```
python3 -B submissions/arxiv-2026-10/build_bapat.py --output /tmp/bapat-new-build
```

The output directory must not exist. The builder produces the upload ZIP,
builds its extracted TeX three times with shell escape disabled, checks
references and font embedding, runs both exact integer checkers, and rejects
both optimized execution and a deliberately false rank-one certificate.
It does not rerun Lean or certify the analytic proof by numerical testing.
