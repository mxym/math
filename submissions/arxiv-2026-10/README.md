# October 2026 arXiv preparation

The active submission is the single combined Bapat paper:

- [Paper and source package](bapat-q-permanent-counterexamples/README.md)
- [PDF](bapat-q-permanent-counterexamples/paper.pdf)
- [Uploadable TeX ZIP](bapat-q-permanent-counterexamples/bapat-arxiv-source.zip)
- [Submission metadata](bapat-q-permanent-counterexamples/SUBMISSION_METADATA.json)
- [Audit record](bapat-q-permanent-counterexamples/AUDIT.md)

This is a submission preparation, not an arXiv submission or acceptance.
The author has not yet registered an arXiv account. Gaussian first-moment
research is deferred for further work and Lean coverage before submission,
as requested by the author. Combining the existing Bapat results does not
count them as a new additional mathematical breakthrough.

The official [arXiv moderation policy](https://info.arxiv.org/help/moderation/index.html#submission-rate),
checked on 8 October 2026, says: “Each author may submit up to two new
submissions per calendar month with a limit of three active submissions.”
See the [1 October 2026 announcement](https://blog.arxiv.org/2026/10/01/updated-rate-limit-policy/).
This is a submission limit, not a guarantee of inclusion. Account creation,
any category endorsement required by arXiv, and the final license selection
are operational steps remaining for the author.

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
