# ECQC parallel results: DOI and release audit

This record archives two recently completed parallel-task manuscripts. Both
were frozen at commit `c0a1085e360604a1f8f274290eb1556202a315ab`; the GitHub
releases are immutable and the Zenodo records are public and findable in
DataCite. The archive contains the PDF, source TeX, and a deterministic source
bundle for each paper. The publication package was independently downloaded
and checked against its SHA-256 manifest on 2026-10-09.

| Manuscript | Version DOI | Immutable GitHub release | Verification scope |
| --- | --- | --- | --- |
| *Extremal same-basis correlations: full-rank rigidity and a stabilizer classification* | [10.5281/zenodo.23256934](https://doi.org/10.5281/zenodo.23256934) | [ecqc-extremal-classification-v1](https://github.com/mxym/math/releases/tag/ecqc-extremal-classification-v1) | Written proof, two exact replay checkers; no claim of complete Lean formalization or external human peer review. |
| *The pure-state ECQC conjecture: counterexamples and a prime-dimensional classification* | [10.5281/zenodo.23256948](https://doi.org/10.5281/zenodo.23256948) | [ecqc-pure-state-classification-v1](https://github.com/mxym/math/releases/tag/ecqc-pure-state-classification-v1) | Written proof and exact replay checkers; the qutrit witness additionally has a complete Lean certificate, while the all-prime classification is not labeled Lean-complete. |

The qutrit Lean supplement is separately frozen at the immutable release
[ecqc-pure-qutrit-lean-v1](https://github.com/mxym/math/releases/tag/ecqc-pure-qutrit-lean-v1).
It replays 73 roots and 35,401 declarations from an empty Lean kernel at trust
level zero, with only the standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. The four-row permanent–determinant formalization is also
separately released at [four-row-permanent-tradeoff-lean-v1](https://github.com/mxym/math/releases/tag/four-row-permanent-tradeoff-lean-v1), but is not included in these two DOI records because its paper is not yet frozen as a standalone manuscript.

`PUBLICATION_STATE.json` records the API publication responses,
`ARCHIVE_AUDIT.json` records local source and attachment checks, and
`verify_downloads.py` reruns the anonymous-download and DataCite checks. DOI
records and immutable timestamps provide persistent public disclosure; they do
not by themselves certify correctness, novelty, or priority.
