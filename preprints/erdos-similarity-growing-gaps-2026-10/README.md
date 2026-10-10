# Erdős similarity: growing logarithmic gaps

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology.
ORCID: [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).

[Version DOI: 10.5281/zenodo.23272596](https://doi.org/10.5281/zenodo.23272596) · [Zenodo record](https://zenodo.org/records/23272460)

This preprint proves positive-measure affine non-universality for every prescribed countable family of positive null sequences satisfying the late-annulus filling condition

```text
z_{n+1} - z_n = o(log log z_n)
```

and for the stated intermittent-window extension. It includes sequences whose adjacent ratios tend to zero and whose occupied logarithmic bins have zero upper Banach density. The full Erdős similarity conjecture, including `2^(-n^2)` and `2^(-2^n)`, remains open.

The [canonical package](../../research/erdos-similarity-growing-gaps/README.md) contains the complete written proof, scope limits, prior-work comparison, exact finite checker, and partial Lean replay. The DOI record freezes the PDF and source archive. Finite diagnostics are evidence for algebraic controls only; the infinite analytic theorem is written proof and is not claimed to be fully Lean formalized. No external human peer review or worldwide priority claim is made.

Reproduction from the canonical package:

```sh
python3 -B research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B -O research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B research/erdos-similarity-growing-gaps/verify.py
```

AI-assisted research is disclosed in the paper and repository. Original material follows the repository reserved-rights policy.


This directory uses the signed author edition. Only author/affiliation/ORCID and PDF metadata changed from the earlier immutable version; [ARTICLE_PROVENANCE.json](ARTICLE_PROVENANCE.json) records the canonical source hash.
