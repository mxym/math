# Gaussian centroid partitions with arbitrary prescribed masses: a universal two-times-collision-probability approximation

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology. ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).

**Status.** Public preprint; not peer reviewed. Version DOI: [10.5281/zenodo.23273177](https://doi.org/10.5281/zenodo.23273177) · [Zenodo record](https://zenodo.org/records/23273177). The canonical research package contains the complete written theorem and proof, exact checker, audit, and literature-scope files. The result is stated as: all prescribed positive mass vectors; U(p)-2Q(p) <= M_d(p) <= U(p), with explicit two-logarithmic consequences.

- [PDF](paper.pdf) · [editable derived manuscript](paper.md) · [source ZIP](paper-source.zip)
- [canonical proof package](../../research/gaussian-centroid-mass-envelope/README.md) · [source provenance](ARTICLE_PROVENANCE.json)

**Evidence and limits.** The canonical package's checker uses exact rational arithmetic and outward rational intervals; it is a reproducibility check for the displayed finite algebraic interfaces, not a replacement for the analytic proof. External inputs (where listed in the canonical README) remain cited mathematical theorems. No external human peer review or worldwide priority claim is made. The manuscript does not claim a full Lean formalization.

Reproduce the exact checks with:

```sh
python3 -B research/gaussian-centroid-mass-envelope/check_exact.py
```

The PDF is a derived typeset edition of the canonical Markdown manuscript; the provenance file binds the canonical source hash and records that the mathematical content was not changed. Research and manuscript preparation used AI assistance; no external funding.
