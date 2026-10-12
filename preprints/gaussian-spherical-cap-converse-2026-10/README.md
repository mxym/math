# A spherical-cap obstruction for Gaussian equal-mass centroid partitions

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology. ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).

**Status.** Public preprint; not peer reviewed. Version DOI: [10.5281/zenodo.23273187](https://doi.org/10.5281/zenodo.23273187) · [Zenodo record](https://zenodo.org/records/23273187). The canonical research package contains the complete written theorem and proof, exact checker, audit, and literature-scope files. The result is stated as: global dimension lower bound d >= (log k)^2/(C+16) for O(1/k)-accurate equal-mass Gaussian centroid partitions.

- [PDF](paper.pdf) · [editable derived manuscript](paper.md) · [source ZIP](paper-source.zip)
- [canonical proof package](../../research/gaussian-spherical-cap-converse/README.md) · [source provenance](ARTICLE_PROVENANCE.json)

**Evidence and limits.** The canonical package's checker uses exact rational arithmetic and outward rational intervals; it is a reproducibility check for the displayed finite algebraic interfaces, not a replacement for the analytic proof. External inputs (where listed in the canonical README) remain cited mathematical theorems. No external human peer review or worldwide priority claim is made. The manuscript does not claim a full Lean formalization.

Reproduce the exact checks with:

```sh
python3 -B research/gaussian-spherical-cap-converse/check_exact.py
```

The PDF is a derived typeset edition of the canonical Markdown manuscript; the provenance file binds the canonical source hash and records that the mathematical content was not changed. Research and manuscript preparation used AI assistance; no external funding.
