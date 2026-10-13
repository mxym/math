# Four equal Gaussian cells: covariance deformation and tetrahedral rigidity

**Public preprint; not peer reviewed.** Version DOI: [10.5281/zenodo.23272806](https://doi.org/10.5281/zenodo.23272806) · [Zenodo record](https://zenodo.org/records/23272806).

For every measurable or fractional partition of standard Gaussian space into four equal-mass cells, the sum of squared first moments is at most

\[12(\arctan\sqrt 2)^2/\pi^3.\]

Equality holds exactly for central regular-tetrahedral winning cones, up to null sets, orthogonal maps, relabeling, and cylindrical extension. The result settles Heilman’s 2014 Conjecture 3 in dimension three and the equal-mass four-cell case of the 2019 Conjecture 1.16, with the imported Gaussian multi-bubble theorem stated explicitly. The broader arbitrary-mass conjecture is not claimed.

**Mathematical status.** This is a complete ordinary mathematical proof of the stated theorem. It uses the published Gaussian multi-bubble theorem of Milman–Neeman (Annals of Mathematics 195 (2022), Theorem 1.1) and the classical Gaussian isoperimetric theorem as explicitly cited external inputs; their hypotheses and the perimeter normalization are matched in the manuscript. The remaining covariance, boundary, deformation, equality and constant calculations are proved in the paper.

- [PDF](paper.pdf)
- [Canonical source package and full proof audit](../../research/gaussian-balanced-four-global/README.md)
- [Editable manuscript](../../research/gaussian-balanced-four-global/paper.md)
- [Audit and verification scope](../../research/gaussian-balanced-four-global/AUDIT.md)

The Lean project separately verifies the internal proof chain except for the external Gaussian multi-bubble theorem and portions of the Gaussian integral evaluation. It does not replace the cited published theorem; it verifies the formal consequences and finite analytic reductions once that theorem is supplied. The exact checker uses rational arithmetic for finite diagnostics (720 matrix cases and 3,087 local identity cases), with two negative controls. Reproduction from the canonical package:

```sh
cd research/gaussian-balanced-four-global
python3 check_exact.py
python3 verify.py
```

No external human peer review or historical-priority claim is made. Research and manuscript preparation used AI assistance; no external funding. Original material is reserved unless a file states another license.


This directory uses the signed author edition. Only archive binding metadata was corrected in this v4 edition; the author/affiliation/ORCID, bibliography, research-method disclosure and PDF metadata remain unchanged from v3. [ARTICLE_PROVENANCE.json](ARTICLE_PROVENANCE.json) records the canonical source hash.

[Editable signed TeX](paper.tex) · [Standalone TeX source ZIP](paper-source.zip). The Zenodo record retains earlier immutable editions; use the `author-v4.pdf` attachment for the current paper. Previous signed edition: [10.5281/zenodo.23272758](https://doi.org/10.5281/zenodo.23272758); earlier signed edition: [10.5281/zenodo.23272595](https://doi.org/10.5281/zenodo.23272595); original edition: [10.5281/zenodo.23272362](https://doi.org/10.5281/zenodo.23272362).

[aiXiv:2610.01490](https://aixiv.online/abs/2610.01490) is the author-submitted edition, using CC BY-NC-ND 4.0 with explicit author authorization. Its PDF is byte-identical to the signed PDF above; the existing immutable DOI record is unchanged. No agent sessions were uploaded. The paper cites published external Gaussian isoperimetric inputs and does not claim a self-contained complete Lean proof.
