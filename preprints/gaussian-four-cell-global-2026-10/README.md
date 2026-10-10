# Four equal Gaussian cells: covariance deformation and tetrahedral rigidity

**Public preprint; not peer reviewed.** Version DOI: [10.5281/zenodo.23272362](https://doi.org/10.5281/zenodo.23272362).

For every measurable or fractional partition of standard Gaussian space into four equal-mass cells, the sum of squared first moments is at most

\[12(\arctan\sqrt 2)^2/\pi^3.\]

Equality holds exactly for central regular-tetrahedral winning cones, up to null sets, orthogonal maps, relabeling, and cylindrical extension. The result settles Heilman’s 2014 Conjecture 3 in dimension three and the equal-mass four-cell case of the 2019 Conjecture 1.16, with the imported Gaussian multi-bubble theorem stated explicitly. The broader arbitrary-mass conjecture is not claimed.

- [PDF](paper.pdf)
- [Canonical source package and full proof audit](../../research/gaussian-balanced-four-global/README.md)
- [Editable manuscript](../../research/gaussian-balanced-four-global/paper.md)
- [Audit and verification scope](../../research/gaussian-balanced-four-global/AUDIT.md)

The exact checker uses rational arithmetic for finite diagnostics (720 matrix cases and 3,087 local identity cases), with two negative controls. Eight Lean exports cover scalar algebra only; Gaussian integration, the imported perimeter theorem, deformation flow, and the complete analytic endpoint are not Lean-formalized. Reproduction from the canonical package:

```sh
cd research/gaussian-balanced-four-global
python3 check_exact.py
python3 verify.py
```

No external human peer review or historical-priority claim is made. Research and manuscript preparation used AI assistance; no external funding. Original material is reserved unless a file states another license.
