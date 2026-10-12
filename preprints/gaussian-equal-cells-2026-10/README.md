# Equal Gaussian cells: the sharp simplex first-moment theorem

**Published revised preprint, version 2.0: https://doi.org/10.5281/zenodo.23250730.** Previous version: https://doi.org/10.5281/zenodo.23248377. All three public attachments were anonymously downloaded and SHA256-checked; DataCite registration is findable. This has not been submitted to arXiv. [Public archive audit](../../releases/gaussian-preprint-20261008/README.md).

Author: Yongxian Zhang (张永贤). School of Computer Science and Engineering, South China University of Technology. ORCID: https://orcid.org/0009-0000-3864-3536. Correspondence: mxymmxym1@gmail.com.

[Seven-page paper](paper.pdf) · [Standalone LaTeX upload ZIP](paper-source.zip) · [TeX](paper.tex) · [Audit](AUDIT.md).

## Mathematical scope

For every k ≥ 2 and every measurable standard Gaussian partition into k equal-mass cells, the sum of squared first moments is at most `(E max_{i≤k} Z_i)^2/(k−1)`. For ambient dimension d ≥ k−1, equality holds exactly for central regular-simplex cones, extended cylindrically, up to null sets, rotations and relabeling. For d < k−1 the bound is strictly unattained; the exact lower-dimensional optimum is not claimed. Fractional partitions are included. An exact nonnegative covariance-deficit integral is proved.

The proof uses the **published Milman–Neeman Gaussian multi-bubble theorem**, https://doi.org/10.4007/annals.2022.195.1.2, followed by the paper's Gaussian flux, price-Hessian and radial differential comparison. This is an ordinary mathematical proof using a proved external theorem. Complete Lean formalization is not a publication prerequisite and is not claimed here.

## Proof and verification boundaries

The expanded derivation and internal mathematical review are retained in [the research package](../../research/gaussian-balanced-simplex-all-k/README.md). The publication is based on PR #7, commit `dd15765aa0854388251b552a31df9e750bd36bb0`; signed authorship, resolved bibliography links and AI disclosures are added without changing the mathematical statement. [Source provenance](SOURCE_PROVENANCE.json).

The research package has eight earlier partial Lean exports. The [separate Lean development, PR #3](https://github.com/mxym/math/pull/3) has additional analytic modules, with its geometric perimeter lower bound still an explicit premise. [CI 37860815416](https://github.com/mxym/math/actions/runs/37860815416) passed at `e408d21e4bffd77c198cf36f9a821daf83bc9596`; it verifies only its selected partial Lean targets and is not a certificate of the unconditional main theorem. The old empty-kernel audit covers its original 53 matching modules, not the complete later development.

No external human peer review, journal acceptance, arXiv submission or worldwide priority is claimed. The proof does not establish positive-correlation noise stability, an arbitrary-mass simplex statement or a sharp metric stability constant. AI use for research and manuscript preparation is disclosed separately; no external funding was received.

## Reproduction

Run `python3 build.py` here with Python, pdfLaTeX and Poppler. It compiles the standalone TeX three times in a fresh temporary directory, rejects unresolved references, missing glyphs, overflow and unembedded fonts, and creates the upload ZIP. It checks typesetting, not the mathematics. Run the research package's `python3 verify.py` separately for frozen source integrity and finite diagnostics.

Existing licenses and third-party notices remain in force. Previously unlicensed original material remains all rights reserved; public access is not a new blanket license.
