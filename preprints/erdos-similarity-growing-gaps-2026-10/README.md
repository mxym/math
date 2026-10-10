# Erdős similarity: growing logarithmic gaps

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology.
ORCID: [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).

[Version DOI: 10.5281/zenodo.23272807](https://doi.org/10.5281/zenodo.23272807) · [Zenodo record](https://zenodo.org/records/23272807)

This preprint proves positive-measure affine non-universality for every prescribed countable family of positive null sequences satisfying the late-annulus filling condition

```text
z_{n+1} - z_n = o(log log z_n)
```

and for the stated intermittent-window extension. It includes sequences whose adjacent ratios tend to zero and whose occupied logarithmic bins have zero upper Banach density. The full Erdős similarity conjecture, including `2^(-n^2)` and `2^(-2^n)`, remains open.

The [canonical package](../../research/erdos-similarity-growing-gaps/README.md) contains the complete written proof, scope limits, prior-work comparison, exact finite checker, and Lean replay. The formalization now includes the finite Bernoulli routing calculation and the complete conditional countable blocker assembly (closed periodic complement, measure estimate, empty interior, and infinite-tail transfer). The existence of those blockers from `WindowFilling`, and hence the unconditional infinite analytic theorem, remains explicitly written proof rather than a Lean theorem. No external human peer review or worldwide priority claim is made.

Reproduction from the canonical package:

```sh
python3 -B research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B -O research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B research/erdos-similarity-growing-gaps/verify.py
```

AI-assisted research is disclosed in the paper and repository. Original material follows the repository reserved-rights policy.


The previous signed edition remains at https://doi.org/10.5281/zenodo.23272596; the original frozen edition remains at https://doi.org/10.5281/zenodo.23272460. This directory uses the signed author edition. Only archive binding metadata was corrected in this v4 edition; the author/affiliation/ORCID, bibliography, research-method disclosure and PDF metadata remain unchanged from v3. [ARTICLE_PROVENANCE.json](ARTICLE_PROVENANCE.json) records the canonical source hash.

[Editable signed TeX](paper.tex) · [Standalone TeX source ZIP](paper-source.zip). The Zenodo record retains earlier immutable editions; use the `author-v4.pdf` attachment for the current paper. Previous signed edition: [10.5281/zenodo.23272759](https://doi.org/10.5281/zenodo.23272759); earlier signed edition: [10.5281/zenodo.23272596](https://doi.org/10.5281/zenodo.23272596); original edition: [10.5281/zenodo.23272460](https://doi.org/10.5281/zenodo.23272460).
