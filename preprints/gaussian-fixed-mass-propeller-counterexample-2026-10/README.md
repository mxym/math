# A facet-exchange counterexample to the fixed-mass regular-simplex conjecture

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology.
ORCID: [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536). Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com).

[Version DOI: 10.5281/zenodo.23272491](https://doi.org/10.5281/zenodo.23272491) · [Zenodo record](https://zenodo.org/records/23272491)

This preprint gives a written counterexample to the arbitrary-positive-mass statement of Heilman, *Stable Gaussian Minimal Bubbles*, arXiv:1901.03934v1, Conjecture 1.16. For every `0<p<1/4`, the mass vector `(p,(1-p)/3,(1-p)/3,(1-p)/3)` has a strict non-regular improvement. The construction uses exact Gaussian facet inequalities and an equal-measure ball exchange, and rules out every regular-tetrahedral candidate with those masses. It does not refute the equal-mass tetrahedral problem.

The [canonical package](../../research/gaussian-fixed-mass-propeller-counterexample/README.md) contains the complete written proof, exact `Q(sqrt(2))` diagnostics, partial Lean algebra, prior-work comparison and explicit limits. No numerical Gaussian integral or solver output is used as a proof premise; the Gaussian optimizer-existence and geometric arguments are written mathematics, not a complete Lean formalization. No external human peer review or worldwide priority claim is made.

Reproduction from the canonical package:

```sh
python3 -B research/gaussian-fixed-mass-propeller-counterexample/checks/exact.py
python3 -B -O research/gaussian-fixed-mass-propeller-counterexample/checks/exact.py
python3 -B research/gaussian-fixed-mass-propeller-counterexample/verify.py
```

AI-assisted research is disclosed in the paper and repository. Original material follows the repository reserved-rights policy.
