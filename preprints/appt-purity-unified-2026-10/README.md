# Unified APPT purity results: exact qutrit theorem and higher-dimensional asymptotics

This is a new expanded manuscript combining the exact qutrit--qudit APPT purity theorem with the higher-dimensional counterexample and unrestricted asymptotic law. The earlier immutable qutrit-only preprint remains unchanged:

- DOI: https://doi.org/10.5281/zenodo.23269470
- Lean proof release: https://github.com/mxym/math/releases/tag/appt-qutrit-purity-complete-v1

## Main results

1. For every `n >= 3`, the exact maximum APPT purity on `C^3 tensor C^n` is `(3n+8)/(3n+2)^2` for `3 <= n <= 8`, and `3/(8n)` for `n >= 9`, with actual attaining states.
2. The arbitrary-dimensional Ahiable--Kothakonda--Winter purity formula (Conjecture 6.7) is false. The state
   `diag(41, 17 [146 copies], 15 [233 copies]) / 6018`
   on `C^10 tensor C^38` is APPT for every global unitary and has purity strictly above both proposed values.
3. If `Pmax(m,n)` is the unrestricted APPT maximum and `D=mn`, then the analytic proof establishes, uniformly for integers `n >= m` as `m -> infinity`,
   `D^2 (Pmax(m,n)-1/D) ~ max(8, 4+n/m)`.
   In particular, `Pmax(m,m)=m^(-2)+8m^(-4)+o(m^(-4))`.

## Proof status

The qutrit theorem is completely formalized in Lean 4.34.1 and independently replayed at trust level zero in the immutable release above. The higher-dimensional counterexample and asymptotic law are written analytic proofs supported by exact rational/integer checkers. They are not included in the qutrit Lean certificate and have not undergone external peer review. The checkers validate algebraic identities, finite regressions, and deliberate negative controls; they are not substitutes for the all-unitary and asymptotic arguments.

The paper does not claim exact finite-dimensional maxima in general dimensions, classification of maximizers, a result for fixed smaller dimension `m`, or equality of APPT and absolute separability.

## Reproduction

From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cd supplementary
python3 check.py --report ../verification/higher-dimensional-exact-checks.json
python3 check_asymptotic.py
python3 check_mesoscopic.py --report ../verification/higher-dimensional-mesoscopic-checks.json
```

The exact qutrit formalization is reproduced from its separate package and release. The `supplementary/` directory contains the detailed analytic proof files and standard-library checkers for the higher-dimensional part. `SOURCE_HASHES.json` binds the manuscript and supplementary sources for this version.

This manuscript is a preprint. It has no arXiv identifier or version DOI yet. No historical first-priority claim is made.
