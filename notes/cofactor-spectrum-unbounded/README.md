# Unbounded normalized cofactor spectra

This package proves a complete unboundedness theorem. For every R>0 there is a
complex rank-two correlation matrix A such that both

    lambda_max(C(A))/per A > R,
    lambda_max(Re C(A))/per A > R,

where C(A)_ij=A_ij per A(i|j), deleting row i and column j. Positive-definite
correlation versions follow by continuity. The proof does not give a rate in
the matrix order.

The R=1 cofactor conjecture was already disproved by Drury. The theorem here
rules out every dimension-independent constant. It is not a solution of Lieb's
permanental-dominance conjecture. SOURCE_AUDIT.md distinguishes the cofactor
ratio from previously known unbounded Hadamard-product and full Schur-power
ratios, and records the limits of the literature check.

## Read

- unbounded_cofactor_spectra.pdf: four-page self-contained mathematical paper
- unbounded_cofactor_spectra.tex: editable source
- PROOF.md: expanded proof with explicit quantifiers and limiting steps
- SOURCE_AUDIT.md: prior work, current versions, access limits, and data provenance
- INDEPENDENT_AUDIT.md: final mathematical and exact-computation review

## Reproduce the optional finite certificate

Run with standard Python 3, without installing packages:

    python verify_witness.py
    python verify_witness_independently.py

The first program rebuilds all omitted-factor products. The second uses a
single-pass marked-product recurrence and does not call the first algorithm.
Both verify using exact integers that the supplied Gaussian-integer rows and
Rayleigh vector satisfy

    2.69 < w* C(A) w / (per(A) ||w||^2) < 2.70.

witness_n200.csv contains all inputs. EXACT_WITNESS_RESULT.json gives the full
integer quantities. n200_independent_result.json records the independent
algorithm's agreement. The Gram rows are reused from the companion Bapat
q-permanent construction in this research project; the cofactor direction is
separately chosen. No independent discovery of those Gram rows is claimed.

The finite certificate illustrates the conventions and a numerical scale.
The analytic proof of unboundedness does not depend on it.

## Review and scope

The proof and final TeX/PDF passed an independent mathematical review within
this research workflow. The exact certificate also passed two distinct integer
algorithms. This is not a claim of external journal peer review or exhaustive
novelty verification. No Lean formalization is included or asserted.

Only original proof artifacts, programs, certificate data, review, and source
links are packaged. Third-party papers and extracted full texts are excluded.
