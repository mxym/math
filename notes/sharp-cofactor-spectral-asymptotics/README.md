# Sharp cofactor extrema: stage package

This package proves sharp logarithmic asymptotics for permanental cofactor
spectral amplification and the sharp rank-two ramp/endpoint limsup constants.
Lieb's arbitrary-subgroup character conjecture and Marcus's block-permanent
conjecture remain unresolved in this investigation. See STAGE_SUMMARY.md for
the precise reason for closing this route and the proved exclusion ranges.

## Read

- sharp_cofactor_extrema.pdf / .tex: the complete self-contained manuscript
- PROOF.md: text rendering of the same TeX proof
- SOURCE_AUDIT.md: prior inputs, access limits, and finite novelty-search scope
- STAGE_SUMMARY.md: original target, completed results, and remaining bridges

The real-Rayleigh extremum allows complex Hermitian A. It is not an extremum
over real matrices. The logarithmic theorem holds for every sufficiently large
order; the ramp/endpoint sharpness is stated as a limsup. Positive-definite
perturbations do not retain rank two for orders above two.

## Reproduce the finite certificates

Python 3.10 or later, standard library only; no installation or network needed.
Run from this directory:

    python verify_dyadic_cofactor_family.py --K 8 --C 7
    python verify_dyadic_cofactor_family.py --K 10 --C 5
    python verify_dyadic_independently.py
    python verify_stage_bounds.py

The first program constructs integer-scaled dyadic polynomial coefficients.
The second independently uses a marked-product recurrence and recursive Fock
weights, then compares all five exact integer quantities. It also computes the
order-eight integer Gram matrix's permanent and all deleted cofactors directly.
The third checks the rank-two factorial exclusion thresholds using rational
bounds, not floating point. All three reject Python optimization modes
(-O, -OO, PYTHONOPTIMIZE=1/2), which would disable assertions.

The JSON files contain full exact quantities and concise certified intervals.
The log files are recorded normal runs. SELF_REVIEW.md records the independent-
algorithm match, negative-mode checks, and document validation. These finite
calculations illustrate the algebraic formulas; the asymptotic theorems are
proved analytically and do not depend on numerical searching.

## Compile the paper

A standard LaTeX installation with amsmath, amssymb, amsthm, mathtools, geometry,
and hyperref is sufficient. Run pdflatex twice on sharp_cofactor_extrema.tex.
PDF byte identity can depend on TeX versions and timestamps; the mathematical
source and exact certificate outputs are the reproducibility targets.

Only self-written manuscripts, scripts, and computed outputs are included.
No downloaded third-party full text is redistributed. A private transfer or
review of this package is not public publication; public placement and release
are a separate coordinated action.
