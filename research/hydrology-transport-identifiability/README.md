# Hydrological model identifiability through transport contrasts

**Research checkpoint — written proofs, exact rational checks, synthetic tests.**
Not a Lean formalization, field validation, established novel discovery, or
externally reviewed publication. No forecast superiority claim is made.

## Main result

For a specified conservative, perfectly mixed, finite compartment network,
water alone can leave continuously many physically valid internal flow models
indistinguishable even with exact discharge, evapotranspiration and total storage.
An ideal water-following label preserves this ambiguity. A tracer with a distinct
compartment-specific loss contrast can instead identify the complete unknown
affine network up to permutation under minimality and rich controlled experiments.

`THEOREMS.md` contains five statements with written proofs: constructive unknown-
network identification; complete anchored local equivalence dimension; the
static/affine/tracer distinction; an exact four-store physical witness; and a
finite-dwell reconstruction avoiding response derivatives under an explicit
anti-aliasing bound. `NOVELTY.md` discloses close prior art and limits the claim.

## Evidence

- `exact.py`: standard-library rational arithmetic; 496 equalities, 72 Bernstein
  coefficients for an entire physical parameter rectangle, 20 reconstruction
  fixtures in two to six stores, and seven deliberately invalid controls.
- `independent.py`: separately implemented polynomial convolution, 24 exact
  quadratic minima, determinant checks and tracer fingerprint; no imports from
  the primary checker.
- `simulate.py`: 730 synthetic days, all-forcing-equivalent water models,
  differing internal fluxes, a tracer-partition sweep, and 20 one-parameter
  noisy fits. This is not a full-network noisy calibration.
- `design.py`: 61 prespecified synthetic demand-onset schedules, scored in the
  three water-invisible sensitivity directions. The best within this finite
  family improves the weakest Fisher eigenvalue by about 89 times.
- `finite_time.py`: noiseless sampled-kernel reconstruction without supplying
  the true rates or contrast eigenvalues to the estimator. At 10-day baseline
  spacing and 1-day middle dwell, all coefficient errors are below 8e-11 in
  the two four-store examples. Conditioning remains poor (~2.3e6).

The rational checks certify their finite algebraic statements, NOT every general
analytic theorem. The written conjugacy argument, not simulated input coverage,
establishes equality for all forcing histories. All numerical data are generated
synthetically; there are no observations of a real catchment in this package.

## Reproduce

From this directory with Python 3.11 or later:

```sh
python3 reproduce.py --output-dir /tmp/hydrology-exact-check
```

The output directory must not exist. The script verifies source hashes, copies
sources to a clean directory, runs both exact checkers normally and with Python
optimization, and requires identical results. No third-party packages are needed.

For the synthetic experiments:

```sh
python3 -m pip install -r requirements-numerical.txt
python3 reproduce.py --numerical --output-dir /tmp/hydrology-full-check
```

Numerical pins are NumPy 2.3.5 and SciPy 1.17.0; the recorded local host uses
Python 3.13.5. Small floating-point changes on other platforms are possible.
SHA256SUMS.json binds source/configuration bytes. Receipts bind result files
separately. A scoped GitHub workflow checks the dependency-free exact branch;
its success is not a claim to have formally verified the written theorems.

## Scope limitations

Fixed finite dimension, baseline controllability and observability, shared water/
tracer internal transport, known input histories, perfect mixing, affine demand
dependence and distinct transport contrasts are substantive assumptions. Deep
stores with identical or zero ET contrasts remain a key unresolved practical case.
Unknown reactions, uptake, sorption, nonlinear storage dependence, irregular
field data and noisy full-network inference are not solved here.

A professor-facing interpretation and experiments are in `EXPERIMENTS.md`.
No release, DOI, or priority claim is justified at this checkpoint.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Original additions retain all rights not otherwise granted. Existing repository
notices and third-party licenses are preserved. Classical results are credited.
