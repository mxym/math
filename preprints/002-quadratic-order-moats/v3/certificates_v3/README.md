# Version 3 exact certificate files

These standard-library Python programs check finite candidate data. They do not run an unbounded search. The mathematical statements, input semantics, scalar-period proof, restoration proof, and limitations are in Section 12 of the version 3 manuscript.

## Run the checks

From this directory, run without Python optimization flags:

- `python test_certificates.py` — 41 norm-prime checks and four finite-lift reconstructions
- `python test_principal_ideals.py` — 24 general-principal checks, including the Q30 rejection walk
- `python independent_checks.py` — separate norm-prime lift reconstruction
- `python independent_principal_checks.py` — direct multiplication-image reconstruction, independent of adjugate membership code
- `python independent_principal_arithmetic.py` — 184 exact membership and minimal-period checks across five order models

The two production checkers use explicit validation errors; optimization does not disable those checks. The test and independent-audit scripts use assertions and must run without `-O`.

## Complete data

- `gaussian_four_steps.json`: Gaussian F4, Q=2, B=1, full bound 20
- `sqrt2_four_steps.json`: real quadratic F4, Q=14, B=6, full bound 179200
- `gaussian_eight_steps.json`: Gaussian F8, Q=130, B=580, full bound 92820
- `sqrt2_eight_steps.json`: real quadratic F8, Q=14, B=6, full bound 351232
- `gaussian_eight_steps_principal.json`: the successful Q130 certificate in the broader principal-ideal format
- `gaussian_eight_steps_principal_rejected.json`: failed Q30 candidate, with its complete 38-step nonzero-voltage walk

F4 consists of the four axial unit coefficient steps. F8 consists of all nonzero coefficient vectors in {-1,0,1}². Full bounds include exceptional irreducibles and are conservative. B is the exact largest avoiding-component size, except that a positive convention of B=1 is used for an empty quotient. Saved statistics are recomputed; the positive proof certificate is the complete allowed set with its integer potentials.

The Gaussian JSON files also retain a larger generic selected-norm bound. Their stronger `finite_exception_component_bound` values are the full bounds listed above. The real examples use the selected-norm bound and do not treat their infinitely many unit associates as a finite set.

## Independence and limits

`prime_element_checker.py` and `principal_ideal_checker.py` are separate new formats and do not alter the old split-pair implementation. The former requires prime absolute norms but permits repeated primes and ramification. The latter permits every nonzero nonunit generator, using both adjugate congruences and the scalar period |N(alpha)|/gcd(a,b).

Both implementations cap inputs at 32 generators, 64 steps, 65536 quotient cells, and 128-bit input integers. The norm-prime implementation also caps claimed primes at 1000000. These are implementation budgets, not restrictions on the mathematical theorems. No general theorem, formal executable verification, optimality claim, or priority conclusion follows from passing finite tests alone.

The first two independent scripts retain their checked arithmetic and graph logic; only their file-location configuration was changed to make this directory self-contained. The 184-generator script is an additional bounded reproduction of the direct multiplication-image stress test. No independent script imports either production checker.
