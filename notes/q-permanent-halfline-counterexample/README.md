# q-permanent half-line monotonicity counterexample

Research note and reproducibility package, 8 October 2026.

## Result

An exact real positive-definite 4-by-4 rational matrix refutes da Fonseca's half-line q-permanent monotonicity extension. Order four is minimal. For every fixed t > 1, a real positive-definite correlation matrix can be chosen with negative derivative at t, including one with rational entries and no zero off-diagonal entries.

**Bapat's original conjecture on [-1,1] is not resolved by this work.**

## Read and reproduce

- [PROOF.md](PROOF.md): complete proof, scope, minimality and general construction.
- [SOURCE_AUDIT.md](SOURCE_AUDIT.md): source interpretation and bounded literature search.
- [verify_exact.py](verify_exact.py) and [EXACT_CERTIFICATE.json](EXACT_CERTIFICATE.json): main exact rational verifier and its output.
- [audit/AUDIT.md](audit/AUDIT.md): independent mathematical and arithmetic audit.
- [audit/verify_exact.py](audit/verify_exact.py) and [audit/exact_results.json](audit/exact_results.json): independent enumeration of all 24 permutations and all 15 principal minors.
- [audit/verify_family.py](audit/verify_family.py) and [audit/family_results.json](audit/family_results.json): independent family checks and an explicit dense rational variant.
- [MANIFEST.json](MANIFEST.json) and [SHA256SUMS](SHA256SUMS): complete file inventory and integrity checks.

Run from this directory with Python 3 and no third-party dependencies:

```sh
python3 verify_exact.py
python3 audit/verify_exact.py
python3 audit/verify_family.py
sha256sum -c SHA256SUMS
```

The scripts regenerate the three JSON certificates beside their respective scripts. The finite checks complement the symbolic proof of the universal theorem.

## Limits

The original 2010 article was inspected through a complete journal-mirror OCR; its exact endpoint inequality glyph was not verified from the page image. The 2018 author manuscript and 2020 published restatement independently establish the target, and the example refutes either endpoint version. The bounded literature search located no prior matching disproof, which is not a guarantee of worldwide novelty. No human peer review or formal Lean verification is claimed.
