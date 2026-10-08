# A counterexample to Billey–Swanson Conjecture 48

First public source version: 8 October 2026 UTC.

The polynomial **F(q) = (Φ₄(q) Φ₉(q) Φ₂₅(q) Φ₃₀(q))⁶** is a nonconstant basic cyclotomic generating function of degree 216. Its 217 integer coefficients are all positive, strictly increase up to the unique peak at degree 108, and then strictly decrease. No prime-order cyclotomic polynomial Φₚ divides F. It therefore contradicts **Conjecture 48 as published** in Sara C. Billey and Joshua P. Swanson, *Cyclotomic Generating Functions*, Electronic Journal of Combinatorics 31(4) (2024), P4.4, [DOI 10.37236/12687](https://doi.org/10.37236/12687).

## Complete proof and exact checks

- [English proof](cyclotomic_prime_factor_20261008/proof.md), including all 109 positive centered q-integer weights and the argument excluding every prime-order factor.
- [Primary standard-library checker](cyclotomic_prime_factor_20261008/verify_counterexample.py) and [full integer certificate](cyclotomic_prime_factor_20261008/certificate.json).
- [Independent proof and review](cyclotomic_independent_20261008/independent_proof.md), [independent checker](cyclotomic_independent_20261008/independent_verify.py), and [independent certificate](cyclotomic_independent_20261008/independent_certificate.json). The independent computation rebuilt the cyclotomic factors without reading, importing, or running the primary script, then compared every coefficient, weight, and prime remainder.
- [Primary source audit](cyclotomic_prime_factor_20261008/source_audit.json) and [independent source audit](cyclotomic_independent_20261008/independent_source_audit.json) record the publication scope and limited literature search.

There are 109 positive centered weights, including the constant weight 1. The 108 actual adjacent differences before the peak have minimum 5. The unique peak coefficient is 11434392 and the coefficient sum is 729000000.

## Reproduce

Use Python 3.9 or later and only its standard library. Keep the two source directories adjacent as supplied. In a writable copy of this package run:

```sh
python3 -B cyclotomic_prime_factor_20261008/verify_counterexample.py
python3 -B cyclotomic_independent_20261008/independent_verify.py
sha256sum --check SHA256SUMS
```

Run without `-O`; both programs use assertions and regenerate their adjacent certificates. Both commands were run in an isolated copy of this publication layout and reproduced both certificates byte-for-byte. The independent program checks the frozen primary certificate only after completing its own exact calculations. No floating-point roots or external algebra package are needed.

## Review status and scope

The full written counterexample and independent exact reconstruction passed review before publication. This is an independent AI-agent mathematical/computational review, not a claim of external human peer review. The original source documents and logs are retained unchanged; the primary proof's “Independent review is pending” sentence records its earlier drafting status and is superseded by this current status and the independent report.

The conjecture asks for a **prime-order** factor Φₚ. The neighboring prime-power result is compatible with this example, which contains Φ₄, Φ₉, and Φ₂₅. No minimum-degree claim, certified historical priority, Lean verification, or digital signature is asserted. The source audit's failure to find an earlier resolution is a limited search result, not a guarantee of originality. No license or personal authorship assignment is added.

[MANIFEST.json](MANIFEST.json) binds the exact version and input identities; [SHA256SUMS](SHA256SUMS) binds the publication files. A separate GitHub Release may record this source commit without altering these proofs.
