# Verification of the positive sextic envelope

## Completed original mathematical audit

The corrected accompanying ZIP retains unchanged the complete original independent `AUDIT.md` and `SIGNOFF.json`. The audit accepts the full invariant and the conclusion

2.8534 < Gamma_C <= exp(104867/100000) < 2.85386

at alpha=431/10000, beta=9/2500, gamma=197/100000, with no mathematical correction required.

- Finite rectangles: all 19,900 dimension pairs 1<=r<=s<=199; submitted and separate exact supporting-plane reconstructions pass normally and under -O, with uniform upper margin below -1/1000000
- Imbalanced tails: all 157,872 cells covering every real z in [0,1/200] for every r=1,...,199; exact no-gap/no-overlap coverage; maximum depth 11; submitted and separate full normal/-O replays pass with uniform upper margin below -1/10000000000
- Both-large dimensions: all r,s>=200 and all h,j>0; separate rational Bernstein and exponential-endpoint calculations pass; product violation is strictly below -13/100000
- Structural and symbolic review: finite-expression grammar, invertible affine-hull equivalence, join sign, harmonic/power-mean reductions, 14 symbolic identities, factorial corrections, and the all-dimensional spectral argument checked
- Corruption and sample tests: 14 distinct corrupt fixtures rejected in ordinary and optimized modes, hence 28 cases; 106,892 supplementary exact sample checks pass
- Inherited lower construction: exact ancestor checker/certificate replayed in both modes, including four corruption controls; no new lower result

The independent implementation imports no candidate module. It uses separate interval operations, 30-term rational logarithms with 112-bit outward rounding, generic even-power moments, and cancellation by polynomial subtraction and division. Its large check uses a different Bernstein conversion and an 18-term rate bound. The adversarial tester necessarily invokes submitted checkers against corrupt copies; that does not erase the independence of the proof reimplementation.

Finite certificate SHA-256:
`f1015d270d337af16de579c068ad6d66237fb0f5b8038c031f41fd6d2abbe4c7`

Full tail certificate SHA-256:
`73f04d318c8dba38cabef5582892a597f6bb5ae704aca178147b341e66b61b1a`

## Reader edition and reproducibility

The public-facing note is an editorial assembly of the frozen proof, with explicit definitions, imported-calculus attribution, and a short proof of the inherited spectral identity. The original ZIP is retained unchanged separately. The corrected public ZIP retains all 143 original entries unchanged and adds precisely the two recovered nested ancestor manifests, bringing the ancestor-source count from 61 to 63. All submitted checker sources, both full certificates, original audit files, and historical root manifests retain their original bytes. `ARCHIVE_INVENTORY.json` covers every one of the corrected ZIP's 145 entries and records both archive hashes and exact additions. Four pinned ancestor dependency files are supplied without modification so the lower certificate can also be replayed offline.

`verify_release.py` distinguishes integrity-only checks, quick replay excluding full tails, and a new full normal/-O replay. Existing completed full audit reports are historical evidence; an integrity-only or quick release check does not claim to repeat their complete tail arithmetic. `--full` is the reproducible way to rerun it.

This is exact arithmetic verification with a separate model-conducted mathematical audit. It is not human peer review or proof-assistant formalization. The analytic calculus, Robbins, Jensen/Hölder, power means, Stirling, elementary logarithm, and Machin inputs remain ordinary mathematical arguments or explicitly attributed prior results. No optimality, unrestricted-body, or first-priority claim is made.
