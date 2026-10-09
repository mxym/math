# Pure-state ECQC: complete prime-dimensional classification

**Author:** Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. **Email:** mxymmxym1@gmail.com. **ORCID:** 0009-0000-3864-3536.

## Result

For prime local dimension `p`, the extended complementary-quantum correlation inequality holds for **every pure state and every complete MUB family if and only if p = 2**. For every odd prime it fails even with identical canonical local bases and with full-Schmidt-rank pure states.

At `p = 3`, the explicit real state

```text
(|01> + |02> - |10> - |20>)/2
```

has quantum mutual information exactly **2 bits**. Every one of the four canonical MUB measurements gives exactly **1 bit** of classical mutual information. The ECQC minimization retains three terms, hence gives **3 bits > 2 bits**. The density matrix and every Born table are exact, not numerical surrogates.

At `p = 5`, the real singlet in the odd-parity subspace, explicitly given in the paper, yields **5 bits > 2 bits**. These states attain the universal pure-state ratio upper bound `p/2`, giving sharp ratios `3/2` and `5/2` in those two dimensions. The upper bound uses the established Holevo theorem; the counterexamples do not depend on it.

For every prime `p >= 5`, a separate embedded Bell family has score `p J_p` and quantum mutual information `2 log(2)`. A polynomial minorant and exact Fourier moments prove the excess is at least **1/576 in natural units**, uniformly over all such primes. Moreover `J_p -> 1-log(2)`, so the ratio diverges with the dimension while entanglement stays at one ebit. This is an analytic all-prime proof, not an extrapolation of finite computation.

A full-Schmidt-rank pure qutrit witness has integer amplitude matrix

```text
W = [[ 0,  5,  5],
     [-5,  1, -1],
     [-5, -1,  1]],
|chi> = sum W[x,y] |xy> / sqrt(104).
```

Its exact entropy excess equals

```text
log(2^57 * 5^100 * 13^26 / 3^243) / 26 > 0.
```

The final sign is certified by integer arithmetic. Its two marginal spectra are `(25/52,25/52,1/26)`; the global state remains pure (rank one).

## Relation to previous work

The original ECQC statement and the separately posed pure-state question are in Hasan Iqbal, arXiv:2509.08286v2, Conjecture 3.1 / equation (6) and Section 5, DOI [10.1007/s11128-026-05258-2](https://doi.org/10.1007/s11128-026-05258-2).

Wang, Wang, and Chen, [arXiv:2608.03828v2](https://arxiv.org/abs/2608.03828), already refuted **unrestricted** ECQC with a mixed classical–classical state at dimension seven and proved unbounded mixed-state overrun. This package does **not** claim the first disproof of unrestricted ECQC. It resolves the **pure-state** question and its prime-dimensional validity classification, with sharp low-dimensional ratios and explicit full-Schmidt-rank witnesses. Literature-search limitations are recorded in [LITERATURE.md](LITERATURE.md).


**Frozen publication record:** DOI [10.5281/zenodo.23256948](https://doi.org/10.5281/zenodo.23256948); immutable GitHub Release: https://github.com/mxym/math/releases/tag/ecqc-pure-state-classification-v1. The archive is version 1.0 and is bound to commit `c0a1085e360604a1f8f274290eb1556202a315ab`.

## Files and verification

- [paper.pdf](paper.pdf) / [paper.tex](paper.tex): complete written proofs, definitions, boundaries, cited dependencies, and scope.
- [QUTRIT_EXACT.md](QUTRIT_EXACT.md): standalone elementary proof first recorded in commit `038aba8eb24ecd446f2ba5f7389f94abd364bdf7`.
- [check_low_dimensions.py](check_low_dimensions.py): reconstructs the actual qutrit/ququint bases, density matrices, partial traces, spectral identities, and Born probabilities. It verifies exact symbolic entropy identities and the integer certificate for the full-Schmidt-rank qutrit.
- [check_exact.py](check_exact.py): separate cyclotomic replay of the embedded Bell construction at `p=5`, plus exact polynomial/moment/rational identities used in the analytic all-prime proof.
- [check_intervals.py](check_intervals.py): independent exact rational entropy intervals for the embedded Bell state and an additional full-Schmidt-rank five-dimensional witness. Its logarithmic remainder is proved, not assumed from a numerical library. See [the supplementary proof](SUPPLEMENTARY_FIVE_DIMENSIONAL.md).
- [test_negative_controls.py](test_negative_controls.py): selected corrupted states and certificates must be rejected.
- `*-check.json`, `negative-controls.json`: recorded replay results; regenerate them rather than trusting the stored `PASS` strings.
- [AUDIT.md](AUDIT.md): proof dependency map, self-review, and verification limitations.

```bash
python3 check_low_dimensions.py
python3 check_exact.py
python3 check_intervals.py
python3 test_negative_controls.py
latexmk -pdf -halt-on-error paper.tex
```

Python 3.10+ and the standard library suffice for all proof checkers. Run without `-O`; optimized execution is rejected. TeX compilation requires a standard LaTeX installation with the packages named in `paper.tex`.

## Formalization and remaining questions

This version has complete written proofs and exact replayable checkers. The explicit pure qutrit counterexample now has a [complete Lean proof of the actual quantum statement](../../formalizations/ecqc-pure-qutrit-counterexample/README.md): density validity, both actual partial traces, complete MUBs, Born expectations, actual spectral and Shannon entropies, the original attained minimum, and strict violation. The fresh verification rebuilds eight own modules and replays the 35,401-declaration closure of 73 roots from an empty kernel at trust level zero, with only propext, Classical.choice, and Quot.sound. **The whole prime-dimensional classification is still not labeled Lean-complete.** Holevo, the qubit positive theorem, sharp-ratio optimality, five-dimensional constructions, full-Schmidt-rank strengthening, and all-prime analytic estimates remain outside this certificate. See the updated manuscript Section 5.2 and the package proof supplement for exact scope.

The sharp ratio for every prime `p >= 7`, a classification of all equality states, an optimal repaired ECQC inequality, and a classification of mixed states are not settled here. The pure-state prime-dimensional validity question itself is settled. No new experiment or experimental confirmation is claimed.

## Replay integrity correction

The immutable v1 source snapshots retain an outdated `SHA256SUMS` after the Lean-scope documentation update. The exact checker sources and their results were unchanged. The current manifest is repaired, and [the CI repair audit](../../verification/ecqc-replay-ci-2026-10-09/README.md) records the original discrepancies and fresh replay. A maintenance supplement is published at [ecqc-exact-replay-integrity-v1.1.1](https://github.com/mxym/math/releases/tag/ecqc-exact-replay-integrity-v1.1.1); frozen v1 files are not modified.

## Provenance and rights

AI assisted research, discovery computation, derivation, coding, literature checking, writing, and self-audit. Numerical optimization was discovery-only and is not a proof dependency. There was no external funding and no external professional mathematical peer review. Independent implementations mean separate code paths within this project, not independent human review.

Copyright (c) 2026 Yongxian Zhang. All rights reserved for separately authored original material. Existing repository and cited-source licenses are preserved; no new blanket license is applied to inherited material. DOI and release timestamps, when assigned, are not evidence of mathematical priority.
