# ECQC: full-rank equality and every pure stabilizer state

**Author:** Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. **Email:** mxymmxym1@gmail.com. **ORCID:** 0009-0000-3864-3536.

## Exact conclusions

Fix an odd prime `p` and the canonical complete MUB family

```text
M_infinity = computational basis,
|b_(a,j)> = p^(-1/2) sum_x zeta^(a*x^2+j*x) |x>,  a,j in F_p.
```

The **same** basis is used on both parties. Bob's basis is not conjugated or independently optimized. Let `E` be the sum of the `p` smallest measured classical mutual informations from the `p+1` settings, and let `Q` be quantum mutual information. All logarithms in the paper are natural.

1. **Every full-Schmidt-rank equality state is classified, without assuming it is a stabilizer state.** For pure states `E <= (p/2) Q`. Full-rank equality holds exactly for
   
   ```text
   |Psi_(s,t,b)> = p^(-1/2) sum_x zeta^(b*x) |x,s*x+t>,
   s^2 = -1,  t,b in F_p,
   ```
   up to an overall phase. Such states exist exactly when `p = 1 mod 4`. There are exactly `2 p^2` distinct rays, and every setting has mutual information `log p`, while `Q = 2 log p` and `E = p log p`. Hence the **global pure-state optimal ratio is p/2 for every prime p = 1 mod 4**. Saturating just the computational, Fourier, and `a=1` settings already forces this form.

2. **Every two-qudit pure stabilizer state is classified by its exact score.** Product states have `E=Q=0`. Every entangled pure stabilizer state has a unique stabilizer graph matrix `K` with determinant `-1`. If `m(K)` is its number of invariant projective lines, then
   
   ```text
   Q = 2 log p,
   E = max(m(K)-1,0) log p.
   ```
   Nonscalar matrices have at most two invariant lines, so `E` is `0` or `log p`. A scalar graph exists exactly when `s^2=-1`, and then `E=p log p`. The states in item 1 are therefore **all pure stabilizer ECQC violations**. At `p = 3 mod 4`, every pure stabilizer state satisfies the stronger `E <= Q/2`.

3. **General equality has a flat Schmidt spectrum and a rank gap.** In any dimension `d` where a complete MUB family is supplied, every nonproduct pure equality state has marginal spectrum `(1/r,...,1/r,0,...)`, and either `r=d` or `r <= (d+1)/2`. This does not assume complete MUBs exist in every dimension.

The paper also counts all pure stabilizer rays and all violating rays exactly. Its finite-field arguments have arbitrary-prime quantifiers; the enumerations are not used to extrapolate those statements.

## Contribution relative to earlier work

Iqbal's ECQC proposal is Conjecture 3.1 / equation (6) of arXiv:2509.08286v2, published as DOI [10.1007/s11128-026-05258-2](https://doi.org/10.1007/s11128-026-05258-2). Wang, Wang, and Chen already refuted unrestricted ECQC using mixed classical–classical states in [arXiv:2608.03828v2](https://arxiv.org/abs/2608.03828v2); that result is not attributed to this project.

The preceding [pure-state paper](../ecqc-pure-state-counterexamples/README.md), frozen at commit `2d67375906d729862d4eb085186a5fd5670ef390`, proved pure counterexamples at every odd prime and sharp ratios at `p=3,5`. This companion **does not repeat that validity classification as new**. It settles the full-rank equality problem and the entire pure stabilizer class, and extends sharp global ratios to every prime `p=1 mod 4`. It also supplies a general spectral/rank obstruction for remaining equality states.

The proof uses the published Holevo theorem and its necessary equality condition (commuting ensemble states), explicitly stated and cited in the paper. All other specialized steps, including the finite-Weyl projector, actual Born laws, invariant-line classification, and complete-MUB identity, are proved. See [LITERATURE.md](LITERATURE.md) for checked sources and search limitations; no historical-priority claim follows from a finite search.


**Frozen publication record:** DOI [10.5281/zenodo.23256934](https://doi.org/10.5281/zenodo.23256934); immutable GitHub Release: https://github.com/mxym/math/releases/tag/ecqc-extremal-classification-v1. The archive is version 1.0 and is bound to commit `c0a1085e360604a1f8f274290eb1556202a315ab`.

## Paper and independent replay

- [paper.pdf](paper.pdf) / [paper.tex](paper.tex): complete eight-page written proof, definitions, boundary cases, references, and disclosures.
- [check_exact.py](check_exact.py): integer cyclotomic construction of actual stabilizer density matrices and every Born table for six states; Hermiticity, purity, both partial traces, exact supports, and five rejected corrupted inputs. It also checks all **69,840** determinant-`-1` matrices over the nine listed prime fields.
- [check_affine_gauss.py](check_affine_gauss.py): a separate integer-autocorrelation implementation, checking **2,825** quadratic root sums and **252** affine Bell states. Actual full phase sums are used for every outcome at `p=3,5,7`; at the larger listed primes all quadratic root sums are checked once and then applied to the separately reconstructed affine coefficients. This is not an independent proof of the classification's reverse direction.
- [exact-replay.json](exact-replay.json) and [affine-replay.json](affine-replay.json): replay records, not substitutes for rerunning the programs.
- [REMOTE_REPLAY.json](REMOTE_REPLAY.json): second-environment replay with identical source/checker-output hashes, a fresh PDF build, and matching normalized extracted text on all eight pages.
- [AUDIT.md](AUDIT.md): theorem-to-lemma map, self-review, and precise verification boundaries.
- [SCREENING.md](SCREENING.md): checked alternative problems, a recorded unsuccessful route, and why the present stronger target was selected.

```bash
python3 check_exact.py
python3 check_affine_gauss.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

Only Python 3.10+ and its standard library are required for the two checkers. Both reject `python -O`. No floating-point entropy or eigensolver is trusted. The PDF requires a conventional LaTeX installation with the packages in `paper.tex`. The general full-rank and rank-gap proofs are analytic; **this package is not a complete Lean formalization**.

## Remaining scope

The sharp pure-state ratio for `p=3 mod 4`, `p>=7`, the general rank-deficient equality classification, mixed-state classifications, and different pairings of Alice's and Bob's bases are not solved here. Nonattainment at full rank does **not** imply a smaller supremum: the rank-two qutrit extremizer can be approximated by full-rank states. No experiment or experimental confirmation is claimed.

## Replay integrity correction

The immutable v1 source snapshots retain an outdated `SHA256SUMS` after the Lean-scope documentation update. The exact checker sources and their results were unchanged. The current manifest is repaired, and [the CI repair audit](../../verification/ecqc-replay-ci-2026-10-09/README.md) records the original discrepancies and fresh replay. A maintenance supplement is published at [ecqc-exact-replay-integrity-v1.1.1](https://github.com/mxym/math/releases/tag/ecqc-exact-replay-integrity-v1.1.1); frozen v1 files are not modified.

## Provenance and rights

AI assisted derivation, exploratory computation, coding, literature checking, writing, and self-audit. No external funding and no external professional mathematical peer review. Separate checker implementations mean separate code paths in this project, not independent human review. Copyright (c) 2026 Yongxian Zhang; all rights reserved for separately authored original material. Existing repository and source licenses remain unchanged. DOI and release timestamps, when assigned, do not certify priority. See [RIGHTS.md](RIGHTS.md).
