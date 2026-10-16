# Actual information-spectrum, iid limits and Renyi converses

This is a new, separately bounded Lean scope for the October 2026 extraction manuscript.
It does not change or enlarge the original 83-root finite-core audit, the 11-root local-cap
audit, or the earlier APPT 39/91/235/444-root audits.

Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned.

## Mathematical endpoints

- `Spectrum.Finite`: finite weighted Cauchy--Schwarz, the diagonal HS inequality with
  every off-diagonal matrix term retained, actual density spectral decomposition,
  and the all-unitary physical Kraus information-spectrum converse
  `F <= Pr{-log p <= log(N/K^2)+t} + exp(-t/2)`.
- `Spectrum.Tensor`: canonical coordinate tensor powers, tensor unitary construction,
  derived iid spectral product law, actual PSD/trace-one tensor densities, and exact
  equality of finite product-spectrum probabilities with sums of self-information.
- `Spectrum.PhysicalTensor`: canonical regrouping into Alice/Bob tensor factors and
  `kraus_tensor_information_bound` on actual complex tensor entries.
- `Spectrum.Probability`: a normalized finite PMF, the canonical infinite iid measure,
  proved independence, common law, finite moments, LLN and CLT. The exact finite-window
  law is connected to `iidInformationEvent`. Gaussian CDF and moving-threshold limits
  follow from the proved CLT, Portmanteau, a null-boundary check and Slutsky.
- `Spectrum.ConverseLimit`: actual-channel rate strong converse for
  `R > (log m + log n - H(p))/2` and actual-channel Gaussian limsup converse at the
  entropy-limited second-order target. Every initial global unitary is quantified.

Inputs may have zero eigenvalues. The Gaussian conclusions retain positive actual
varentropy. The channel notion is the original finite Kraus channel with completeness
and physical transpose-conjugate positivity; no output fidelity, tail probability,
LLN, CLT or tensor-spectrum conclusion is an input hypothesis.

- `Spectrum.Variational`: Gibbs nonnegativity and the exact escort change of law;
  attained infimum/supremum certificates for both the alpha-in-[1,2] fidelity-exponent
  scalar identity and the alpha-in-(0,1) strict-direct scalar identity. Escort
  interpolation is proved by continuity and the intermediate value theorem.
  Positive-support reduction and rank are connected to actual singular densities.

- `Spectrum.Holder`: finite capped Holder interpolation, internally derived matrix
  effect caps and quadratic budgets, physical one-copy and iid Renyi moment bounds,
  exact tensor moment multiplication, and the optimized variational exponential
  converse `kraus_tensor_variational_exponential_converse`. For every positive eta,
  actual channel fidelity is eventually at most `exp(-n*(E_p(log(mn)-2R)-eta))`,
  where `E_p(c)=inf_q [D(q||p)+(H(q)-c)_+/2]` on the actual positive eigensupport.
  The endpoint alpha=1 follows from the physical unit effect cap. This formulation
  remains valid when an individual fidelity is zero.

## Exact limits of this scope

This package does not claim universal Schur--Weyl lower bounds, complete capacity
achievability, a matching operational fidelity-exponent lower bound or reliability theorem,
Berry--Esseen constants, Haar averages, unknown-support minimax asymptotics,
or circuit synthesis. It formalizes the converse, optimized exponential upper bound, scalar variational identities, and actual iid probability bridge.
It does not identify abstract CP maps with a finite Kraus presentation.

## Reproduce

At the pinned revision, obtain the Mathlib cache, then run:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

`--fresh` rebuilds only this new package's mathematical and audit outputs. Imported
dependencies are checked again by the trust-zero empty-kernel replay. The replay
compares original root types and universes and rejects same-type forged proofs;
the mathematical closure permits only `propext`, `Classical.choice`, and `Quot.sound`.
The verification utility was adapted, with a separate namespace/output stem, from
`spectral-extraction-core/Verification/ReplaySupport.lean`.

The owned `SOURCE_HASHES.json` also binds the unchanged finite-core source inputs.
The source inventory is evidence of byte identity, not an external peer review.
The PMF, CLT, strong law, spectral theorem, and matrix results use the pinned Mathlib
implementation and its original authorship/licenses.
