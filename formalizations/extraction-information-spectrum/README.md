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

- `Spectrum.Types`: actual integer occupation counts and empirical probability
  laws; at most `(k+1)^D` types and at most `exp(k H(q))` words in one type, derived
  from the exact empirical iid likelihood and total probability one. Therefore
  the state-independent collection `H(q_w)<=c` has at most `(k+1)^D exp(kc)` words.
  Positive-mass self-information words lie in this collection by Gibbs; zero-mass
  words are explicitly discarded in the information-mass comparison. Its mass
  has the proved LLN lower limit and moving-threshold Gaussian liminf. Fixed
  polynomial logarithmic overheads are negligible at first and second order.
  This module does not depend on any protocol, Schur, or Haar package.

- `Spectrum.Direct`: an exact occupation product, equal likelihood for equal
  empirical types (including zero-likelihood types), supported escort weak
  duality, and the finite direct error estimate
  `1-mass <= (k+1)^D exp(-k E_direct(c))` for `H(p)<c<log|supp(p)|`.
  The variational exponent is attained, is proved strictly positive, and is
  retained under moving thresholds converging to c, with the polynomial removed
  from its exponential rate. Actual-density statements use the actual matrix
  rank and allow singular densities. This is a classical compression-error
  bound; composing it with a physical universal protocol is outside this package.

- `Spectrum.Prefix`: the actual mass of every r-element subset of a decreasing
  finite spectrum is bounded by its first r entries.
- `Spectrum.Tilt`: exact escort likelihood ratios and constructed typical bands;
  asymptotic full escort mass from the proved finite iid law; original-law mass
  lower bounds and actual finite cardinality bounds. The same optimized escort
  attains the exact positive-support variational value and yields subsets with
  `card(A_k)<=exp(k(H(q)+epsilon))` and eventually
  `p^k(A_k)>=exp(-k(D(q||p)+epsilon))`. The parameter and subsets are constructed.
  These are the classical ingredients for a matching operational exponent;
  their composition with the physical extraction profile is outside this package.

## Exact limits of this scope

This package does not claim universal Schur--Weyl lower bounds, complete capacity
achievability, a matching operational fidelity-exponent lower bound or reliability converse,
Berry--Esseen constants, Haar averages, unknown-support minimax asymptotics,
or circuit synthesis. It formalizes the converse, optimized exponential upper bound, scalar variational identities, exact classical direct error upper bounds, and actual iid probability bridge.
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

The earlier run `reproduction-20261016T043319Z` was stopped with SIGTERM during
the user-requested storage migration. Its interrupted logs are retained and are
explicitly not PASS evidence. The final source-bound run is recorded separately.
All current builds were run with the D-backed research filesystem and D-backed
temporary/download caches; storage placement is not a mathematical assumption.
