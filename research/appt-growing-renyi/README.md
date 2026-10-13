# APPT entropy at every positive Rényi order

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Complete all-order proof](ALL_ORDER_VARIATIONAL.md) ·
[Linear-order coupled profile](LINEAR_ORDER_VARIATIONAL.md) ·
[Elementary profile and its compact-order bridge](UNIFORM_PROFILE.md) ·
[Complete bounded-aspect spectral criteria](SPECTRAL_PROFILE.md) ·
[High-order endpoints](PAPER.md) · [Zero-order windows](SMALL_ORDER_BOUNDARY.md) ·
[Exact finite small-order phase](EXACT_SMALL_ORDER.md).

For actual all-global-unitary APPT densities, put D=mn and
E_α=log D−min S_α. The complete ordinary mathematical result is

    sup_(n≥m, α>0) |E_α/P^all_α(m,n)−1| →0   as m→∞.

There is no aspect-ratio or order-growth restriction. This resolves the
first nonzero entropy deficit even when it tends to zero. Below α=√m,
P^all is the explicit elementary formula U0. Above it, P^all is the logarithm
of a continuous two-variable finite scalar maximum V*, divided by α−1.
The split is a convenient display choice, not a physical phase boundary.

The high-order scalar maximum keeps the exact endpoint u_D=3D/(D+2) and
the exact finite physical protection coefficient. A necessary clique
rearrangement couples the actual spectral peak to the middle width. Exact
projection/spike APPT states match every scalar competitor asymptotically.
Thus the optimization is proved on the entire actual APPT set, without
assuming three-level spectra. The scalar approximant is not claimed to be
the exact finite-dimensional maximum.

The more explicit windows and classifications remain useful:

* At α→∞ with α=o(m), uniformly for all n≥m,
  `M*_α−1 ~ u_D^α/D + α(α−1)/(2m²)`. Both contributions are retained.
* At α/m→c>0, the limiting maximum F_*(c,r), r=3^α/D, couples the peak
  and bulk rather than independently adding their maxima. Its mixing
  parameter has an analytic optimizer, leaving a one-dimensional width
  maximum. In the pure-bulk endpoint r=0, F_* has a closed expression.
* For bounded n/m and every diverging α, the exact peak alone gives the
  moment-excess law. The softplus window is
  `α log u_D−log D→z`, where `(α−1)E_α→log(1+e^z)`.
* At α→0, uniformly over all n≥m,
  `D E_α ~ max{1,1−m^(−α)+(α/2)n/m}`. The two window coordinates are
  α log m and α n/m. All finite-window near-minimizers, including the
  alternating critical branches, are classified.
* At a convergent finite aspect ratio, near-minimizers are classified for
  every limiting order in [0,∞], including both finite critical orders.
  Growing-order entropy optimality and moment-excess optimality have
  different exact tolerances on the actual largest eigenvalue.
* For every finite D=mn≥4 and `0<α≤1/(512D)`, the exact minimum is
  `S_α=log(D−1)`, and every equality state is `(I−vv*)/(D−1)`.
  This band is explicitly sufficient; its largest possible endpoint is
  not claimed.

This is one continuation of the APPT research direction. The existing
projection/spike constructions, elementary endpoints and fixed-order laws
are credited inputs; the separate windows are not counted as independent
major conjecture solutions. No historical first-solution claim is made.

## Proof and verification boundary

The new limits, objectives, optimization bridges and classifications have
**complete written proofs without complete Lean formalization**.
[Initial proof/Lean map](THEOREM_MAP.md),
[linear-order map](LINEAR_ORDER_MAP.md) and
[all-order map](ALL_ORDER_MAP.md) specify the respective obligations.
The earlier notes retain their stage-specific scopes; the all-order note
supersedes their then-open unrestricted-aspect large-order gap.

The independent internal assistant read all eight initial proof/scope files,
then both new variational proofs and their prerequisite maps, and reported
no unresolved mathematical changes. Its literal read scopes and hashes are
in [the initial review](MANUSCRIPT_REVIEW.json),
[the linear-order review](LINEAR_ORDER_REVIEW.json) and
[the all-order review](ALL_ORDER_REVIEW.json). This is internal review,
not external human peer review. The inherited fixed-order chains are
identified inputs rather than freshly re-proved in their entirety.

The original APPTSubunit 8-module/39-root audit keeps its finite construction
and physical half-order-head scope. Its actual negative-family entrypoints
are recorded in the map; they do not certify the new order-dependent limits.
The parallel main purity formalization and its independently archived
receipt retain their own scope. No Lean build, added root, new audit or
expanded kernel claim was performed by this continuation.

Two standard-library checkers passed 455 exact rational SOS specializations,
two actual rational density-matrix negative-PPT controls (−9/3269 and −1/70),
and 51 numerical growing-order evaluations. Ordinary and `-O` Windows runs
and matching WSL runs passed. They share one implementation. The finite
evaluations supplement the endpoint proofs; they do not prove the universal
variational optimization or its limits. The reviewers did not independently
execute these checkers.

```bash
python3 check_growing_orders.py
python3 -O check_growing_orders.py
python3 check_small_order.py
python3 -O check_small_order.py
```

[Source bindings](SOURCE_HASHES.json) and the
[read-only source/review check](../../verification/appt-growing-renyi-20261014/README.md)
bind the final packet. [Literature comparison](COMPARISON.md) records the
current primary read scopes; it does not certify global priority.

Fixed-m moving-order optimization, exact finite minima outside the stated
small band, full arbitrary-aspect spectral rigidity, absolute separability
and complete formalization remain outside the result. Original rights and
third-party notices are preserved. OpenAI AI assistants assisted; no external
funding. No new Release, DOI, aiXiv submission or external peer-review status
is asserted.
