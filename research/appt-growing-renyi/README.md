# APPT entropy when the Rényi order moves with dimension

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Uniform all-order theorem](UNIFORM_PROFILE.md) ·
[Complete limiting-order spectral criteria](SPECTRAL_PROFILE.md) ·
[High-order proof](PAPER.md) · [Zero-order proof](SMALL_ORDER_BOUNDARY.md) ·
[All-aspect macroscopic high-order law](MACROSCOPIC_HIGH_ORDER.md) ·
[Proof/Lean map](THEOREM_MAP.md) · [Literature and scope comparison](COMPARISON.md).

The ordinary proof chain is complete in these stated ranges:

* m→∞ and bounded n/m: one explicit equivalent is uniform over **every α>0**,
  including α→0, the two finite transition orders, α of logarithmic size and
  α growing arbitrarily faster than D=mn.
* m→∞ and arbitrary n≥m: the same equivalent is uniform for all
  `0<α≤U_m` with `U_m=o(m)` and U_m≥2 eventually.
* For a convergent finite aspect ratio, the first nonzero entropy-deficit
  near-minimizers are classified for every limiting order α∈[0,∞]. At α=1/2
  the two branches may alternate; at α=2 purity optimality alone is the
  leading condition. At the infinity endpoint the exact peak tolerance
  distinguishes entropy optimality from moment-excess optimality.
* At the weaker absolute-error scale, every n≥m and every diverging order
  satisfy `E_α−[log(3D/(D+2))−log D/α]_+→0`, uniformly. This does not replace
  the first nonzero equivalent in the excluded unrestricted-aspect large-order
  range.

The high-order moment law for α→∞, α=o(m) is

    M*_α−1 ~ [3D/(D+2)]^α/D + α(α−1)/(2m²),

and its logarithm gives the entropy equivalent, with both positive terms
retained when comparable. For bounded aspect, the peak term alone gives the
law for every diverging α. The critical entropy window is
`α log[3D/(D+2)]−log D→z`, where `(α−1)E_α→log(1+e^z)`.

At α→0, uniformly for all n≥m,

    D E_α ~ max{1,1−m^(−α)+(α/2)n/m}.

The two small-order window coordinates are α log m and α n/m. This proves
why the earlier fixed-order subunit coefficient cannot be extrapolated
uniformly through zero. The full finite-window near-minimizer classification,
including the exact two critical branches, is in the zero-order note.

These are actual all-global-unitary APPT density results. Their upper bounds
use physical Schmidt witnesses and the original spectrum, and their lower
bounds use finite physical projection/spike states with explicitly selected
integer parameters. Existing constructions, the elementary endpoints and
the older fixed-order laws are credited as inputs; the new uniform profile
is one continuation of the same APPT direction, not several counted major
conjecture solutions. No first historical solution is certified.

## Verification boundary

The new objective, limits, compact-order connection and spectral criteria
are **written proofs without complete Lean formalization**. The original
APPTSubunit 8-module/39-root audit keeps its original finite construction and
half-order-head scope. The negative finite lower family has its old actual
Lean entrypoint; the new α-dependent limits do not. The separate positive
lacunary certificate likewise retains its own source and scope. No Lean
module, root, axiom or audit is added by this package.

Two standard-library checkers verify 455 exact rational SOS specializations
and reject two actual rational density matrices by negative partial-transpose
quadratic forms: −9/3269 for a wrong positive protection coefficient and
−1/70 for removing the negative-family protector. They also evaluate 51
finite growing-order examples. Those evaluations are numerical diagnostics,
not universal proofs. Ordinary and `-O` runs passed in Windows, and matching
WSL runs passed; these environments use the same implementation.

```bash
python3 check_growing_orders.py
python3 -O check_growing_orders.py
python3 check_small_order.py
python3 -O check_small_order.py
```

The independent internal manuscript review will be source-bound to the actual
papers and identify its read scope. It is not external human peer review.
Until that record is completed, this directory is a protected local research
draft; the main README result catalogue is updated only after mathematical
review. Source hashes will bind the final manuscript and records.

Unrestricted-aspect orders comparable to m or larger, fixed-m moving-order
minima, exact finite minima, absolute separability and complete formalization
remain outside the result. Original rights and third-party notices are
preserved. OpenAI AI assistants assisted; no external funding. No new
Release, DOI, aiXiv submission or external peer-review status is asserted.
