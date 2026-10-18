# Independent mathematical and interface review

Review baseline: `aa1cd0c497a4a9963013ec6dde76a5ed296e2c61`.
Reviewer: newly spawned independent internal AI reviewer, separate from the
mathematical authors. This is not external human peer review or priority
certification. Status: preliminary source review; final new-source kernel audit
is pending. No concrete mathematical defect was found in the inspected frozen
endpoints. The following are checked claims and exact boundaries, not a claim
that the manuscript has been completely formalized.

## Same actual reserved family

`OperationalCompletion/ReservedFamily.lean` defines `reservedProtocol` by
choosing `exists_reserved_geometric_protocol` using only `m,n,k,K` and their
arithmetic proofs. The unknown input `X` is quantified after the protocol and
its local witnesses. `KrausPPTProtocol.IsProductLocal` retains two actual finite
Kraus families, both completeness identities, and equality of their product
channel with the selected protocol on every complex matrix. It is not merely
positivity or an overlap budget. The preprocessing unitary is a single member
of the protocol; it does not vary with `X`.

`ReservedPure.balanced_reserved_family_sharp` refers to that exact definition.
Its eventual block threshold is independent of the integer `K` and the unknown
unit vector `z`; its matching upper bound applies to every actual Kraus PPT
protocol. The theorem is balanced `m=m`, `m>=2`. For every positive real epsilon,
it gives a multiplicative `(1-epsilon)` profile lower bound, including targets
below, at and above the real profile width. Epsilon at least one is harmless
but does not make the small-epsilon conclusion vacuous. This is an asymptotic
profile theorem, not exact finite-block equality.

`ReservationLimit` retains the actual natural floor `a^k/Q(k)`. The divisor is
`4*gridSectorCount(k)*pureSupportRank(m,n,k)`, with logarithm o(sqrt(k)) at fixed
dimensions. `reservedLarge_ratio_bounds` bounds natural subtraction using the
exact integer budget. The retained large fraction tends to one when `m>=2`.
`ReservationCutoff` loses exactly `log(4*Q(k)^2)` relative to the intrinsic
compression cutoff, and only uses quotient lower bounds after the divisor is
proved below both physical dimensions. This loses o(sqrt(k)), not a silently
ignored constant or floor.

`ReservedLaws.reserved_fidelity_exponent` covers `R>=0`, `m>=2`, `m<=n`, every
positive natural target sequence of the stated logarithmic rate, and every
actual density matrix including zero eigenvalues. The R=0 branch is explicit
in `ReservedExponent`; the high-rate proof uses smaller soft-grid widths and
does not assume the final target fits a local sector. `reserved_reliability_limit`
keeps `R<log(m)` and `H<log(mn)-2R<log(rank(X))`. The lower exponential converse
ensures the error is positive in that region, avoiding a misleading use of
Lean's totalized `log(0)`. Equality boundaries are not included.

`reserved_gaussian_limit` has positive varentropy and the strict entropy-limited
gap `C_H<log(m)`. Its second-order sequence is arbitrary subject to the displayed
limit; local-sector feasibility is proved eventually from that gap.
`reserved_eventually_exact` uses both `R<log(m)` and the strict rank cutoff.
It is genuine eventual fidelity one, obtained from exact support entropy mass
and the actual density upper bound. No equality-boundary exactness is claimed.
All these endpoints use the same `reservedProtocol` expression as the pure
profile theorem. This does not identify it with an efficient Schur circuit.

## Genuine complete positivity and PPT bridge

`CPInterface/Choi.lean` defines complete positivity as PSD preservation by the
entrywise actual matrix amplification for every finite auxiliary type and
matrix. Choi PSD follows by applying it to the unnormalized entangled vector
projection. `choiKraus` is the actual matrix square-root column family.
`choiKraus_apply` proves equality on every complex matrix, and trace duality
makes TP imply the completeness identity. CP/Choi/Kraus equivalences do not take
a Kraus or PSD certificate on the abstract side.

`CPInterface/PPT.lean` separately applies this construction to the channel and
its partial-transpose conjugate. `abstract_ppt_iff_actual_protocol` is genuinely
bidirectional and retains any supplied preprocessing `U` and the channel action
on every matrix. Its channel-model meaning must be stated accurately: the cPPT
condition constrains the postprocessing map `Phi`; the arbitrary global `U`
remains a separately allowed preprocessing operation. The theorem does not say
that `Phi o Ad_U` is itself cPPT for arbitrary global U, and the existing actual
protocol model does not impose that claim. No channel-model substitution was
found in the bridge.

## Finite probability and actual target inversion

`finite_iid_berryEsseen_sup` and `information_iid_berryEsseen` retain every
positive block length, positive variance, arbitrary finite laws and zero-weight
atoms. The universal constant is an explicit finite expression involving proved
integrals; there is no optimized numerical-constant claim. The terminal input
hypotheses are law positivity/normalization/variance, not a BE estimate, CLT,
Fourier approximation or smoothing certificate. `density_information_berryEsseen`
uses actual Hermitian eigenvalues and the exact iid spectral-weight bridge.

`QuantitativeQuantile` has a generic reusable inversion lemma with a CDF-error
premise, but its actual information-spectrum endpoint discharges that premise
with the internally proved finite BE theorem. `pptTargets` is defined by
existence of an actual finite Kraus PPT protocol and fidelity >=1-epsilon;
`universalTargets` uses the fixed density-independent protocol and both actual
local output caps. The Gaussian maximum theorem proves eventual nonemptiness,
boundedness and attainment internally through `NaturalMaximum`, rather than
assuming an optimizer or monotonicity in K.

The finite lower inverse endpoint currently uses `universalBlockProtocol`, not
the reserved family. The final same-family reserved finite-BE/maximum hookup is
therefore pending a later frozen source. `finiteCappedTarget` floors the actual
exponential and applies both integer caps. Positivity and the log-floor loss
include logarithmic budget zero; its finite achievability statement explicitly
retains the nonnegative budget and the finite BE quantile admissibility window.
Converse inverse bounds apply to all successful actual targets without local
caps. These are genuine finite targets, not arbitrary sets chosen to satisfy
the theorem conclusion.

`triangular_universal_gaussian_error` retains the computed Lyapunov ratio,
divergent sigma, and compression-loss/sigma conditions. Its sufficient
variance-floor theorem proves these from an actual uniform positive variance,
third centered moment=o(sqrt(k)), and an explicit dimension-loss bound
=o(sqrt(k)). Growing dimension alone is not asserted sufficient. The moving
Gaussian threshold need not converge. This concerns the intrinsic universal
family and does not silently substitute the reserved family or Schur overhead.

## Schur and circuit boundaries

The actual Jucys product theorem concerns joint eigenvectors of the proved
commuting Hermitian copy-permutation operators. It is not a classification of
joint eigenvalues as integer tableau contents. Codimension-one exact purity
and its scaled limit concern D=s+1 only; they cannot establish a general-rank
sharp two-moment expansion or Weyl-hook constant. The support-rank endpoint is
a leading lower bound with its matching upper bound still separate.

The all-k recursion is an actual word on exactly 2k original qubits. Its basis
action is coherent; the pure-power endpoint explicitly uses the original paired
coordinate equivalence and works for every amplitude vector z. Its polynomial
bound counts the actual recursively assembled gate list. This is currently
compression, not a completed Bell extraction/discard protocol. The actual Bell
circuit endpoint is required before final audit. Finite-gate approximation and
Solovay--Kitaev are outside the frozen compression endpoint.

## Verification status

The new audit helper library was ordinarily compiled successfully, 4 jobs;
log: `D:/math/tmp/extraction-resume-20261018/build-logs/20261018T150939291329Z-extraction-completion-audit.log`.
Only helper code has been built in this review tree so far. `reproduce.py --plan`
checks the draft list/config/import inventory. No final source manifest or
full empty-kernel/forged-proof verification has been produced. After a notified
final mathematical freeze, the report and scope must incorporate the actual
new endpoints and all checks must run in this independent tree.
