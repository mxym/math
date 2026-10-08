# Entry002 v3: actual number-field prime-ideal PNT work, round 4

The all-quadratic-orders `MainTarget` and universal prime supply remain OPEN.
The closed finite sieve and no-walk target remain proved. This round preserves
the exact target, genuine irreducibility and field norm, every real and imaginary
quadratic field, and every positive conductor. It does not substitute finitely
many rings, a finite checker, or a written-proof audit for the main theorem.

The immutable round3 archive is
`entry002-v3-lean-round3-20261007.zip`, SHA256
`b522ad7db760522efd762dc9a8dfc97b75bc794ecdb2ce5f059b30f628cb7cc7`.
Its Library ID is `${PRIVATE_DELIVERY_ID}`, and its backing
file ID is `${PRIVATE_DELIVERY_ID}`. Round4 was extracted from
those exact bytes into a fresh isolated directory; the archive is unchanged.

## Exact open proposition and unchanged conditional MainTarget

`Entry002.NumberFieldPrimeIdealPNTTarget`, in
`Entry002/PrimeIdealAnalyticDefs.lean`, is only a transparent definition of:

```lean
∀ (N : Type) [Field N] [NumberField N],
  Tendsto (fun x : ℝ =>
    ((Entry002.nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) /
      (x / Real.log x)) atTop (nhds 1)
```

`Entry002.PrimeIdealNaturalPNT N` is the same per-field statement. These
definitions are not proofs or axioms. They count actual nonzero prime ideals
of `𝓞 N`, with actual `Ideal.absNorm` and inclusive natural-floor endpoints.
This is the natural `x/log x` counting theorem, not Dirichlet density.

The unchanged conditional main theorem is
`Entry002.arithmeticSupply_mainTarget_of_primeIdealPNT`, in
`references/upstream/arithmetic-audit/ArithmeticSupplyMainFromPrimeIdealPNT.lean`.
Its raw displayed premise is the local binder `hPrimeIdeal`; no theorem proving
that premise has been supplied. The arithmetic assembly constructs an actual
finite Galois normal closure of an arbitrary-conductor ray field. It therefore
uses the premise at that normal closure, but its public quantification remains
all number fields. The new elementary estimates also hold for all number fields.

## Closed mathematical progress

The five new mathlib-only modules prove the elementary inputs needed by the
number-field Wiener route, without an analytic premise:

* `PrimeIdealAnalyticDefs`: actual prime norms are at least two; positive
  norm-power exponents are unique and within the finite cutoff; the genuine
  logarithmic prime-power coefficient is nonnegative.
* `PrimeIdealPowerSummation`: exact coefficient and endpoint double sums
  `∑_{N(P)^k=n, k>0} log N(P)` and `∑_{N(P)^k≤x, k>0} log N(P)`, and `θ_K≤ψ_K`.
* `PrimeIdealVonMangoldtBound`: the genuine full ramification/inertia identity
  gives `Λ_K(n)≤[K:ℚ]Λ(n)`, including ramified primes and non-Galois fields.
* `PrimeIdealChebyshev`: actual `ψ_K` and count bounds, absolute convergence
  and holomorphy of the true coefficient L-series on `Re(s)>1`, and the actual
  higher-power error `|ψ_K−θ_K|≤2[K:ℚ]√x log x=o(x)`.
* `PrimeIdealNaturalPNTBridge`: honest cutoff estimates and conditional
  implications `θ_K(x)/x→1 ⇒ PrimeIdealNaturalPNT K` and
  `ψ_K(x)/x→1 ⇒ PrimeIdealNaturalPNT K`. The two weighted asymptotics are
  equivalent by the unconditional error bound; neither is asserted to hold.

The separate `ArithmeticSupplyPrimeIdealWiener.lean` applies the actual audited
`WienerIkeharaTheorem'`. It proves both elementary Wiener inputs, including
its precise exclusive `cumsum` cutoff, then the conditional endpoint
`Entry002.primeIdealNaturalPNT_of_wiener_boundary`. Its complete remaining
premises are visible:

```lean
(G : ℂ → ℂ)
(hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
(hG' : Set.EqOn G (fun s : ℂ =>
  LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)) s - 1 / (s - 1))
  {s : ℂ | 1 < s.re})
```

This is a proved conditional analytic reduction. No such boundary function
has been constructed for an arbitrary number field, and the original PNT
premise has not been replaced or claimed closed by this theorem.

## Actual remaining foundations

An ideal-factorization proof must identify the logarithmic convolution of
the genuine ideal-count coefficients with `Λ_K`. The exact missing finite
norm/divisibility-fiber equivalence and weighted regrouping are identified in
`references/PrimeIdealLogConvolution-foundations-round4.md`. The raw Dedekind
coefficient has `a_K(0)=1`; the existing L-series convention ignores zero, and
its convolution construction already performs the required zero correction.

The serious analytic gap is genuine Dedekind-zeta continuation and line-one
nonvanishing, followed by the true logarithmic-derivative identity producing
the displayed continuous `G`. One route uses a quantitative all-ideal count
`C_K x+O(x^α)` with `α<1`, a complex integral continuation, and the Euler
three-point positivity argument. The pinned library currently supplies the
all-ideal `C_K x+o(x)` asymptotic and a positive real-axis residue, not that
power-saving estimate or complex boundary construction. A finite Lipschitz
chart cover of the actual norm domain and quantitative lattice counting are
still substantial missing foundations on that route.

`references/NumberFieldPrimeIdealPNT-analytic-audit-round4.md` records bounded,
commit-addressed primary-source inspection. Apparent public Chebotarev results
have actual `sorry`, or only Dirichlet-density scope. Other candidates are
source-level intermediate lemmas, not imported checked foundations. No
repository-name or finite keyword search is claimed to prove global absence.

## Verification and trust boundary

Lean4.34.1, compiler `5045d0056413266e57c625dcd7c365b10e377c52`, and official
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain fixed.
The fresh main build has 85 substantive modules and one umbrella, 4282 jobs.
Its complete stored-type/body audit covers 2339 safe roots: 2003 theorem and
336 definition roots, including generated equations and private proofs. These
are compiler declarations, not counts of independent mathematical results.
Only `propext`, `Classical.choice`, and `Quot.sound` occur, with no unsafe,
partial, or missing proof dependencies. The two previously exposed generated
`TimeLaw` cached-metadata discrepancies are unchanged; the stronger stored
closure remains authoritative. Target detection explicitly reports the
universal number-field PNT OPEN as well as MainTarget and prime supply OPEN.

The four authenticated patched PNT source modules and the new analytic bridge
are also freshly compiled, followed by a new complete analytic stored-body
audit. Official package caches remain trusted. No full CFT rebuild or second
kernel replay is claimed in this round. Parent-reported round3 empty-kernel
endpoint replay is recorded separately as received independent evidence,
not as this worker's rerun and not as a proof of number-field PNT.

The production source validator now derives its external dependency closure
from fixed endpoints and authenticates Git-tree and exact patch bytes before
reading imports. It requires unique paths and exact membership, rather than
999 rows. The original 15 negative controls missed the external manifest
duplicate/omission attack reported by the parent. Round4 explicitly repairs
that gap and rejects the unchanged-row-count omitted/duplicated/modified
Wiener sample through both production entrypoints. The exact external scope
remains 995 CFT plus four PNT modules. Final logs and ledgers report the new
analytic workload separately; it overlaps the main audit and older workloads.

No GitHub push, publication, unrelated repository inspection, or target-changing
axiom occurred. Source and evidence are packaged; tools and binary caches are
omitted. The final archive manifest and Library receipt bind the delivered bytes.
