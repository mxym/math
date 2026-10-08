# Lean counterexample to Wakhare's Conjecture 2

This directory proves a finite counterexample to Conjecture 2 in Tanay Wakhare,
*Iterated Entropy Derivatives and Binary Entropy Inequalities*,
arXiv:2312.14743v2, published in *Journal of Approximation Theory* (2025),
DOI 10.1016/j.jat.2025.106143.

Reference: https://arxiv.org/abs/2312.14743v2

## Main result

For the coprime pair `k = 11`, `r = 10`, the exact parameter is the unique
`alpha ∈ (0,1)` such that `alpha^10 * (1 + alpha) = 1`. The polynomial defined
by the original equations (1.3) and (1.4) has at least four distinct roots in
`(0,1)`. In particular, its number of roots in `(0,1)`, counted with
multiplicity, is at least four and cannot equal two.

The four roots are in the disjoint open intervals

- `(1/5, 2/5)`
- `(2/5, 3/5)`
- `(3/5, 2/3)`
- `(2/3, 4/5)`

The final universal negation is `EntropyCounterexample.wakhare_conjecture_two_false`.
It has **no hypotheses**. Its statement negates the two-root count assertion even
when restricted to positive coprime pairs with `r < k` and parameters satisfying
the exact defining equation in `(0,1)`.

This is a disproof of the named auxiliary root-count conjecture. It does not
claim to disprove Ho's entropy inequality or to solve Frankl's union-closed sets
conjecture.

## Formal chain

1. `Alpha.lean` proves existence by the intermediate value theorem, uniqueness
   by strict monotonicity on positive reals, and the exact bounds
   `117/125 < alpha < 937/1000`.
2. `Definitions.lean` defines `h` and `p` directly from the paper's finite sums.
   It proves both fixed coefficient expansions by kernel-checked exact
   arithmetic. The coefficient lists are not assumptions.
3. `Signs.lean` proves the five strict signs `+,-,+,-,+` at the five rational
   points. It evaluates the original polynomial with rational lower/upper
   parameter bounds and uses positivity of its coefficient of the parameter.
   No approximate real parameter is substituted.
4. `FourRoots.lean` supplies intermediate-value lemmas placing four distinct
   roots in four disjoint open intervals.
5. `Counterexample.lean` combines the preceding proofs without sign hypotheses.
   It also defines the original finite sums directly as `Polynomial ℝ`, proves
   evaluation agrees with `p`, proves the polynomial is nonzero, and uses
   `Polynomial.roots`, a multiset counting multiplicities, filtered to `(0,1)`.
   The root-count lower bound is a proved multiset-cardinality inequality.

Important unconditional conclusions:

- `counterexample_four_intervals`
- `counterexample_four_ordered_roots`
- `counterexample_root_count`
- `counterexample_not_two`
- `counterexample_to_conjecture_two`
- `wakhare_conjecture_two_false`

The theorem `counterexample_for_any_parameter` additionally shows that the
result is independent of the particular choice construction of `alpha`.

## Verification and dependencies

Pinned versions:

- Lean `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`

Run `./verify.sh` from any directory. The script compiles every proof module in
sequence into a newly created empty local build directory and imports only that
fresh local output plus the existing, pinned dependency cache. No multi-gigabyte
library copy or network download is needed. The existing sibling
`../crouzeix_lean_coverage_20261007/` toolchain and mathlib cache are reused as
read-only dependencies. Their mathematical sources are not modified.

The script checks all named theorem dependencies using `#print axioms`, and
rejects any dependency outside `propext`, `Classical.choice`, and `Quot.sound`.
The proof source contains no `sorry`, `admit`, custom axioms, `native_decide`, or
`unsafe`. `norm_num`, `ring`, `linarith`, and ordinary `decide` produce proof
terms that the Lean kernel checks.

Evidence files:

- `logs/cleancompile.log`: clean build outcome and timings
- `logs/pins.log`: actual toolchain and mathlib revision
- `logs/finaltheorem-signatures-and-axioms.log`: complete theorem signatures and axiom dependencies
- `logs/axiom-audit.json`: machine-readable axiom audit
- `theorem_names.txt`: complete audited theorem inventory
- `VERIFICATION.json`: verification result and source SHA-256 hashes

The Python certificates in sibling research directories were mathematical
cross-checks only. They are not imported by the formal proofs and are not
trusted proof inputs.
