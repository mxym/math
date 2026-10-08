# Independent audit of the Lean counterexample to Wakhare Conjecture 2

Date: 2026-10-08 UTC.

## Verdict

The five mathematical source modules independently compile from their source snapshot into a newly created empty owned build directory. All 37 explicitly named theorems have exactly the standard axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`. No source warning or error occurred. The final theorem has no outer hypotheses. All 79 owned declarations, including generated declarations, passed their axiom audit, and their 16,089-declaration transitive dependency closure was successfully replayed into an empty kernel environment at trust level zero in 77.247 seconds. No owned declaration was skipped. The deliberate invalid-proof negative control was rejected as required.

## What was checked

The audited source is `source/{Alpha,Definitions,Signs,FourRoots,Counterexample}.lean`. It was copied as text, not as compiled objects, from the author's directory. `source-sha256.json` identifies the exact files. The author's source was read-only throughout this audit.

The primary source was independently opened during this audit: [Wakhare, arXiv:2312.14743v2](https://arxiv.org/html/2312.14743v2), Introduction, Conjecture 2, equations (1.3) and (1.4), and Section 6, equation (6.1). The function and polynomial definitions match the published expressions: outer indices cover `0 ≤ j < k`, inner indices cover `0 ≤ v ≤ j`, alternating signs and denominators are real-valued, the binomial arguments are `r*v+k` and `k`, and the first summand uses `h k k`. All binomial upper indices used here are nonnegative, so `Nat.choose` has the required meaning. The parameter equation used formally is the paper's equivalent integer-power equation (6.1).

The source correspondence is a human semantic audit. Lean proves the integer-power parameter equation and uniqueness; this development does not separately formalize the real-exponent manipulation converting equation (1.1) to (6.1).

### Complete chain, without assumed certificates

- `Alpha.lean` proves existence, positivity, the upper bound below one, the algebraic equation, uniqueness among positive solutions, and exact rational bounds `117/125 < alpha < 937/1000`.
- `Definitions.lean` defines the genuine double finite sum and the associated function. Both displayed coefficient polynomials are proved equal to these sums; they are not assumed or supplied by an external numerical oracle.
- `Signs.lean` proves five strict signs `+,-,+,-,+` at `1/5`, `2/5`, `3/5`, `2/3`, and `4/5`, using exact rational arithmetic and the proved bounds on the exact parameter.
- `FourRoots.lean` proves intermediate-value lemmas. The four roots lie in the four open intervals between consecutive sample points; they are strictly ordered, are all in `(0,1)`, and all six pairs are unequal.
- `Counterexample.lean` applies those lemmas with all hypotheses discharged. Its polynomial-valued definitions repeat the original finite sums, and evaluation equivalence is proved. It proves the polynomial is nonzero. `unitRootCount` is the cardinality of the `Polynomial.roots` multiset filtered to `(0,1)`. The mathlib theorem `Polynomial.count_roots` identifies each multiset count with `rootMultiplicity`. Thus this is genuinely multiplicity counting. Four distinct roots give a four-element finset contained in the filtered roots, followed by the proved `toFinset.card ≤ card` inequality.
- `counterexample_to_conjecture_two` verifies `0 < 10 < 11`, coprimality, the admissible exact parameter and root count at least four. `counterexample_not_two` excludes count two. `wakhare_conjecture_two_false` negates the universal assertion even on the smaller domain of positive coprime pairs, sufficient to disprove the published all-pairs assertion.

## Final theorem and scope

The checked final signature is:

```lean
EntropyCounterexample.wakhare_conjecture_two_false :
  ¬ (∀ k r : ℕ, 0 < r → r < k → Nat.Coprime k r →
      ∀ a : ℝ, a ∈ Set.Ioo 0 1 → a^r * (1+a)^(k-r) = 1 →
        unitRootCount (pPolynomial k r a) = 2)
```

There are no outer parameters or assumptions. The binders and implications displayed under the negation are the universally quantified conjecture being disproved, not assumptions imposed on the result.

This proves at least four distinct interior roots, hence at least four counted with multiplicity. It does not prove exactly four, determine multiplicities, assert a smallest example, classify all parameters, establish novelty, refute the entropy inequality, or solve the union-closed sets conjecture. The separately audited `(20,19)` example is not part of this Lean development.

## Reproducibility and trust boundary

Run `./run_independent.sh`. It creates a new `fresh-owned.XXXXXX` directory on each run. `LEAN_PATH` contains that new directory followed only by the existing upstream dependency-package build directories. It excludes the author's directory, the author's old or new owned oleans, the old project's own build directory, and previous independent owned builds. The source directory contains no imported owned olean. Every one of the five mathematical modules is compiled again in dependency order.

The reused toolchain is Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The reused official mathlib checkout HEAD is `d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency files were changed, and no multi-gigabyte dependency copy was made. `logs/lean-path.txt`, `logs/build-directory.txt`, and `logs/pins.log` record the actual run. This is an independently rerun audit in the shared environment, not a separately provisioned machine or independent kernel implementation.

The independent source scan rejects `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, and `implemented_by` in the five mathematical modules after removing comments. There are 37 explicit theorems and 10 explicit definitions. The replay auditor enumerates every declaration originating in those five modules, including generated declarations, and rejects any unsafe/partial declaration or any axiom dependency outside the standard three.

The additional replay uses official `Lean.Kernel.Environment.replay` on a complete dependency closure, starting with `mkEmptyEnvironment 0`. It rechecks definitions and proof terms; generated constructors and recursors are compared with those regenerated by the kernel. This goes beyond importing compiled artifacts or compiling an audit wrapper. The checking harness itself uses ordinary Lean metaprogramming and a partial traversal routine; it is outside the mathematical proof modules and is not an extra trusted mathematical axiom. A separate negative control sends a deliberately ill-typed theorem (`Nat.zero` purportedly proving `True`) through the same empty-kernel mechanism and requires its rejection.

Fresh recompilation and empty-kernel replay are separate checks. Reuse of upstream compiled dependencies is disclosed; no full fresh source build of all mathlib is claimed. The replay covers the transitive closure of all owned declarations, not every unrelated declaration in mathlib. Standard Lean axioms remain axioms; they are not proved by replay.

## Evidence

- `source-sha256.json`: hashes of the five audited mathematical source modules
- `theorems.txt`, `definitions.txt`: independently extracted explicit declaration inventory
- `theorem-axioms.json`: all 37 theorem axiom sets
- `logs/run.log`: fresh compilation outcomes and timings
- `logs/theorem-signatures-and-axioms.log`: full checked theorem signatures and axiom sets
- `logs/negative-control.log`: rejection of the deliberate invalid proof
- `logs/empty-kernel-replay.log`: all-owned axiom audit and replay outcome
- `VERIFICATION.json`: consolidated final results

No publication, git operation, external contact, or attachment delivery was performed.
