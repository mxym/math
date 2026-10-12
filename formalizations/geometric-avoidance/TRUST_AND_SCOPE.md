# Trust, scope and interpretation

## Mathematical content

`MainTarget` uses Lean's ordinary real field, ordinary topology and Mathlib's standard real measure space. Its volume condition is

```lean
ENNReal.ofReal (1 - ε) < MeasureTheory.volume E
```

with E compact and contained in the unit interval. This is genuine Lebesgue measure, not a substitute probability measure or a counting statistic. The independent probe checks `volume (Icc u v) = ENNReal.ofReal (v-u)` and `volume (Icc 0 1) = 1`.

For each positive ε below one, E precedes all sequence parameters. Nonzero real coefficients of both signs, all real centers, every real ratio strictly between zero and one and every natural tail are covered. Existence of arbitrarily late terms outside E is stronger than merely one escaping term. It does not assert an eventual all-outside tail or a uniform numerical escape bound.

There are no additional hypotheses on the final theorem. Intermediate conditional interfaces are reusable local lemmas, and the final construction proves their premises. Historical progress comments were preserved to keep proof-source bytes unchanged.

The exclusions have mathematical content. At a member b of E, a = 0 or q = 0 makes an eventual constant sequence. At a member a+b of E, q = 1 is constant. The whole unit interval fails avoidance, for example for a = 1, b = 0, q = 1/2. `checks/IndependentBoundaryFacts.lean` proves these boundary facts. The theorem only asks for ε in (0,1), so its set has positive measure.

## What kernel replay adds

Ordinary compilation checks owned declarations against imported declarations. The audit goes further: it traverses the actual stored type and value dependencies of the main theorem, gathers 34,771 declarations, and replays them into an empty environment at trust level zero using the official Lean kernel. It checks that the replayed root has the literal type `ContinuumGeometric.MainTarget`. Inductive blocks, constructors and recursors are handled through the official replay machinery. This is not merely an import list or a cached list of claimed axioms.

The complete safe-owned graph contains 35,197 declarations. All 1,164 owned declarations are located by actual defining module rather than namespace prefix. Lean generates nine internal `._unsafe_rec` code-generation implementations for ordinary terminating definitions. They are inventoried, not ignored; none occurs in any safe owned type/proof closure. The mathematical source contains no `unsafe`, `partial`, `sorry`, custom axiom, `native_decide` or custom elaborator escape. Audit programs themselves use metaprogramming to inspect and replay proof terms; they are checking tools, not premises of the theorem.

## Remaining trust

The allowed foundational axioms are precisely `propext`, `Classical.choice` and `Quot.sound`. The result retains the ordinary mathematical interpretation of these axioms, Lean's definitions and inference rules, the correctness of the official kernel and replay implementation, compiler/runtime execution, and the underlying machine. Empty-kernel replay reduces dependence on imported compiled proof validation; it does not eliminate implementation or foundational trust.

The release uses a SHA-256-pinned official Linux x86-64 Lean release archive and exact source commits. Reuse of an installed toolchain verifies the executable and all 17,750 recorded distribution-file hashes, including the runtime and checking libraries. Pinned official dependency caches are reused read-only; this is not a claim that every Mathlib module or the compiler was rebuilt from source. The actual main dependency closure is kernel-rechecked. The audit's recorded source/artifact hashes cover 1,301 defining modules in the whole safe-owned graph, of which 1,298 occur in the main closure.

The independent semantic audit was AI/model-based, separate from the proof-writing work. It is not external professional-human peer review. Finite arithmetic regression tests and negative controls help detect errors in interfaces, guards and checking scripts, but do not replace the universal Lean proof or semantic interpretation. No evidence here establishes novelty, priority or practical efficiency.

## Out of scope

The stronger theorem about power-controlled nonlinear remainders and continuum leading-exponent profiles is written only. This package does not certify arbitrary C¹ or flat germs, arbitrary slow remainders, or finite-sieve optimality. It does not provide an explicit useful numerical description of E. Its large and noncomputable choices are legitimate for this existence theorem.
