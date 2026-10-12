# Complete Lean formalization: infinite log-concavity of all cycle chromatic polynomials

**Research extension to the [previously formalized C17 counterexample](../chromatic-infinite-logconcavity-counterexample/README.md).** Lean **4.34.1**, Mathlib **v4.34.1**, commit **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. This package is a new all-length theorem, not a reissue of the already published single-cycle proof.

## Fully formalized theorem

Let `SimpleGraph.cycleGraph n` be Mathlib's actual undirected cycle on `Fin n`, with `n ≥ 3`, and let `Pₙ ∈ ℤ[X]` be its chromatic polynomial. We define `Pₙ` by the **genuine graph-coloring counting specification**: for every number `q : ℕ` of available colors, its evaluation at `q` is the cardinality of `SimpleGraph.Coloring (SimpleGraph.cycleGraph n) (Fin q)`, including `q = 0, 1, 2`.

The Lean proof derives the precise polynomial

\[
  P_n(X)=(X-1)^n+(-1)^n(X-1)
\]

for **every** `n ≥ 3` by a bijection between graph proper colorings and closed walks of length `n` on the complete `q`-color graph, followed by the exact adjacency-matrix trace identity. No graph/polynomial correspondence is assumed as an axiom.

For the full absolute-coefficient sequence `aₖ = |[Xᵏ]Pₙ|`, **zero extended on both sides**, define the log-concavity operator

\[
  (\mathcal L a)_k=a_k^2-a_{k-1}a_{k+1}.
\]

Our main Lean theorem is:

\[
\boxed{\forall\,n\ge3,\qquad
  (\forall r,k\in\mathbb N,\ (\mathcal L^r a)_k\ge0)
    \iff n\le11.}
\]

In particular all cycles `3 ≤ n ≤ 11` are **infinitely log-concave**; each length `12 ≤ n ≤ 16` has a certified finite negative iterate; and **every length `n ≥ 17`** is a counterexample already after the **third** log-concavity iteration at `k = 2`. The latter is proved by one exact polynomial identity and a uniform positivity theorem, **not** by enumerating values of `n`.

## Core proof declarations

The formalization comprises 11 named modules under [`ChromaticCyclesAllN/`](ChromaticCyclesAllN/), plus the root [`ChromaticCyclesAllN.lean`](ChromaticCyclesAllN.lean). Important declarations are:

| Theorem | Lean proof conclusion |
|---|---|
| `cycleGraph_colorings_all` | Every `n ≥ 3` and every color count `q` satisfy the exact graph counting polynomial identity. |
| `cycleGraph_chromatic_polynomial_classification` | True cycle-graph chromatic polynomial, plus the **if and only if** infinite-log-concavity classification. |
| `every_actual_cycle_n_ge_17_fails` | The infinite family fails `LC (LC (LC a)) 2 ≥ 0`. |
| `cycle_binomial_infinite_classification` | Explicit coefficient-sequence classification for all lengths, including 12–16. |
| `triple_preserved` | A three-factor strengthened log-concavity invariant is preserved by the full iterate operator. |
| `third_iterate_closed_formula` | The symbolic factorization proving failure for every `n ≥ 17`. |

The graph step uses the actual `SimpleGraph.cycleGraph` adjacency structure, closes the wrap-around edge, constructs and identifies closed complete-graph walks, compares their cardinalities by injective maps, and evaluates `Matrix.trace` exactly. The positive infinite-iterate case uses a **uniform invariant-preservation lemma** plus exact finite initial certificates, not a finite iteration cutoff masquerading as an infinite theorem.

**Boundary convention:** The sequence is indexed by `ℕ` and zero-extended; `a₀ = 0` and `aₖ = 0` for `k > n`. At `k = 0`, Lean's truncated subtraction `k - 1` is harmless because `a₀ = 0`. The result does not silently switch to endpoint deletion or an unrelated binomial sequence.

## Fully reproducible verification

From this directory, with Git/network access for a fresh Mathlib checkout:

```sh
# Installs the exact toolchain listed in lean-toolchain if not already installed.
# lake-manifest.json pins every upstream dependency including Mathlib.
lake exe cache get
bash scripts/replay.sh
```

Alternatively `lake build ChromaticCyclesAllN` compiles the complete library target. `scripts/replay.sh` builds the library and **additionally** checks all primary axiom dependencies, bans `sorry`/`admit`/`native_decide`/unchecked axioms in owned proof files, and confirms that an intentionally invalid proof is **rejected**. The GitHub Actions workflow performs the same steps on a clean Linux runner. See [`audit/AxiomsAudit.lean`](audit/AxiomsAudit.lean) and [`audit/InvalidProof.lean`](audit/InvalidProof.lean).

Axioms for exported roots are confined to Lean/Mathlib's **`propext`, `Classical.choice`, `Quot.sound`**—no `sorryAx`, `native_decide`, custom axioms or unsafe declarations are accepted. A full dependency-kernel reimplementation is not claimed; verification uses the Lean kernel on the fixed upstream toolchain/Mathlib commits.

## Provenance and limits

The [earlier C17 package](../chromatic-infinite-logconcavity-counterexample/README.md) already proved the isolated graph-theoretic counterexample. The present package extends the **entire graph-coloring/polynomial chain and the infinite-iteration classification to every cycle length**. Its definitions and proof do not import the earlier C17 code. The mathematical formulas and finite classifications are from [`notes/chromatic-infinite-logconcavity-counterexample/`](../../notes/chromatic-infinite-logconcavity-counterexample/); this is the independent full-length Lean extension.

The proof is about finite undirected cycles; no assertion is made about all graphs, arbitrary chromatic-polynomial sequences or other conjectures. Prepared with AI assistance. Formal kernel verification is not an external human peer review or a claim of mathematical publication priority.
