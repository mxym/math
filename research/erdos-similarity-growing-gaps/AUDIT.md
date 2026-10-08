# Proof review and verification boundaries

The new theorem has a complete written proof in `paper.md`. The review
below was performed by the same AI research workflow, not an external
professional referee. Existing bounded-gap formal evidence does not
formalize the new growing-gap endpoint.

| Step | Review conclusion | Evidence |
|---|---|---|
| Annular sampling | All selected inputs lie in the requested tail; only the needed crossings use the annulus bound. Endpoint activations are strictly open. | Section 2, equations (5)–(8) |
| Varying parameters | Branching, depth, edge count and gap all depend on the same annulus position; no fixed-tree asymptotic is reused. | Section 4, especially (24) |
| Template size | Uniform in every real branching $b\ge2$, every height, and nonnegative $L,g$. | Lemma 6; four all-parameter Lean lemmas |
| Probability | Own selector keys are distinct and unexposed; terminal keys are distinct after conditioning on all selectors. Shared routing paths are allowed. | Section 3.2 |
| Continuous parameters | Representatives cover full line-sign strata, including zero signs and exact grid boundaries, and are selected before free table entries. | Section 3.3 |
| Measurability | Exceptional centers are the compact projection of a closed finite relation. Representative selection needs no measurable dependence on the center. | Section 3.4 |
| Buffer | $T=U^{o(1)}$ makes the actual finest-grid buffer cost decay exponentially on the same annuli. | (25); not yet Lean-formalized |
| Repair | Uses the infinite selected tail beyond the template; no later logarithmic-gap control is assumed. | Lemma 5 proof |
| Global quantifiers | The nonempty countable family is prescribed first; the set then works for every stated parameter and every tail, with infinitely many distinct outputs even without injectivity. | Section 5 |
| New examples | Derivatives and elementary bin counting prove ratio decay and zero upper Banach density; intermittent blocks strictly broaden the global-gap condition. | Section 6 |

## Actual verification

- The standard-library exact checker checks 320 preorder placements
  containing 32,880 windows and 1,472 entropy algebra controls, and
  rejects corrupted span and edge data. Its ordinary and optimized
  outputs are byte-identical. These finite controls are not proofs of
  the infinite sequence theorem.
- `VariableTree.lean` proves four universal algebraic lemmas. Its source
  is freshly compiled with official Lean 4.34.1 and pinned Mathlib.
  `Replay.lean` gathers their actual dependency closure, rejects unexpected
  axioms and unsafe/partial dependencies, and replays 7,157 declarations
  into an empty trust-level-zero kernel environment. Root types and
  universe parameters are compared. A false bound must fail compilation.
- The 9-page PDF is compiled without TeX shell escape, has no missing
  characters or unresolved references and no overfull boxes. Its exact
  Markdown/TeX/PDF hashes are recorded.
- `verify.py` checks inventory and source hashes, replays the exact
  controls in both Python modes, and checks archived Lean-source/log
  correspondence. A fresh Lean run is a separate explicit command.

The official Lean implementation/runtime, machine, and standard axioms
`propext`, `Classical.choice`, `Quot.sound` remain trusted. The partial
Lean replay proves the finite algebra; it does not check the new analytic
asymptotics, annular sampling, examples or main avoidance endpoint.
The source-provenance record credits the inherited finite method.

## Remaining problem

The full Erdős similarity conjecture remains unproved by this package.
In particular neither $2^{-n^2}$ nor $2^{-2^n}$ meets the hypotheses.
`RESEARCH_LOG.md` identifies the exponential-depth obstruction for that
next regime. A finite literature comparison does not establish priority.
