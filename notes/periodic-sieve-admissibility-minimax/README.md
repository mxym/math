# Exact CRT minimax duality for arbitrary finite lattice sieves

Research note, 8 October 2026. [Complete general proof](paper.md) · [logical dependency audit](AUDIT.md) · [precise reproduction references](results/REPRODUCTION.md).

This continuation extracts a general theorem from the exact quadratic-prime sieve programme, **independent of quadratic integers or prime-value conjectures**.

For any integer lattice dimension `d`, any finite symmetric set of steps `F`, and **arbitrary** allowed residue sets `U_p ⊆ (Z/pZ)^d` indexed by rational primes, let `M(P)` be the maximal connected-component size of the periodic lattice graph passing the finitely many local conditions at primes `p∈P`. Let `A*` be the supremum of sizes of **finite connected patterns** admitting a translation into `U_p` modulo *every* individual rational prime. Then

\[
\boxed{\inf_{P\text{ finite}} M(P) = A^*.}
\]

**Finite attainment:** If the right-hand side is finite, there is **one finite set of primes attaining the infimum**. If it is infinite, no finite sieve can have bounded component sizes. This uses only coordinatewise CRT and the finiteness, up to translation, of connected lattice shapes with a fixed number of vertices. The paper gives the entire traditional proof, including empty/degenerate cases and a crude explicit upper bound on the number of obstruction primes needed.

For norm-coprime predicates in the Euclidean domain `Z[sqrt(-2)]`, the local sieve by any finite rational prime set can be realized exactly by a finite family of **principal prime ideals**. Conversely, every finite principal-ideal sieve contains its associated norm-coprime sieve as an allowed subgraph. Hence the same minimax identity applies **exactly to all finite principal-ideal sieves** in this ring.

The [197-point universally admissible shape](../sqrt-minus-two-universal-sieve-barrier/README.md) and [matching six-stage period-sieve proof](../sqrt-minus-two-exact-sieve-optimum/README.md) instantiate the duality sharply for the genuine fourteen-step \(\sqrt6\le D<\sqrt8\) graph:

\[
\boxed{\text{largest universally admissible connected shape}
      =\text{optimal finite principal-sieve component bound}=197.}
\]

This is **not** the maximum component consisting *only of actual irreducible elements*. The unconditional result for that separate graph remains \(90\le B_D\le197\). Under the *unproved* Schinzel H, a separate [conditional note](../sqrt-minus-two-conditional-prime-197/README.md) would give `B_D=197`, but not unconditionally.

## Independent reproducibility

The **abstract minimax theorem requires no computation**: Sections 2–3 of the paper are short complete proofs. The ring-specific sharp197 instantiation uses the previously **published, independently checked exact witnesses**, not an additional unverified solver run. To verify them from this directory:

```sh
(cd ../sqrt-minus-two-universal-sieve-barrier && python3 code/check.py && python3 code/check_projection.py)
(cd ../sqrt-minus-two-exact-sieve-optimum && python3 code/check_exact.py && python3 code/self_test.py)
```

Each linked directory also includes raw data, an audit and SHA256 checks. Full details are listed in [results/REPRODUCTION.md](results/REPRODUCTION.md).

This is AI-assisted written mathematics, not a claim of first discovery, external human refereeing, complete literature review or Lean kernel formalization. The true prime-only maximum remains an explicitly separate open target.
