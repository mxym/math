# Six finite Lean checks, partial paper scope

Pinned Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

```sh
bash bootstrap.sh
lake env lean Diffuse.lean
```

- `three_complement_intersection`: two labels, each excluding one of
  three group indices, retain a common index. Finite kernel reduction.
- `three_complement_incidence_count`: each label has exactly two of
  the three replacement indices. Finite kernel reduction.
- `repair_margin`: the actual numerical rank increase L preserves the
  strict finite fractional branch under Delta>D(D-2)L.
- `peak_removal_margin`: a maximum-coordinate violation and L<=1/M
  give the strict repair margin.
- `actual_restriction_budget`: for actual finite blocks A, their
  weights, point p and finite S, sums the real block restriction and
  proves it is bounded by M times the actual sum of pair codegrees.
  The caller supplies the pair-count budget from the paper's separate
  global double count; that double count is not formalized here.
- `odd_set_degree_budget`: the scalar handshake and degree bounds
  imply the odd-set constraint. It does not prove Edmonds's theorem.

All six axiom lists are frozen in `../results/lean-axioms.txt`. No
`sorry`, `sorryAx`, `native_decide` or extra axioms occur. The `decide`
proofs for the three-element index set use normal kernel reduction.

Not formalized: the construction of all repaired hypergraph incidence,
its simplicity, finite LP duality, minimax compactness and convex
perturbation, rounded coordinate cap, predecessor finite bound within
this project, Edmonds's theorem, matching-distribution construction,
Kayll's theorem, and asymptotic/core arguments. Complete written proofs
and explicit imported sources cover these parts. The earlier finite
incidence frontier Lean project remains separate and unchanged.
