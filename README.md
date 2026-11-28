# Exact dyadic-extremal classification for six-layer bipartite abelian actions

This source slice combines the fixed-base censuses and the stronger quotient result for catalogue problem **#070**, the Erdős–Gyárfás power-of-two cycle problem. All graphs here are finite and simple. “Free” means that no nonidentity group element fixes a vertex.

**Main result.** Let a nonempty bipartite graph of minimum degree at least three admit a free abelian action on at most six vertex orbits which preserves both parts. If it has no simple cycle of length 4, 8, or 16, the quotient is the **simple \(K_{3,3}\)**. Each graph component is a regular abelian cover of this quotient and every vertex lies on a 32-cycle. Consequently in this whole action class the minimum graph order with shortest dyadic cycle 32 is **798**, and there are **three nonisomorphic lift graphs** at equality.

The first part is proved in [the six-layer quotient classification](FactorErdosGyarfasSixLayerExtremalQuotient.md). The proof reduces the orbit multiplicities to three cubic matrices, rules out the two doubled matrices by finite universal integer-relation certificates, and rules out an extra matching on \(K_{3,3}\) by a direct sixteen-cycle argument. The same conclusion holds component by component even if the original graph is disconnected. The theorem does not apply to actions which interchange the two sides, or to arbitrary graphs of minimum degree three.

## Exact fixed-base results included

| Connected regular abelian cover of | Minimum order whose shortest dyadic cycle is 32 | Labeled-base maps at equality | Nonisomorphic lift graphs |
|---|---:|---:|---:|
| \(K_{3,3}\) | 798 (133 sheets) | 56 | 3 |
| \(K_4\) with one edge subdivided once | 95 (19 sheets) | 4 | 1 |

See [the fixed-base proof and census](FactorErdosGyarfasFixedBaseMinima.md). The once-subdivided tetrahedron has a degree-two vertex, so its minimum is a separate fixed-base result, not a candidate in the main minimum-degree-three class. Cinna Davis gave the [earlier 95-vertex example and its upper dyadic bound](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/erdos-gyarfas-abelian-covers/PROOF.md). The earlier cyclic 798 witness already motivated the larger enumeration. The increments are the two precise minima and equality classification, and the new proof carrying the first minimum to the whole part-preserving free-action class.

The [rooted \(K_{3,3}\) theorem](FactorErdosGyarfasK33Rooted.md) connects the two pieces. The [two-orbit lemma](FactorErdosGyarfasAbelianTwoOrbits.md) is a needed compression tool. The [four-fiber reduction appendix](BipartiteFourFiberReduction.md) allows the small-quotient reduction to be checked from one old short certificate, in place of using the full general five-orbit theorem. The [class-two companion](FactorErdosGyarfasClassTwo.md) is an existence extension, not a nonabelian equality claim.

## Reproduce

Use Node.js 18 or newer and Python 3.10 or newer from this directory. Only optional `--arrays` uses NumPy. The main checker reads exact certificate data but neither searches a bounded list of deck groups nor assumes prime-order voltages.

```sh
sha256sum -c MANIFEST.sha256
node verify_erdos_gyarfas_six_layer_extremal.mjs
python3 verify_erdos_gyarfas_six_layer_extremal_independent.py
python3 verify_erdos_gyarfas_bipartite_four_corner.py
node verify_erdos_gyarfas_k33_hnf.mjs 1 102
node verify_erdos_gyarfas_k33_hnf.mjs 103 133
python3 verify_erdos_gyarfas_fixed_base_independent.py
python3 verify_erdos_gyarfas_k33_rooted.py
python3 verify_factor_erdos_gyarfas_two_orbits.py
python3 verify_erdos_gyarfas_class_two.py
```

Exact provenance, independent full HNF and equality-case receipts, and optional index-bounded replays are recorded in [RELEASE_NOTES.md](RELEASE_NOTES.md). The algorithms are reusable verification evidence, not separately released claims and not Lean formalizations.
