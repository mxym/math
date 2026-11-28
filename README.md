# Dyadic cycles in graphs with at most six free abelian orbits

This source slice combines the quotient classification and exact cover censuses for problem #070, the Erdős–Gyárfás power-of-two cycle problem. All graphs in the main theorem are nonempty, finite and simple. The abelian action is **free**: no nonidentity group element fixes a vertex.

**Main result.** Let \(G\) have minimum degree at least three and admit a free abelian action with at most six vertex orbits. If \(G\) has no cycle of length \(4\), \(8\) or \(16\), it has exactly six orbits, and the quotient is the **simple \(K_{3,3}\)**: every base edge comes from one translation matching, with no internal edges. In particular \(G\) is cubic and bipartite, and each graph component is a connected regular abelian cover of this quotient. Every vertex lies on a simple 32-cycle. The smallest possible order in this whole class is **798**, attained by **three nonisomorphic graphs**.

The [general six-orbit proof](FactorErdosGyarfasGeneralSixOrbitClassification.md) does not assume that the graph is bipartite or that a specified bipartition is preserved by the action. It uses quotient reduction and finite exact integer-relation certificates valid for all finite abelian deck groups. Smaller cases ([two](FactorErdosGyarfasAbelianTwoOrbits.md), [three](FactorErdosGyarfasAbelianThreeOrbits.md), [four](FactorErdosGyarfasAbelianFourOrbits.md), [five](FactorErdosGyarfasAbelianFiveOrbits.md)), the [rooted \(K_{3,3}\) theorem](FactorErdosGyarfasK33Rooted.md) and the fixed-base census below complete the argument. The former [part-preserving result](FactorErdosGyarfasSixLayerExtremalQuotient.md) is supporting evidence and a shorter proof on a smaller domain. No claim is made about arbitrary graphs or actions beyond six orbits.

## Exact fixed-base results

| Base of a connected regular abelian cover | Minimum lift order with shortest dyadic cycle 32 | Labeled-base maps at equality | Nonisomorphic lift graphs |
|---|---:|---:|---:|
| \(K_{3,3}\) | 798 (133 sheets) | 56 | 3 |
| \(K_4\) with one edge subdivided once | 95 (19 sheets) | 4 | 1 |

See [the fixed-base proof and census](FactorErdosGyarfasFixedBaseMinima.md). The second base has a degree-two vertex, so its 95-vertex minimum is not in the main minimum-degree-three class. The 19-sheet witness is due to [Cinna Davis](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/erdos-gyarfas-abelian-covers/PROOF.md); the exact minimum and equality count are separate conclusions. The earlier cyclic 798-vertex example motivated the first census. The [class-two companion](FactorErdosGyarfasClassTwo.md) is a supporting existence theorem, not a nonabelian extremal result.

## Reproduce in this directory

Use normal Python 3.10+ (not optimized mode) and Node.js 18+. The independent general six-orbit checker uses SymPy. Optional dense-array fixed-base checks use NumPy; the main proof and default fixed-base commands have neither dependency. Read [the replay notes](RELEASE_NOTES.md) for completed check ranges and scope. The complete Node lower-index census is substantially slower than the quotient and equality checks.

```sh
sha256sum -c MANIFEST.sha256
python3 verify_erdos_gyarfas_general_six_orbits.py
python3 six-orbit-general-independent-review.py "$(cat erdos_gyarfas_general_six_orbit_certificate.json)"
python3 verify_factor_erdos_gyarfas_two_orbits.py
python3 verify_factor_erdos_gyarfas_three_orbits.py
python3 verify_factor_erdos_gyarfas_four_orbits.py
python3 verify_factor_erdos_gyarfas_five_orbits.py
python3 verify_erdos_gyarfas_k33_rooted.py
python3 verify_erdos_gyarfas_fixed_base_independent.py
node verify_erdos_gyarfas_k33_hnf.mjs 1 102
node verify_erdos_gyarfas_k33_hnf.mjs 103 133
```

The supporting part-preserving and class-two replays are listed in [the replay notes](RELEASE_NOTES.md). The programs are reproducibility artifacts, not separate mathematical claims and not Lean formalizations.
