# Exact minima for dyadic-32 abelian graph covers

This isolated source archive accompanies catalogue problem **#070**, the Erdős–Gyárfás power-of-two cycle problem. It records two exact extremal questions for **connected regular abelian covers of specified bases**. The dyadic minimum of a graph means the least length of a simple cycle whose length is a power of two.

| Fixed base | Minimum graph order with dyadic minimum 32 | Labeled-base maps at equality | Unlabeled lift graphs at equality |
|---|---:|---:|---:|
| \(K_{3,3}\) | 798 (133 sheets) | 56 | 3 |
| \(K_4\) with one edge subdivided once | 95 (19 sheets) | 4 | 1 |

The proof and exact construction data are in [FactorErdosGyarfasFixedBaseMinima.md](FactorErdosGyarfasFixedBaseMinima.md). Here “labeled-base” means that isomorphisms commute with the projection to the fixed labeled base. When base automorphisms are allowed, the 56 maps in the first row split into \(24,24,8\); exact adjacency-power trace pairs distinguish their three lift graphs. The four maps in the second row form a single class. Below 133 sheets the first census excludes all 166,344,289 kernels; below 19 sheets the second excludes all 4,178.

The earlier cyclic 798-vertex witness motivated the fixed-base minimum computation. Cinna Davis previously gave the [95-vertex witness and universal dyadic bound for the subdivided base](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/erdos-gyarfas-abelian-covers/PROOF.md); the present results prove the minimum across all finite abelian deck groups and the equality classifications. The original fixed-base census was developed by the project research Dreamer; a separate implementation independently rechecked the equality map classification, explicit graph invariants, and the second base, and tested the modular HNF sieve across the ranges below.

## Reproduce

Use Node.js 18 or newer and Python 3.10 or newer from this directory. Only the optional `--arrays` mode uses NumPy. The primary full census and the default independent checks need no third-party package.

```sh
sha256sum -c MANIFEST.sha256
node verify_erdos_gyarfas_k33_hnf.mjs 1 102
node verify_erdos_gyarfas_k33_hnf.mjs 103 133
python3 verify_erdos_gyarfas_fixed_base_independent.py
python3 verify_erdos_gyarfas_fixed_base_independent.py 1 63
python3 verify_erdos_gyarfas_fixed_base_independent.py --arrays 64 102
python3 verify_erdos_gyarfas_fixed_base_independent.py --arrays 103 133
python3 verify_erdos_gyarfas_k33_rooted.py
python3 verify_factor_erdos_gyarfas_two_orbits.py
python3 verify_erdos_gyarfas_class_two.py
```

The primary complete Node replay is partitioned above simply for reproducibility. Its count assertion is independent of the finite loop implementation and its clause shortcut checks that no 16-walk certificate has more than one outstanding collision blocker. The independent default Python command uses the full CRT chart at 133 sheets and literal graphs for the subdivided base. The optional Python HNF sieve takes any inclusive subrange between 1 and 133, with or without NumPy acceleration. The exact ranges actually replayed are listed in [RELEASE_NOTES.md](RELEASE_NOTES.md). These are exact integer computations, not Lean formalizations.

The root result that every vertex of an abelian \(K_{3,3}\) cover belongs to a \(4/8/16/32\)-cycle is included as [supporting context](FactorErdosGyarfasK33Rooted.md), with its elementary abelian subclass counts clearly separate. The [two-orbit lemma](FactorErdosGyarfasAbelianTwoOrbits.md) gives the abelian compression step. The [two-step nilpotent extension](FactorErdosGyarfasClassTwo.md) is included solely for the related existence statement. It does not extend either minimum to nonabelian covers. The reusable enumeration techniques are verification tools, not independent theorem claims.

Neither the general Erdős–Gyárfás conjecture nor unrestricted minima over arbitrary graphs or covering bases are asserted. See [the earlier five-orbit release](https://github.com/mxym/math/releases/tag/erdos-gyarfas-abelian-five-orbit-threshold-v1.0.0) for the separate original project threshold.
