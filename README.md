# Eight-variable Boolean quartics are affine on an affine four-flat

**Theorem (finite, classification-dependent proof).** Every Boolean function of algebraic degree at most four on eight variables restricts to an affine function on some affine subspace of dimension four. Thus it is normal or weakly normal in the terminology of Gillot, Langevin and Polujan (GLP). The word *affine* includes the constant functions; we do **not** assert that a constant four-flat always exists. There is no statement about degrees five and above or higher numbers of variables.

This is the conjecture posed in [GLP, 2024](https://arxiv.org/abs/2407.14038) and on the [authors’ supplementary page](https://langevin.univ-tln.fr/project/indice/indice.html). Their [journal paper, 2026, Theorem 7](https://doi.org/10.1109/TIT.2026.3685370) proves the bent subclass, not the entire quartic case. Here the non-bent case is eliminated by all hyperplane restrictions jointly and an analytic peak-set obstruction. See [the proof](PROOF.md) for the finite checks, their completeness, and where the published classifications enter.

**External dependencies.** (1) GLP's exhaustive cover of abnormal seven-variable functions of degree at most four, under extended-affine equivalence, in particular that there are no cubic exceptions. (2) The complete eight-variable classification of quartic leading forms, not of full quartic functions; the 7-variable table labels restrictions. (3) The eight-variable bent subclass, either the journal theorem or its [separate replacement check](https://github.com/mxym/math/tree/f6409cb23f85261d10af618bbbc9275885ab5d76/research/euclidean-tensor-geometry/theoretical-cryptography/eight-variable-bent-normality-repair). No computation here assumes the published intermediate count of 30 expandable classes. Input-file integrity and the calculations on those inputs are checked; the two published cover/exhaustiveness results are not regenerated from scratch. A missing orbit in a source cover would matter; duplicate representatives do not.

**Attribution and reproducibility.** Obtain the following public data directly from the authors' servers; they are **not redistributed**. The two header data files are the ANF-format downloads in the authors' [B(s,t,m) data directory](https://langevin.univ-tln.fr/data/bst/), not the differently formatted files from 2007. Their ordering fixes all zero-based record IDs below. For background see the [eight-variable project](https://langevin.univ-tln.fr/project/quartics/) (Langevin, Leander, Rabizzoni, Véron, Zanotti; with Hou's class count) and [Gillot–Langevin seven-variable project](https://langevin.univ-tln.fr/project/agl7/aglclass.html).

| Local name | Source file | SHA-256 |
|---|---|---|
| ab7.txt | [GLP, 39,952-record cover](https://langevin.univ-tln.fr/project/indice/rd2-4-7.txt) | fc58fe0b3b11b67056ebb5f49c58aea8b338edb8d9cda9313d15494850dc7c80 |
| q7.dat | [B-4-4-7.dat](https://langevin.univ-tln.fr/data/bst/B-4-4-7.dat) | 6dd6570fc71bf535c6a7ebe4e1733e01d3efa5c72812e01ec9e296fe1aa8c0eb |
| q8.dat | [B-4-4-8.dat](https://langevin.univ-tln.fr/data/bst/B-4-4-8.dat) | 2b403fc9fd57a72b8587f3f06e3e2f93fed044db4f22bdc2fdc9ef2a5c9a3885 |

Run on Linux with Python 3.10+, NumPy, and g++ supporting C++17. No network is used by the verifier. Do not disable assertions. To retain computed certificates use a directory name that does not yet exist:

```sh
python3 verify.py ab7.txt q7.dat q8.dat --keep reproduced
```

The two ANF/Walsh routes check every signed coefficient of every source record. Two exterior-algebra routes compute each of the 254,490 hyperplane restrictions of leading forms independently. The Python and C++ integer sieves separately enumerate all full-spectrum candidates and implement the restriction-count join. No floating-point LP, solver, heuristic cutoff or probabilistic test enters. The check includes signed-slice identities and a corrupted intermediate table as a negative control. The manifest of derived files is printed by the verifier. The complete local spectrum table and all 28 global histogram candidates are produced by this command, not hard-coded inputs.
