# Parallel-proofs reconciliation: independent-arity simplex recursions (005)

**Date:** 7 October 2026 (America/Los_Angeles). **Scope:** model-assisted consistency and reproducibility cross-check; no external mathematical referee report or originality certification.

## One theorem, two disclosures

Two independently maintained proof packages were committed in close succession:

1. [Homogeneous product–join classification](../notes/unbalanced-homogeneous-projection-recursion/README.md), commit [`de012fc`](https://github.com/mxym/math/commit/de012fc48098eda40c61eabce0243d9f8c05707e), with [`paper.md`](../notes/unbalanced-homogeneous-projection-recursion/paper.md) and [`checker.py`](../notes/unbalanced-homogeneous-projection-recursion/checker.py).
2. [Independent-arity simplex recursions](../notes/independent-arity-simplex-recursions/README.md), commit [`b64b11c`](https://github.com/mxym/math/commit/b64b11c978879bda223b77b2c51e28954f585470), with [`PROOF.md`](../notes/independent-arity-simplex-recursions/PROOF.md) and [`check.py`](../notes/independent-arity-simplex-recursions/check.py).

**They prove the same mathematical theorem**, not two separate results: over *all* positive integers `m,k,p`, the fixed-arity recursion `K_0=T_p`, `K_{j+1}=(K_j^m)^{*k}` uniquely maximizes `lim R(K_j)^(1/d_j)` at `(2,2,5)`. Both prove every other triple has logarithmic rate `<131/125` and both inherit the winning lower endpoint `14267/5000` from 005 v5. Neither settles varying arities or arbitrary product/join expression trees. They must **not** be counted as two independent mathematical breakthroughs or two novelty claims.

## Genuine differences in proof and certificate

The two rational implementations and their all-parameter partitions differ substantially:

| Check | `unbalanced-homogeneous-projection-recursion` | `independent-arity-simplex-recursions` |
| --- | --- | --- |
| Large product-arity cutoff | `m>=20`, `1<=p<=19` | `m>=32`, all `p` |
| Large seed cutoff | `p>=20`, all `m,k>=2` | `p>=32`, `2<=m<=31` |
| Large join-arity cutoff | `k>=20`, including special `m=2` tail | `k>=32`, seven special seeds at `m=2` |
| Remaining finite grid | 6,155 losing triples, one winner | 27,690 regular + 209 refined losing triples, one winner |
| Exceptional long-join estimate | One exact-level restart; 19 seed inequalities, two tangent budgets | One exact-level restart; seven seed inequalities |
| `pi` bound | Rational Machin recheck against `333/106 < pi < 355/113` | Rational Machin enclosure used directly |
| Logarithms | 16-term atanh bounds | 18-term atanh bounds |

These are different verification routes for the **same** claim; neither code file simply invokes the other checker. Both use the same published 005 v2 product/join calculus and the same pinned 005 v5 winner. They are therefore not entirely independent proofs of the geometric input. No claim is made that either manuscript was developed without exposure to the other; the Git history establishes only the disclosure order.

## Commands and observed outcomes

From repository root, these commands were run successfully on the current publication sources:

```sh
python3 notes/unbalanced-homogeneous-projection-recursion/checker.py
python3 -O notes/unbalanced-homogeneous-projection-recursion/checker.py
python3 notes/independent-arity-simplex-recursions/check.py
python3 -O notes/independent-arity-simplex-recursions/check.py
python3 -O preprints/005-simplex-product-optimum/v5/code/check_balanced.py
python3 notes/unbalanced-homogeneous-projection-recursion/negative_controls.py
```

The second package's optimized output was byte-compared against its tracked `results/replay.txt`, and the first package's normal and optimized outputs were compared as part of its initial release. All checks passed. Both packages' `SHA256SUMS` inventories passed `sha256sum -c` using the corresponding file-relative paths. The first package's three negative controls each produced the expected exception.

### Mathematical trust boundary

The code checks rational finite comparisons, exact rational logarithm intervals, Machin pi bounds and exceptions. Both *general* theorems also rely on written infinite-tail monotonicity, Robbins--Stirling, and the previously published geometric calculus; finite numerical success alone cannot validate those steps. The review compared the infinite-tail parameter partitions and inspected their key inequalities, but has **not** machine-formalized each inference or provided a human peer-review certificate. No discrepancy between the two statements or finite certificates was identified in this review.

## Next research target

The natural remaining problem is the full point-generated product–join class with **variable operations** (including unequal subtrees or periodic and aperiodic operations). Its known upper Bellman envelope is separate; neither homogeneous theorem establishes equality for this larger class. The two exact checkers remain useful as regression tests while work on the unrestricted operation grammar continues.
