# Arbitrarily weighted cycle strong Chollet and block extension

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Complete written proof](PAPER.md) · [Actual theorem/verification map](THEOREM_MAP.md).

For every cycle with arbitrary nonnegative real conductances, its actual
weighted Laplacian satisfies strong Chollet for every principal subset,
with weighted degrees taken in the ambient graph. On every odd cycle,

    (product_i d_i) per L - per(L circ L) >= 2 (product_e w_e)^2.

The explicit lower bound is not claimed sharp. Positive odd-cycle
conductances give strict inequality. The new proof for odd lengths at least
five compares two matching moments of independent neighbor choices and uses
the classical triangle-free Motzkin--Straus bound, with its proof included.
The weighted triangle and bipartite support were already known and credited.

The theorem extends to every nonnegative weighted graph whose positive-support
blocks are bipartite or cycles, including all weighted cactus graphs, and to
every nonnegative diagonal addition. All ambient principal subsets, zero
conductances, isolated vertices, disconnected graphs and empty matrices are
included. Published Lieb/strong-closure inputs are disclosed and the closure
calculation is written out. **Arbitrary weighted nonbipartite blocks remain
open here.** This is a complete written proof in the stated range, without
a complete Lean formalization or external peer-review claim.

Reproduce the exact auxiliary diagnostics with Python 3.10+ and its standard library:

```bash
python3 check.py
```

The program uses actual integer/rational Laplacians, Ryser permanents,
ambient principal diagonals and exact neighbor-choice probability laws.
Its finite matrix checks supplement the all-length proof and are not
extrapolated into a universal theorem. Final source hashes and fresh Windows
and WSL records are included; the two runs use the same implementation.

Primary screening read Pant--Singh arXiv:2604.24192v2, Theorems 3.1, 4.3,
5.3 and 5.4; those graph cycle/cactus statements use unweighted Laplacians.
The repository's all-unweighted theorem and existing weighted triangle were
checked before selecting the remaining weighted odd-cycle step. No literature
search certifies first historical discovery. No new Lean build, kernel replay,
Release or DOI is claimed here. Research and writing used OpenAI AI assistants;
no external funding. Copyright 2026 Yongxian Zhang; all rights reserved for
original materials, with existing third-party rights preserved.
