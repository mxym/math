# Independent arities in simplex product/join recursions

**Companion theorem to manuscript 005 v5.**

The [complete proof](PROOF.md) extends the published **balanced**
homogeneous recursion classification \((K^t)^{*t}\) to **all independent
positive integer arities**
\[
K_0=T_p,\qquad K_{j+1}=(K_j^m)^{*k}.
\]

For every positive integer triple \((m,k,p)\) the asymptotic projection
ratio exists. The **unique maximizing triple** is
\[
\boxed{(m,k,p)=(2,2,5).}
\]
Every other triple obeys
\[
\log\Lambda_{m,k,p}<131/125
<\log(14267/5000)<\log\Lambda_{2,2,5}.
\]

This includes the entire unequal-arity family \(m\ne k\), not just a
larger finite search window. The strict winner's lower witness is inherited
from 005 v5; all new exclusions use the proof in this directory.

## Replay

Python 3.10+ standard library; no internet and no additional packages.

From repository root:

```sh
python3 notes/independent-arity-simplex-recursions/check.py
python3 -O notes/independent-arity-simplex-recursions/check.py
python3 preprints/005-simplex-product-optimum/v5/code/check_balanced.py
python3 -O preprints/005-simplex-product-optimum/v5/code/check_balanced.py
```

Expected independent-arity report:

```text
PASS: independent-arity homogeneous recursion classification
finite regular exclusions: 27690
finite three-level exclusions: 209
independent k-tail certificates: 930
analytic tails: m>=32, p>=32, k>=32
winner: (m,k,p)=(2,2,5), inherited lower witness from 005 v5
competitor upper: exp(131/125) < 14267/5000
methods: rational Machin pi, rational atanh log, factorial / Robbins bounds
no float or assertion-dependent checks
```

The two normal/optimized outputs are required to agree byte-for-byte.
The [verification log](results/replay.txt) is a fixed snapshot.
The code uses `fractions.Fraction` and explicit exceptions, plus
finite rational intervals for logarithms and \(\pi\). It separates
finite checks from three proved infinite-parameter reduction lemmas.
It never identifies finite enumeration alone with a universal proof.

## Contribution and limits

This result **strictly extends 005 v5's parameter scope**, rather than
determining the optimum over arbitrary product/join expression trees.
All geometric calculus and the lower witness are imported from 005 v2/v5.
The public OpenAI/math family 088 contains the earlier simplex-product
counterexample; its original proof is a different, finite product test.
The full classification here is supported by the [new derivation](PROOF.md)
and [new exact certificate](check.py).

There is no external human refereeing, full Lean formalization, or
priority/novelty certification. Author attribution is the mxym repository
account with AI-assisted preparation.

**Parallel verification:** [another full proof/certificate package](../unbalanced-homogeneous-projection-recursion/README.md) was published for the *same* independent-arity theorem, with smaller finite core and different tail reductions. The [cross-audit](../../reviews/2026-10-07-independent-arity-parallel-audit.md) records shared inputs, actual overlap and replay results; neither package is a different theorem.

## Sharper second-place result and independent cross-check

The [unique runner-up theorem](SECOND_BEST.md) proves that `(m,k,p)=(2,2,6)` is the only second-best homogeneous simplex recursion. Its [separate exact checker](check_second.py) certifies the strict universal third-place upper threshold `log Λ < 10479/10000` and an exact level-five lower witness for the runner-up. All positive integer triples are covered, including unbounded seed dimension and arities; the original leading orbit remains the unique best.

A [parallel 005 supplement](../unbalanced-homogeneous-projection-recursion/README.md) independently proves the **same first-place theorem** using smaller parameter cutoffs and a different rational interval engine. These two first-place proofs are cross-verification, not separate claimed discoveries. The newly isolated **second-place classification** is additional mathematics.
