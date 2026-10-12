# Complete classification of independent homogeneous product–join arities

**Research supplement to entry 005 — 7 October 2026.**

The [complete proof](paper.md) extends 005 v5 from balanced recursions `(K^t)^{*t}` to **every** `(K^m)^{*k}`, for arbitrary positive integer `m,k` and simplex seed dimension `p`.

For `K_0=T_p` and `K_{j+1}=(K_j^m)^{*k}`, the asymptotic projection-volume root rate has a **unique** maximum at `(m,k,p)=(2,2,5)`. Every other triple has `log(rate)<131/125`, while the winner satisfies `rate>14267/5000`, inherited from 005 v5. This covers unequal arities and both boundary operations (one product or one join). The full product/join class with arbitrary trees remains open.

The [standalone exact checker](checker.py) replays 6,155 finite competitor exclusions, 19 boundary simplex checks, a 19-case large-product tail, 323 large-join-tail endpoint inequalities, 19 exceptional large-join inequalities, and a global seed-dimension tail. All comparisons are strict rational intervals with certified logarithms and a certified rational enclosure for pi. It runs in a few seconds with Python 3 and no third-party packages.

```sh
python3 notes/unbalanced-homogeneous-projection-recursion/checker.py
python3 -O notes/unbalanced-homogeneous-projection-recursion/checker.py
```

Inherited geometric calculus: [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md). Inherited winner and benchmark: [005 v5](../../preprints/005-simplex-product-optimum/v5/paper.md). New: all independent-arity upper bounds, full four-way infinite-tail proof, exact finite classification, boundary arities. These are not claims of priority, human peer review, or full Lean formalization.

**Parallel verification:** [a separate proof/certificate package](../independent-arity-simplex-recursions/README.md) was also published for the *same* full independent-arity theorem, with different infinite-tail reductions. See the [cross-audit](../../reviews/2026-10-07-independent-arity-parallel-audit.md). It must not be counted as a second mathematical theorem.

## Independent cross-check and further classification

A separately developed [all-arity proof with a distinct cutoff and checker](../independent-arity-simplex-recursions/PROOF.md) establishes **the same** first-place classification. It is independent corroboration, not a second distinct mathematical theorem. That proof has now also been tightened to prove a genuinely stronger [unique second-place classification](../independent-arity-simplex-recursions/SECOND_BEST.md): the runner-up is `(m,k,p)=(2,2,6)`, and every other nonwinning triple has logarithmic rate strictly less than `10479/10000`. The original proof and finite certificates in this directory are preserved apart from correction of one accidental formula-control character in the displayed expression for `J_{m,k,p}`.
