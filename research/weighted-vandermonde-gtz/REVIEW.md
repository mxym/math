# Independent internal review and reproduction

The proof in [the research note](README.md) and a separate adversarial review were AI-assisted. This is not an external referee report, formal verification, or a priority determination.

## Checks of the proof

1. **Support and weights.** Merging equal nodes preserves the weighted moment measure and retains a genuine original index at the largest weight. The constant moment forces every nonzero dependence to have both signs. The sign of its ordinary mass change may be chosen before moving to a boundary point, so the remaining mass does not increase. Division by this mass strengthens the target; the preserved positive definite moment matrix prevents fewer than $r$ distinct survivors. Zero probabilities, even when the limiting target is singular, follow by taking a fixed successful subset along a subsequence.
2. **Duality and induction.** Using an orthonormal complement gives the contraction in the proof. Separately, for a real input matrix $F$, put $D=\operatorname{diag}(p)$ and let the columns of $R$ form any basis of $\ker(F^tD)$. For an $r$-set $I$ with complement $J$, the original criterion is equivalent to
   $$
   R^t\operatorname{diag}\!\left(\frac{p_i(\mathbf{1}_{i\in J}-p_i)}{1-p_i}\right)R\succeq0.
   $$
   Indeed $D^{1/2}R$ is an unnormalized complement, and the weighted test is invariant under invertible column changes. This gives a rational test independent of the construction of the Vandermonde dual. Polynomial duality itself only uses the interpolation-residue identity through degree $q-2$. The sign of $P'(x_i)$ has no effect on row outer products. The cases $r=1$ and $q=r$ avoid division by $1-p_i$, and after compression $q-r<r$.
3. **Complex scope.** The generalized circle can be sent to the real line with its pole off the finite node set, by an invertible map on homogeneous degree-$r-1$ forms. The resulting nonzero row factors pull back to precisely the original fixed weights. The Fourier consequence covers contiguous bands, including restriction and rewhitening; it does not concern arbitrary Fourier columns or arbitrary complex isometries.
4. **Sharpness.** Every nonsingular choice in the duplicated construction has its row Gram minus $I_r/n$ congruent to $I_r-\mathbf1\mathbf1^t/r$, hence positive semidefinite with nullity exactly one. Other choices are singular. Continuity of the maximum, over finitely many subsets, of their smallest singular values proves the sharp limiting bound even when duplicate nodes are forbidden.
5. **Quadratic span.** In the general real-row argument, applying the trace forces both signs in each nonzero covariance relation among nonzero rows. If the dimension of the linear span of the outer products is at most $r+2$, the reduced dual rank is at most two; every real rank-two system can be put in the affine polynomial chart. A nonzero homogeneous conic relation in rank three cuts the six-dimensional quadratic span to at most five, also for a reducible conic. The remaining six-atom test is *weighted*, not simply the six-row uniform case.
6. **Related but distinct statistical designs.** Saturated design results on intervals, e.g. [Dette–Melas](https://arxiv.org/abs/1105.3575), allow nodes to move. Even allowing free probabilities on the fixed sample is not enough to dominate the original information matrix on a saturated support. For $r=2$, take $x=0,\sqrt3,-\sqrt3$, $w(x)=(1+x^2)^{-1}$, and uniform probabilities. The three row projectors have trace one and average $I_2/2$. A convex combination of two projectors dominating this average would have to equal it by the trace, which requires an orthogonal pair. No pair is orthogonal. The **unnormalized** sum of two selected projectors, as in the theorem, works: its eigenvalues are $1/2$ and $3/2$. The selected subset need not work simultaneously for all probability vectors.

## Reproduce

Run from this directory with Python 3:

```sh
python verify.py
python verify_independent.py
```

The first script is standard-library only. It constructs the subset over rational inputs and checks the output against the **original** weighted Gram matrix using all principal minors: 120 cases in ranks 1–6. It also verifies exact saturation for all nonsingular choices in repeated-node examples of ranks 1–5.

The second script uses SymPy (tested with 1.14.0). It does **not** import the selector or its PSD test. It uses rational nullspaces, exhaustive subsets and exact semidefinite elimination, including zero pivots. Results:

| Test | Coverage |
| --- | --- |
| General weighted complement equivalence | 524 candidate subsets: 168 feasible and 356 infeasible on both sides |
| Brute-force original-node inequality | 20 instances and 985 subsets at distinct nodes; 227 feasible, at least one per instance |
| Complex Cayley change of variables | 24 exact per-observation Hermitian congruences |
| Unequal-multiplicity sharpness | 20 group omissions, ranks 1–5, each with nullity exactly one |

The cases include repeated and closely spaced nodes, extreme positive masses, zero rows in general complement tests, and singular limiting probability targets. Finite checks supplement the proof; they do not establish the theorem on their own.
