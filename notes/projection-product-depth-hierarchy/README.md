# Exact second-level projection spectrum and a strict hierarchy at every product depth

**Research continuation of entry 005 — 8 October 2026.**

[Complete mathematical proof](paper.md) · [Independent exact finite/infinite checker](code/check_depth2.py) · [Separate finite certificate producer](code/produce_finite.py) · [1,214 exact winning split records](certificates/finite_splits.tsv) · [Reproduction/audit scope](AUDIT.md).

## Two substantial theorems

**A. A strict infinite product-depth hierarchy.** Define product depth as the greatest number of Cartesian-product nodes along a root-to-leaf path; joins do not increase it. For **every** integer `k>=0`, the point-generated product/join class of depth at most `k` has an **attained** and **exactly computable algebraic** spectral maximum `lambda_k`. The hierarchy is strictly increasing:

\[
\boxed{1=\lambda_0<\lambda_1<\lambda_2<\cdots<\lambda_k<\lambda_{k+1}<\cdots\nearrow\lambda_*<\infty.}
\]

The asymptotic projection-body root growth rates satisfy `Gamma_k=e*lambda_k`. Consequently **no finite bounded product depth attains the full recursive-class spectral rate**. More strongly, its sharp dimension-`d` maximum loses by an **exponential factor** against the unrestricted class as `d` grows, with a rigorously positive, exactly computable base at least `lambda_(k+1)/lambda_k>1`. If an optimizer at depth `k` has augmented dimension `D_k`, the new strict lower increment is `log(lambda_(k+1)/lambda_k)>1/[2*D_k^2*(2*D_k^2-1)]`, providing an explicit dimension-only rational gap. The proof uses a uniform Robbins sublinear product correction and an explicit central-binomial operator that raises a finite maximizer's depth by one while strictly increasing its spectral value. An effective tail cutoff makes the exact optimum at every *fixed* depth recursively computable, though no practical runtime guarantee is claimed. The full limit `lambda_*` is still unknown.

**B. Exact all-dimensional classification at depth two.** Allow *arbitrary finite joins* and at most two nontrivial nested Cartesian-product operations along a path, with no balance, dimension or homogeneity restriction. The unique maximizing **primitive product state** is

\[
P=X\times X,\quad X=(T_5\times T_5)*(T_5\times T_5),\quad
\dim P=42,\quad
Q(P)=\frac{257554342358885086515}{36893488147419103232}.
\]

Thus the exact spectral growth constant at depth two is

\[
\boxed{\lambda_2=Q(P)^{1/43},\qquad \Gamma_2=e Q(P)^{1/43}.}
\]

The previous depth-one optimum is `lambda_1=(189/128)^(1/11)`. The checker proves `lambda_2>lambda_1` by exact rational powers, and independently verifies a third-depth witness strictly better than `lambda_2`. There is **no extrapolation from a bounded numerical sample**: the infinite cases are proved analytically, and the remaining finite core contains precisely 1,214 dimension splits and 2,770,504 exact candidate products. Only one winning invariant-state split survives, `(r,s)=(21,21)` with both factors in state `(H,Q)=(12,(189/128)^2)`. We do **not** claim geometric uniqueness of all affine representatives.

## Reproduction

Python 3.10+ standard library only, from repository root:

```sh
# Replay the independently published depth-one Pareto state certificate:
python3 notes/projection-persistent-nesting-gap/code/check.py

# Re-evaluate every primitive depth-two candidate and the analytic tail constants:
python3 notes/projection-product-depth-hierarchy/code/check_depth2.py
python3 -O notes/projection-product-depth-hierarchy/code/check_depth2.py

# Deliberate corruptions must be rejected; verify all pinned package bytes:
python3 notes/projection-product-depth-hierarchy/code/negative_controls.py
(cd notes/projection-product-depth-hierarchy && sha256sum -c SHA256SUMS)
```

Optional exact regeneration of the static 1,214-row finite certificate:

```sh
python3 notes/projection-product-depth-hierarchy/code/produce_finite.py
(cd notes/projection-product-depth-hierarchy && sha256sum -c SHA256SUMS)
```

The independent checker reads the *prior fully certified* depth-one Pareto data using fixed SHA-256 source checks, computes every candidate's rational `Q`, compares exact integer powers, and independently agrees with the producer's winning indices and `Q` values. It also verifies rational atanh logarithm intervals, the rigorous pi bound, both unbounded parameter tails and the strict third-level example. The ordinary and optimized Python outputs must agree byte for byte, and hostile corrupted inputs must be rejected.

## Trust and scope

The geometric product/join calculus is inherited from 005 v2 (which credits the OpenAI/math family 088 product mechanism), while the two sharp depth-one inequalities are inherited from the [two-layer sharp spectrum](../two-layer-projection-depth-separation/paper.md). The full-depth Bellman ceiling guaranteeing finite `lambda_*` is also existing 005 work. **New in this supplement** are the strict infinite nesting hierarchy with finite attainment/effective exact computation at every finite depth, and the complete second-level spectral classification across **all dimensions** with its exact proof certificate.

The exact value of the full unrestricted product/join supremum remains open, as does the classification of all geometric equality cases or all larger-depth constants. This is AI-assisted research with a written analytic proof and replayable rational arithmetic, **not** external human peer review, full proof-assistant formalization or a priority claim.
