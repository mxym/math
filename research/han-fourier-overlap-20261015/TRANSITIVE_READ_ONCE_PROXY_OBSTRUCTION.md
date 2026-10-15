# The adaptive absolute-spectral-distance proxy fails on every coordinate

Author-only auxiliary proof, recorded while studying full FEI. No independent ordinary review or novelty claim is made. The unrestricted FEI target remains open here.

For a sign-valued Boolean function `f` and a coordinate `i`, define

\[
L_i(f)=\sum_T\left|\widehat{f^+}(T)^2-\widehat{f^-}(T)^2\right|.
\]

We exhibit monotone read-once formulas `f_d` on `2^d` uniform bits such that every coordinate has

\[
\boxed{L_i(f_d)/I_i(f_d)\ge 3d/2.}
\]

Thus there is no universal `K` for the statement “every Boolean function has some positive-influence coordinate satisfying `L_i≤K I_i`.” This concerns an overstrong proxy. Read-once formulas already satisfy FEI by O'Donnell–Tan's composition theorem, so it is not a counterexample to FEI.

## The homogeneous formula

Let `f_0(x)=x`, and let `p_j=P(f_j=+1)` and `μ_j=2p_j−1`. To form `f_{j+1}`, use two independent copies of `f_j` and apply

* `OR₂` if `p_j≤1/2`;
* `AND₂` if `p_j>1/2`.

The same gate is used at every node on a given level. With sign encoding,

\[
\operatorname{AND}(g,h)=(g+h+gh-1)/2,\qquad
\operatorname{OR}(g,h)=(g+h-gh+1)/2.
\]

For `AND`, `p_{j+1}=p_j²`; for `OR`, `p_{j+1}=2p_j−p_j²`. The interval `[1/4,3/4]` is invariant under the stated choice: `AND` sends `(1/2,3/4]` into `(1/4,9/16]`, and `OR` sends `[1/4,1/2]` into `[7/16,3/4]`. Since `p_0=1/2`, all `|μ_j|≤1/2`.

Each formula is monotone. Swapping the two identical child subtrees independently at every node acts transitively on its leaves. Consequently every leaf has the same positive influence `α_j` and the same ratio `R_j=L_i(f_j)/α_j`. Positivity follows either directly from essentiality or from the influence recurrence below.

## Exact local recurrence

Consider `AND(g,h)`, where `g` and `h` have disjoint variable sets and the same mean `μ`, and choose a coordinate `i` in `g`. Let `g+`, `g-` have means `u+`, `u-`. Monotonicity gives

\[
u_+-u_-=2\alpha,\qquad (u_++u_-)/2=\mu,\qquad \alpha=I_i(g)>0.
\]

Split the Fourier coefficients according to whether the `g` index and `h` index are empty. For a nonempty `g` index, summing over all `h` indices multiplies its squared-coefficient difference by

\[
\frac{(1+\mu)^2+(1-\mu^2)}4=p,\qquad p=(1+\mu)/2.
\]

The empty `g` index and nonempty `h` indices contribute

\[
\tfrac14|(1+u_+)^2-(1+u_-)^2|(1-\mu^2)
=\alpha(1+\mu)(1-\mu^2).
\]

The new constant-coefficient difference has magnitude `4|μ_new| p α`, whereas the old constant-coefficient difference, which must be subtracted before multiplying the nonempty part by `p`, has magnitude `4|μ|α`. Also `I_i(AND(g,h))=pα`. Therefore

\[
R_{new}=R_{old}-4|\mu|+2(1-\mu^2)+4|\mu_{new}|.
\]

For `OR`, replace the factors `1+μ` and `p` by `1−μ` and `1−p`. The empty-index contribution is `α(1−μ)(1−μ²)` and the new influence is `(1−p)α`. Division gives **the same recurrence**. All absolute values are retained; no cross term is set to zero.

For a dictator `f_0`, both restrictions have the same squared Fourier law, so `R_0=0` and `μ_0=0`. Telescoping yields the exact identity

\[
R_d=2\sum_{j=0}^{d-1}(1-\mu_j^2)+4|\mu_d|.
\]

Every summand `1−μ_j²` is at least `3/4`, which proves the displayed lower bound `R_d≥3d/2` simultaneously for every leaf coordinate.

## Logical consequence and limits

González–MacManus–Pereyra, [arXiv:2606.00246v2](https://arxiv.org/abs/2606.00246v2), use `L_i` as a sufficient larger quantity for entropy-increment control, with constants adjusted. A generic reduction from the full target to a universal *adaptive* `L_i` bound cannot work: the family above has no acceptable coordinate at large depth.

This proof does not exclude the adaptive **true conditional entropy** bound `Q_i≤K I_i` in `ENTROPY_SPLIT_AND_OPEN_GATE.md`. Replacing squared coefficient differences by their absolute values loses cancellation and quadratic smallness. Numerical values for `Q_i` or actual entropy increments must not be inferred from `R_d`.

Read-once FEI is an existing result: [O'Donnell–Tan, arXiv:1304.1347](https://arxiv.org/abs/1304.1347). The present derivation is retained as an attack-route control, with no assertion of priority or a newly solved major conjecture. Exact integer Walsh controls check all coordinates at depths 0–4 (`1,2,4,8,16` input bits); the proof above, rather than those finite controls, supplies arbitrary depth.

Author: Yongxian Zhang (张永贤), South China University of Technology. No external funding. OpenAI assisted analysis and drafting. All rights reserved for original material; third-party rights and attribution are retained.
