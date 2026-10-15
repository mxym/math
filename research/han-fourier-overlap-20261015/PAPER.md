# A transitive read-once obstruction to Han's Fourier-overlap question

**Complete ordinary written auxiliary proof, independently read in full.** The source-bound internal AI-agent review is recorded in REVIEW.md and FINAL_STATUS_BINDING.json. This does not solve or refute the Fourier entropy–influence conjecture. No formal proof, external human review or priority certification is claimed.

Yongxian Zhang (张永贤), South China University of Technology. 2026-10-15.

## Abstract

Han asks whether every Boolean function has a coordinate whose adjacent Fourier-coefficient overlap is bounded by a universal constant times that coordinate's influence. We construct monotone Boolean read-once formulas on `2^d` variables for which every coordinate has overlap/influence ratio at least `3d/8`. The construction starts with uniform independent bits and uses one common binary AND or OR gate at each level, choosing the gate to keep the output bias bounded. The Fourier entropy–influence conjecture itself remains unaffected: the constructed family lies in a class already known to satisfy that conjecture.

## The original quantifiers

Throughout, `f:{−1,1}^N→{−1,1}`, the input measure is uniform, and

\[
\widehat f(S)=\mathbb E[f(X)\chi_S(X)],\qquad
I_i(f)=\Pr[f(X)\ne f(X^{\oplus i})].
\]

Put

\[
A_i(f)=\sum_{S\subseteq[N]\setminus\{i\}}
|\widehat f(S)\widehat f(S\cup\{i\})|.
\]

[Han, Combinatorica 45, article 4 (2025)](https://link.springer.com/article/10.1007/s00493-024-00133-z), Question 3.1, equation (3.18), also in [arXiv:2312.08271v2](https://arxiv.org/abs/2312.08271v2), asks whether there exists one universal `c>0` such that every Boolean function has some coordinate with `A_i(f)≤c I_i(f)`. The present argument negates this full coordinate-existence statement. Every coordinate of the counterexample is essential, so a zero-influence coordinate cannot satisfy it vacuously.

**Theorem.** For each integer `d≥0` there is a monotone Boolean read-once formula `f_d` on `N_d=2^d` uniform variables such that all coordinates have positive influence and

\[
\frac{A_i(f_d)}{I_i(f_d)}\ge\frac{3d}{8}
=\frac38\log_2N_d \qquad (i\in[N_d]).
\]

Consequently the universal constant requested in Han's Question 3.1 does not exist.

## Construction and bias control

Start with `f_0(x)=x`. Given `f_j`, let `g` and `h` be copies on disjoint variable sets, and write `p_j=Pr(f_j=1)` and `μ_j=2p_j−1`. Define `f_{j+1}` to be `OR(g,h)` if `p_j≤1/2`, and `AND(g,h)` otherwise. Sign encoding gives

\[
\operatorname{AND}(g,h)=\tfrac12(g+h+gh-1),\quad
\operatorname{OR}(g,h)=\tfrac12(g+h-gh+1).
\]

Thus

\[
p_{j+1}=\begin{cases}2p_j-p_j^2,&p_j\le1/2,\\p_j^2,&p_j>1/2.\end{cases}
\]

If `p∈[1/4,1/2]`, its OR image is in `[7/16,3/4]`. If `p∈(1/2,3/4]`, its AND image is in `(1/4,9/16]`. Since `p_0=1/2`, induction proves

\[
1/4\le p_j\le3/4,\quad |\mu_j|\le1/2 \quad(j\ge0).
\]

Each formula is monotone. Its identical-subtree swaps act transitively on its leaves. All coordinates therefore have the same influence, denoted `α_j`, and the same ratio `A_i/I_i`.

## An exact Fourier recurrence

It is convenient first to use the squared-restriction distance

\[
L_i(f)=\sum_T\left|\widehat{f^+}(T)^2-\widehat{f^-}(T)^2\right|.
\]

Writing the corresponding original coefficients as `c_T=hat f(T)` and `d_T=hat f(T∪{i})` gives restriction coefficients `c_T+d_T` and `c_T−d_T`. Therefore

\[
L_i(f)=4\sum_T|c_Td_T|=4A_i(f).
\tag{1}
\]

We compute `L_i` for `F=AND(g,h)`, where `g,h` have disjoint variables and equal mean `μ`, and `i` is a coordinate in `g`. Let `α=I_i(g)`. Monotonicity gives means `u_+=μ+α` and `u_−=μ−α` for the restrictions of `g`. Set `p=(1+μ)/2` and let `ν=E F`.

For nonempty Fourier index `U` in the `g` variables, the coefficients of `F` are `(1+μ)hat g(U)/2` when the `h` index is empty, and `hat g(U)hat h(V)/2` when `V` is nonempty. Parseval in `h` gives the combined multiplier

\[
\tfrac14[(1+\mu)^2+(1-\mu^2)]=p.
\]

Hence those indices contribute `p[L_i(g)−4|μ|α]`, subtracting the old constant-index contribution before multiplying.

For empty `g` index and nonempty `h` index, the restriction coefficients are `(1+u_±)hat h(V)/2`. Their contribution to `L_i(F)` is

\[
\tfrac14|(1+u_+)^2-(1+u_-)^2|(1-\mu^2)
=\alpha(1+\mu)(1-\mu^2).
\]

Finally the mean of `F` depends affinely on the mean of `g`, with slope `p`. Its two restriction means are `ν±pα`, so the new constant-index contribution is `4|ν|pα`. Together with `I_i(F)=pα`, this yields

\[
\frac{L_i(F)}{I_i(F)}
=\frac{L_i(g)}{I_i(g)}-4|\mu|+2(1-\mu^2)+4|\nu|.
\tag{2}
\]

For `OR`, the same calculation replaces `1+μ,p` by `1−μ,1−p`. The nonempty-`h` contribution becomes `α(1−μ)(1−μ²)` and the new influence becomes `(1−p)α`, so equation (2) is unchanged.

In our construction the multiplying influence factor is always in `[1/2,3/4]`; starting with `α_0=1`, every `α_j` is positive. Thus all divisions above are legitimate. The calculation applies to any leaf of either identical child subtree.

## Proof of the theorem

Let `R_j=L_i(f_j)/I_i(f_j)`, independent of `i` by transitivity. A dictator has `R_0=0` and `μ_0=0`. Equation (2) telescopes exactly:

\[
R_d=2\sum_{j=0}^{d-1}(1-\mu_j^2)+4|\mu_d|.
\]

Since `|μ_j|≤1/2`, this is at least `3d/2`. Dividing by 4 using (1) proves `A_i/I_i≥3d/8` for every coordinate. Given any proposed finite `c`, choose an integer `d>8c/3`. Then every coordinate violates the proposed inequality. This proves the negative answer. ∎

## Scope and prior work

The target is Han's adjacent-coefficient overlap condition, not the original FEI inequality `H(hat f²)≤C I(f)`. O'Donnell and Tan already proved FEI for read-once formulas over bounded-arity gates in [arXiv:1304.1347](https://arxiv.org/abs/1304.1347). The present counterexamples use only binary gates and therefore do not refute FEI.

González, MacManus and Pereyra's [arXiv:2606.00246v2](https://arxiv.org/abs/2606.00246v2), Sections4–5, discuss this stronger route and show that a specified bad splitting variable can violate an absolute-spectral-distance inequality. The all-coordinate quantifier is essential here: the transitive construction provides no alternative coordinate satisfying a uniform overlap bound.

The bounded current literature screen read the precise current Han question and these later primary sections, and searched for a prior negative answer. No such primary resolution was identified in that screen. This does not certify priority or replace a full literature review.

The standard-library controls in `han_q31_exact_controls.py` enumerate the complete truth table of this construction through depths0–4. For all 31 coordinates in those five examples, integer Walsh transforms and physical edge counts give identical rational influences; direct restricted truth tables additionally check identity (1), and exact rational arithmetic checks recurrence (2). The earlier NumPy controls in `read_once_proxy_controls.py` cover the same examples. These are consistency checks; the preceding induction proves arbitrary depth without a search or a numerical limit. `TRANSITIVE_READ_ONCE_PROXY_OBSTRUCTION.md` contains the earlier research derivation. These are one result, not two independent solutions.

`HAN_Q31_TARGET_AND_SOURCE_MAP.json` records the exact logical target, proof dependencies, current primary-source screen, actual reading scopes, computational scope and unresolved review status. The frozen review packet binds that map and this text by SHA-256.

## Declarations

No external funding. OpenAI assisted the analysis, computation and preparation of this manuscript. The author is responsible for the mathematical content. Original material: all rights reserved. Existing results and questions remain attributed to their original authors. The complete source-bound internal AI-agent ordinary review has passed. No formalization, external human peer review, submission, Release or DOI is claimed.
