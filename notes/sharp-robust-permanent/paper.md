# Sharp-order robustness of permutation permanent inequalities under uniform-marginal perturbations

**Status:** complete mathematical proof draft, independently checkable from the displayed arguments and the cited Bristiel--Caputo permanent inequality; not a Lean formalization or an external peer review.

**Date:** 2026-10-07. **Scope:** all fixed integers `n >= 3`; arbitrary (not necessarily conjugation-invariant) laws on `S_n`; independent, nonidentically distributed tensor products.

## 1. Definitions and main theorem

Write `u` for uniform probability measure on the symmetric group `S_n`. For a probability measure `nu` on `S_n`, let

```math
\|\nu-u\|_{\mathrm{TV}}=\tfrac12\sum_{\pi\in S_n}|\nu(\pi)-1/n!|.
```

Say that `nu` has **uniform one-point marginals** if `nu{pi:pi(i)=j}=1/n` for every `i,j in [n]`. All functions below are nonnegative, and

```math
\|f\|_p=\left(\frac1n\sum_{j=1}^n f(j)^p\right)^{1/p},
\qquad
P_\nu(f_1,\ldots,f_n)=\mathbb E_{\pi\sim\nu}\prod_{i=1}^n f_i(\pi(i)).
```

Set

```math
q_n=\frac{n\log n}{\log(n!)},\qquad
B_n=(1+2n)^{n-1}-1,\qquad
r_n(p)=\frac{p-q_n}{4n^4 B_n}.
```

**Theorem 1 (quantitative sharp-order robustness).** Let `n >= 3`.

1. If `q_n < p <= 2` and `nu` has uniform one-point marginals with `TV(nu,u)<r_n(p)`, then for all `f_1,...,f_n >= 0`,
   ```math
   P_\nu(f_1,\ldots,f_n)\leq\prod_{i=1}^n\|f_i\|_p. \tag{1}
   ```
   Apart from a zero function, equality is possible only when every `f_i` is constant. The lower radius is **explicit** and linear in `p-q_n`.
2. The same inequality holds for any `p>=2` if `TV(nu,u)<r_n(2)`, because normalized `L^p` norms increase with `p`.
3. The uniform-marginal hypothesis is necessary for (1) at any finite exponent `p>1` (regardless of closeness to `u`).
4. This exponent range is optimal for a **whole uniform-marginal TV neighborhood**: when `p<q_n`, (1) fails even at `nu=u`; at `p=q_n` it fails for uniform-marginal measures arbitrarily close to `u`.
5. Let `R_n(p)` be the supremum of radii `r` for which (1) holds for every uniform-marginal measure at TV distance `<r`. For `q_n<p<=2`,
   ```math
   \frac{p-q_n}{4n^4B_n}\le R_n(p)
       \le n\left(n^{-n/p}-\frac1{n!}\right). \tag{2}
   ```
   Consequently `R_n(p)=Theta_n(p-q_n)` as `p downarrow q_n`, with explicit positive lower and upper coefficients.

**Theorem 2 (tensorization).** Fix `n>=3` and `p` and a perturbation radius as in Theorem 1. Let `nu_1,...,nu_b` be potentially distinct uniform-one-point-marginal permutation laws on `S_n`, each within that radius of `u`, and let `pi_l ~ nu_l` be independent. Then every `F_i:[n]^b -> [0,infinity)` satisfies

```math
\mathbb E\prod_{i=1}^n F_i(\pi_1(i),\ldots,\pi_b(i))
\le \prod_{i=1}^n\left(n^{-b}\sum_{x\in[n]^b}F_i(x)^p\right)^{1/p}. \tag{3}
```

## 2. Precise inherited input

Bristiel and Caputo, *Entropy inequalities for random walks and permutations*, **Annales de l'Institut Henri Poincare, Probabilites et Statistiques** 60 (2024), Corollary 1.14, DOI `10.1214/22-AIHP1267`, prove the sharp row-norm upper bound on the permanent. At the critical exponent `q_n`, their result, rewritten with **normalized** counting norms, is

```math
P_u(f_1,\ldots,f_n)\le \prod_{i=1}^n\|f_i\|_{q_n}. \tag{BC}
```

We **do not** reprove (BC), claim to have discovered its optimal uniform exponent, or use an unverified equality classification at `q_n`. The independent contribution of this note is a fully quantitative uniform-marginal perturbation theorem with an optimal-order stability radius and its nonidentically distributed tensorization. OpenAI's September 26, 2026 manuscript *A strict four-row permanent inequality and permutation moments*, Section 2, obtains an unspecified exponent `p_0 in (4/3,2)` and unspecified perturbation tolerance for `n=4` by a different, local-plus-compactness argument. Its four-row setting motivates the present all-`n` question.

For `n>=3`, `1<q_n<2`: the lower inequality follows from `n!<n^{n-1}`; the upper one follows by pairing factors `j(n+1-j)>=n` and, in the odd case, using the central factor `(n+1)/2>sqrt(n)`. At least one inequality is strict.

## 3. Quantitative improvement of normalized L^p over L^q

**Lemma 3.** Let `n>=2`, `1<=q<p<=2`, and `f:[n]->[0,infinity)` have `||f||_p=1`. With `m=(1/n)sum_j f(j)` and `V=(1/n)sum_j(f(j)-m)^2`, one has

```math
1-\|f\|_q\ge\frac{p-q}{8n^3}V. \tag{4}
```

**Proof.** Put `X_j=f(j)^p` and `alpha=q/p in (0,1)`. Since `(1/n)sum X_j=1`, every `X_j in [0,n]`. The function `t^alpha` has second derivative at most `-alpha(1-alpha)n^{alpha-2}` for `0<t<=n`. Taylor's theorem around `t=1`, extended continuously at `0`, gives

```math
t^\alpha\le1+\alpha(t-1)
-\tfrac12\alpha(1-\alpha)n^{\alpha-2}(t-1)^2
\quad(0\le t\le n).
```

Averaging and using `E X=1` yields

```math
1-\|f\|_q^q
\ge \tfrac12\alpha(1-\alpha)n^{\alpha-2}\operatorname{Var}(f^p). \tag{5}
```

Let `M=max_j f(j)>=1` and choose an index `j_*` with `f(j_*)=M`. Because `p>=1` and `0<=x<=M`,

```math
M^p-x^p\ge M^{p-1}(M-x)\ge M-x.
```

Using the identity `Var(h)=n^{-2} sum_{i<j}(h_i-h_j)^2` and retaining only pairs involving `j_*`,

```math
\operatorname{Var}(f^p)
\ge n^{-2}\sum_j(M^p-f(j)^p)^2
\ge n^{-2}\sum_j(M-f(j))^2
\ge V/n. \tag{6}
```

Finally, `0<=||f||_q<=1` and `q>=1` imply `1-||f||_q >= (1-||f||_q^q)/q`. Combining (5)--(6) and `alpha(1-alpha)/q=(p-q)/p^2` gives

```math
1-\|f\|_q\ge\frac{p-q}{2p^2}n^{q/p-3}V
\ge \frac{p-q}{8n^3}V,
```

since `p<=2` and `n^{q/p}>=1`. QED.

## 4. Proof of Theorem 1

Assume no `f_i` is identically zero. By homogeneity normalize `||f_i||_p=1`. Define

```math
m_i=n^{-1}\sum_j f_i(j),\quad g_i=f_i-m_i,\quad
V_i=n^{-1}\sum_jg_i(j)^2,\quad V=\sum_i V_i.
```

Each `0<m_i<=1`, `0<=f_i(j)<=n^{1/p}<=n`, and `||g_i||_infty<=n+1<=2n`. From (BC) and Lemma 3,

```math
\begin{aligned}
1-P_u(f_1,\ldots,f_n)
&\ge 1-\prod_i\|f_i\|_{q_n}\
&\ge \frac1n\sum_i(1-\|f_i\|_{q_n})
\ge \frac{p-q_n}{8n^4}V. \tag{7}
\end{aligned}
```

The middle inequality uses `0<=||f_i||_q<=1` and `1-prod a_i >= max_i(1-a_i) >= n^{-1}sum_i(1-a_i)`.

We now bound the perturbation **quadratically** in the deviations. Expand

```math
\prod_{i=1}^nf_i(\pi(i))
=\sum_{S\subseteq[n]}
 \Big(\prod_{j\notin S}m_j\Big)
 \prod_{i\in S}g_i(\pi(i)).
```

The constant terms cancel between `nu` and `u`. Terms with `|S|=1` also cancel by exact uniform one-point marginals. For any set `S` of size `s>=2`, select two distinct indices `a,b in S`. Since `||g_i||_infty<=sqrt(n V_i)`,

```math
\left\|\prod_{i\in S}g_i(\pi(i))\right\|_\infty
\le n(2n)^{s-2}\sqrt{V_aV_b}
\le \frac n2(2n)^{s-2}\sum_{i\in S}V_i.
```

Writing `delta=TV(nu,u)` and using `|E_nu H-E_u H|<=2delta||H||_infty` and `prod_{j notin S}m_j<=1`,

```math
|P_\nu(f_1,\ldots,f_n)-P_u(f_1,\ldots,f_n)|
\le \delta n\sum_{\substack{S\subseteq[n]\\|S|\ge2}}
(2n)^{|S|-2}\sum_{i\in S}V_i.
```

For each fixed `i` the coefficient in the subset sum is

```math
\sum_{s=2}^n\binom{n-1}{s-1}(2n)^{s-2}
=\frac{(1+2n)^{n-1}-1}{2n}
=\frac{B_n}{2n}.
```

Therefore

```math
|P_\nu(f_1,\ldots,f_n)-P_u(f_1,\ldots,f_n)|
\le\frac{\delta B_n}{2}V. \tag{8}
```

Combining (7) and (8) proves the quantitative **deficit estimate**

```math
1-P_\nu(f_1,\ldots,f_n)
\ge\left(\frac{p-q_n}{8n^4}-\frac{\delta B_n}{2}\right)
\sum_{i=1}^n\operatorname{Var}(f_i). \tag{9}
```

When `delta<r_n(p)` the coefficient is positive. Hence (1) holds, and equality with nonzero functions forces `V_i=0` for all `i`, i.e. every row function is constant. Conversely constant functions give equality. The `p>=2` case follows by monotonicity of counting norms. This proves parts 1--2.

For necessity of uniform one-point marginals, if the marginal of `pi(i)` is not uniform, there is a mean-zero `g:[n]->R` with `E_nu g(pi(i))>0`. Put `f_i=1+t g` for sufficiently small `t>0` and let every other function be `1`. The left side of (1) has first derivative `E_nu g(pi(i))>0` at `t=0`, while `||1+t g||_p` has derivative `E_u g=0`. This contradicts (1), proving part 3.

For parts 4--5, set `C_n=< (1\ 2\ ...\ n) >`, the cyclic regular subgroup, let `w_n` be uniform on `C_n`, and consider `nu_t=(1-t)u+t w_n`. Both laws have uniform one-point marginals, and

```math
\|\nu_t-u\|_{TV}=t\left(1-\frac n{n!}\right),\qquad
\nu_t(\mathrm{id})=\frac{1-t}{n!}+\frac tn. \tag{10}
```

Choose `f_i=1_{\{i\}}`. The left side of (1) is `nu_t(id)`; the right side is `n^{-n/p}`. At `p<q_n`, already `1/n!>n^{-n/p}`. At `p=q_n`, they are equal for `t=0` and any `t>0` makes the left side strictly larger, while TV tends to zero.

For `q_n<p<=2`, the indicator witness fails exactly when

```math
t>t_*(p):=
\frac{n^{-n/p}-1/n!}{1/n-1/n!}. \tag{11}
```

Here `0<t_*(p)<1`: the first inequality uses `p>q_n`, and the second follows from `p<=2` and `n^{-n/2}<1/n` for `n>=3`. Taking `t downarrow t_*(p)` in (10) proves

```math
R_n(p)\le \left(1-\frac n{n!}\right)t_*(p)
=n\left(n^{-n/p}-\frac1{n!}\right).
```

Finally, as `p downarrow q_n`,

```math
n\left(n^{-n/p}-\frac1{n!}\right)
=\frac{n^2\log n}{n!\,q_n^2}(p-q_n)+O_n((p-q_n)^2).
```

The explicit lower bound in (2) is also linear with strictly positive coefficient, which completes Theorem 1. QED.

## 5. Proof of Theorem 2

Induct on `b`. The case `b=1` is Theorem 1. Conditional on the first `b-1` permutations, apply (1) to the final permutation and the functions `j -> F_i(x,j)`. This replaces each such function by

```math
G_i(x)=\left(\frac1n\sum_{j=1}^n F_i(x,j)^p\right)^{1/p}
\quad(x\in[n]^{b-1}).
```

Apply the induction hypothesis to the `G_i`. Since

```math
n^{-(b-1)}\sum_xG_i(x)^p=n^{-b}\sum_{(x,j)\in[n]^b}F_i(x,j)^p,
```

the resulting inequality is (3). Independence is the only relation assumed among the permutation laws. QED.

## 6. Four-row interpretation and exact examples

For `n=4`, `p=7/4` satisfies `p>q_4` because `24^7>4^{16}` (an exact integer inequality). Thus (1) and (3) hold with a **specified** `p=7/4` and the explicit positive tolerance `r_4(7/4)`. In the notation of the four-row shuffle recursion, the resulting moment exponent is

```math
\theta=1-1/p=3/7<1/2.
```

The theorem also permits every real `p in (q_4,2)`, so `theta` can approach `1-1/q_4` from above. It does **not**, by itself, improve the final shuffle mixing time constant: further representation-theoretic bookkeeping would be needed to optimize that constant.

Other exact admissibility tests include `(n,p)=(3,15/8),(6,5/3),(12,3/2)`; for `p=a/b` in lowest terms the certificate is the integer inequality `(n!)^a>n^(nb)`. A checker in `code/check_examples.py` verifies these comparisons and exact cyclic-mixture counterexamples. This finite program is **illustrative only**: equations (4)--(11), not sample computations, establish the all-`n` theorem.

## 7. Scope, limitations, provenance

- The proof depends on the **published** Bristiel--Caputo sharp permanent inequality (BC), not on a numerical optimizer or a Lean kernel. The quantitative margin and the TV estimate are proved explicitly above; all real parameters are covered analytically.
- At the critical exponent `q_n`, arbitrarily small perturbations can invalidate the inequality. This is a sharp topological obstruction, not merely a weakness of the stated constant.
- The constants `r_n(p)` are intentionally conservative; their exact best numerical values are **not** claimed. Only their linear order in `p-q_n` for fixed `n` is proved sharp.
- No bound uniform in growing `n` is claimed. Tensorization concerns a fixed `n` and any finite number of independent columns.
- No claim of worldwide novelty, priority, external peer review, or full formal verification is made. The mathematical ancestry is Bristiel--Caputo (2024) for (BC) and OpenAI (2026) for the motivating four-row perturbation problem.

### Sources

1. A. Bristiel and P. Caputo (2024), *Entropy inequalities for random walks and permutations*, Ann. Inst. Henri Poincare Probab. Stat. 60(1), 54--81. DOI: https://doi.org/10.1214/22-AIHP1267. Corollary 1.14.
2. OpenAI (September 26, 2026), *A strict four-row permanent inequality and permutation moments*, https://github.com/openai/math/blob/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/02-permanent.tex . Theorem 1 and Section 2.


## 8. Further result: the exact local single-atom TV modulus

The cyclic-mixture obstruction above is simple but not the strongest possible atom concentration. The following exact refinement is useful independently of the permanent inequality.

**Proposition (sharp atom concentration).** For `n >= 3`, put `beta_n=(n-2)/n` and `c_n=binom(n,2)/n!`. If `nu` is any probability measure on `S_n` with uniform one-point marginals, then for every `sigma in S_n`,

```math
\left|\nu(\sigma)-\frac1{n!}\right|
\le \beta_n\,\|\nu-u\|_{TV}. \tag{12}
```

This coefficient is optimal, and for **every** `0 <= delta <= c_n` there is a uniform-one-point-marginal measure `nu_delta` with TV distance exactly `delta` from `u` and

```math
\nu_\delta(\sigma)=\frac1{n!}+\beta_n\delta. \tag{13}
```

**Proof.** Relabel outputs so `sigma=id`. Let `v=nu-u=v_+-v_-` be the signed Jordan decomposition, where the positive and negative parts each have total mass `delta=TV(nu,u)`. Let `F(pi)=|{i:pi(i)=i}|` count fixed points. Marginal preservation implies `sum_pi v(pi)F(pi)=0`. Crucially, `F(id)=n` while `F(pi)<=n-2` for every nonidentity permutation: a nonidentity bijection cannot move just one point.

If `v(id)>0`, the positive part contributes at least `n v(id)` to the nonnegative fixed-point sum, whereas the negative part is supported away from `id` and contributes at most `(n-2)delta`. Since the two sums agree, `n v(id)<=(n-2)delta`. If `v(id)<0`, exchange positive and negative parts. This proves (12).

To prove sharpness, let `D` be uniform measure on the **derangements** (permutations with no fixed points), and `T` uniform measure on the `binom(n,2)` transpositions. Define

```math
P=\left(1-\frac2n\right)\delta_{id}+\frac2n D,
\qquad Q=T. \tag{14}
```

Both have the same one-point marginals: for every `i`, the diagonal probability is `1-2/n`, and each off-diagonal probability equals `2/[n(n-1)]`. For `D`, the latter follows by symmetry under conjugations fixing `i`; for `T`, exactly one transposition maps `i` to each `j != i`. The measures `P,Q` have disjoint supports. Hence

```math
\nu_\delta=u+\delta(P-Q)
```

is a probability distribution with uniform one-point marginals whenever `delta <= binom(n,2)/n!`: only the transposition masses decrease, each by `delta/binom(n,2)`, so all masses remain nonnegative. Disjointness gives `TV(nu_delta,u)=delta`, while `P(id)=1-2/n` and `Q(id)=0`, proving (13). Left-translate this construction to any `sigma`. QED.

**Sharper upper bound near the critical exponent.** Write `Delta_n(p)=n^{-n/p}-1/n!`. If `q_n<p<=2` and

```math
\frac{\Delta_n(p)}{\beta_n}<\frac{\binom n2}{n!}, \tag{15}
```

then the identity-indicator test applied to (13), taking `delta` just larger than `Delta_n(p)/beta_n`, gives

```math
R_n(p)\le\frac{\Delta_n(p)}{\beta_n}
=\frac{n}{n-2}\left(n^{-n/p}-\frac1{n!}\right). \tag{16}
```

Condition (15) holds automatically for all `p>q_n` sufficiently close to `q_n` (with `n` fixed). Compared with the global cyclic upper bound in (2), (16) improves the coefficient by a factor `n-2`. In particular, the linear critical-window estimate is refined to

```math
\frac1{4n^4B_n}
\le \liminf_{p\downarrow q_n}\frac{R_n(p)}{p-q_n}
\le \limsup_{p\downarrow q_n}\frac{R_n(p)}{p-q_n}
\le \frac{n^2\log n}{(n-2)n!\,q_n^2}. \tag{17}
```

The exact value of the limiting critical-window coefficient, and whether it is always controlled solely by the permutation-singleton test, are **not** claimed. This stronger upper bound is a purely combinatorial result: it does not require Bristiel--Caputo or any numerical computation.
