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


## 9. A complete sharp radius at three rows and exponent two

The all-arity estimate of Theorem 1 supplies a positive explicit radius but does not generally determine its exact value. For three rows, the endpoint `p=2` admits a complete exact solution.

**Theorem 4 (exact three-row robustness radius).** Let `u` be uniform on `S_3`. For a probability law `nu` with all one-point marginals uniform, the inequality

```math
\mathbb E_{\pi\sim\nu}\prod_{i=1}^3 f_i(\pi(i))
\leq\prod_{i=1}^3
\left(\frac13\sum_{j=1}^3 f_i(j)^2\right)^{1/2}
\quad(f_1,f_2,f_3\ge0) \tag{18}
```

holds **if and only if**

```math
\|\nu-u\|_{TV}\le \frac1{\sqrt3}-\frac12. \tag{19}
```

The endpoint is **included**, and consequently

```math
R_3(2)=\frac1{\sqrt3}-\frac12.
```

The matrix inequality below is a separate sharp `3\times3` permanent--determinant inequality and does not use the Bristiel--Caputo input.

### 9.1. Uniform one-point marginals parameterize the whole family

Every law with uniform one-point marginals on `S_3` is of the form

```math
\nu_t(\pi)=\frac16+t\,\operatorname{sgn}(\pi),
\qquad -\frac16\le t\le\frac16. \tag{20}
```

Indeed, for each `i,j` there are exactly two permutations with `pi(i)=j`, one even and the other odd. The marginal equation says their masses sum to `1/3`. Every even--odd pair of permutations on three letters agrees at exactly one location, so these equations apply to every such pair. All even permutations therefore have the same mass, and all odd permutations have the same mass, establishing (20). Conversely (20) has uniform marginals. Since three permutations have each parity,

```math
\|\nu_t-u\|_{TV}=3|t|. \tag{21}
```

For a `3\times3` matrix `A` with rows `f_1,f_2,f_3`,

```math
6\,\mathbb E_{\nu_t}\prod_i f_i(\pi(i))
=\operatorname{perm}(A)+6t\det(A). \tag{22}
```

### 9.2. Sharp permanent--determinant inequality

**Lemma 5 (an exact trilinear inequality).** Put

```math
\beta=\frac2{\sqrt3},\qquad
\lambda=\beta-1.
```

For every real `3\times3` matrix `A` with row vectors `a,b,c\in\mathbb R^3`,

```math
\operatorname{perm}(A)+\lambda|\det(A)|
\le \beta\,\|a\|_2\|b\|_2\|c\|_2. \tag{23}
```

The constant is sharp both for the identity matrix and for the all-ones matrix.

**Proof.** Swapping two columns preserves the permanent and row norms, while changing the determinant sign. Thus it suffices to prove the bound with `+lambda det(A)`. Expanding along the last row, the resulting trilinear form is `c^T M(a)b`, where, writing `a=(a_1,a_2,a_3)`,

```math
M(a)=
\begin{pmatrix}
0&(2-\beta)a_3&\beta a_2\\
\beta a_3&0&(2-\beta)a_1\\
(2-\beta)a_2&\beta a_1&0
\end{pmatrix}. \tag{24}
```

It therefore suffices to establish `\|M(a)\|_{2\to2}\le\beta\|a\|_2`, for all real `a`. Define

```math
k=2\sqrt3-3>0,\qquad h=\sqrt3-1>0
```

and

```math
H(a)=\frac34\Big(\beta^2\|a\|_2^2 I_3-M(a)^TM(a)\Big).
```

A direct multiplication gives

```math
H(a)=\begin{pmatrix}
a_1^2+k a_2^2 & -h a_1a_2 & -h a_1a_3\\
-h a_1a_2 & a_2^2+k a_3^2 & -h a_2a_3\\
-h a_1a_3 & -h a_2a_3 & a_3^2+k a_1^2
\end{pmatrix}. \tag{25}
```

All its diagonal entries are nonnegative. The principal `2\times2` minor on indices `1,2` is, exactly,

```math
\det H_{\{1,2\}}=
k\big(a_1^2a_2^2+a_1^2a_3^2+a_2^4+
k a_2^2a_3^2\big)\ge0. \tag{26}
```

The other two principal minors are obtained by cyclic permutation of `a_1,a_2,a_3`, hence are also nonnegative. Finally, direct expansion and factorization gives

```math
\begin{aligned}
\det H(a)&=k^2\,\Big(
\sum_{i\ne j}a_i^4a_j^2-
6a_1^2a_2^2a_3^2\Big)\\
&=k^2\Big[
(X+Y+Z)(XY+YZ+ZX)-9XYZ
\Big]\ge0, \tag{27}
\end{aligned}
```

where `X=a_1^2,Y=a_2^2,Z=a_3^2`. The last inequality follows from two instances of AM--GM:
`X+Y+Z>=3(XYZ)^(1/3)` and `XY+YZ+ZX>=3(XYZ)^(2/3)` (and is immediate when any variable is zero).

Thus **all principal minors of the real symmetric matrix `H(a)` are nonnegative**. The principal-minor criterion gives `H(a)\succeq0`, equivalently `M(a)^TM(a)\preceq\beta^2\|a\|_2^2 I`. By Cauchy--Schwarz in the last row, (23) follows.

The identity matrix gives `perm(A)=det(A)=1` and `1+lambda=beta`; the all-ones matrix gives `perm(A)=6`, `det(A)=0`, and `beta (sqrt3)^3=6`. Both are equality cases. QED.

### 9.3. Endpoint radius and its necessity

Suppose `3|t|<=1/sqrt3-1/2`. Then `|6t|<=lambda`. By (22), Lemma 5, and convexity in the coefficient of `det A`,

```math
6\,\mathbb E_{\nu_t}\prod_i f_i(\pi(i))
\le \beta\prod_i\|f_i\|_{\ell^2}
=\frac2{\sqrt3}\prod_i\|f_i\|_{\ell^2}.
```

Dividing by six and using `\beta/6=3^{-3/2}` yields (18), including the endpoint.

Conversely, if `3|t|>1/sqrt3-1/2`, choose the indicator rows `f_i=1_{\{i\}}` for `t>0`; their product is supported only on the identity and (18) requires

```math
\frac16+t\le 3^{-3/2},
```

which is false. For `t<0`, choose indicator rows realizing any odd permutation instead; its mass is `1/6+|t|` and gives the same contradiction. This proves both implications of Theorem 4 and the exact value of `R_3(2)`. QED.

The identities (24)--(27) are elementary equalities in the real quadratic field `Q(sqrt3)`. An independent symbolic replay of these displayed identities is provided in `code/check_s3_exact.py`. The proof is the positive-semidefiniteness argument above; no numerical optimization is invoked. This endpoint solution does **not** assert a formula for `R_3(p)` when `q_3<p<2`.


## 10. Equality classification and the quadratic saturation barrier

The exact `S_3,p=2` result has a sharp equality classification. Moreover, exponent two is a genuine transition for the singleton obstruction: when `p>2`, an atom that saturates the necessary singleton bound is unstable under a two-row perturbation.

**Theorem 6 (all equality cases at the sharp three-row radius).** Retain the notation `nu_t` of (20), and let `t_2=1/(3 sqrt(3))-1/6`. If `|t|<=t_2`, equality in (18) with nonnegative functions `f_1,f_2,f_3` holds precisely in these cases:

1. At least one row is identically zero.
2. Every row is a nonzero constant function.
3. `|t|=t_2`, and all three rows are positive multiples of singleton indicators supported at distinct columns, corresponding to an **even** permutation when `t=t_2` and an **odd** permutation when `t=-t_2`.

There are no other nonzero equality cases. In particular, for `|t|<t_2` every nontrivial equality case is constant.

**Proof.** Work first with `t=t_2` and nonzero rows. The positive-semidefinite proof of Lemma 5 shows that equality requires `b` to belong to the kernel of `H(a)`, and `c` to be a positive multiple of `M(a)b`. In terms of `X=a_1^2,Y=a_2^2,Z=a_3^2`, (27) gives

```math
0=\det H(a)/k^2=(X+Y+Z)(XY+YZ+ZX)-9XYZ. \tag{28}
```

If `XYZ>0`, equality in both AM--GM inequalities forces `X=Y=Z`, hence (because the row is nonnegative) `a_1=a_2=a_3>0`. Here `H(a)` is a positive multiple of the Laplacian of the triangle graph; its kernel is spanned by `(1,1,1)`. Thus `b` is constant, and `M(a)b` is also constant; `c` is constant.

If `XYZ=0`, equation (28) requires `XY+YZ+ZX=0`, so exactly one component of the nonzero row `a` is positive. For example, if `a=(A,0,0)`, (25) becomes `H(a)=\mathrm{diag}(A^2,0,kA^2)`, so `b` is supported in the second coordinate. Equation (24) then forces `c` to be supported in the third coordinate. The cyclic variants give exactly the three even-permutation singleton configurations. They are genuine equality cases by (22)--(23).

For `t=-t_2`, swapping two columns changes the determinant sign without altering any row norm, and converts the even configurations into the odd ones. For `|t|<t_2`, the comparison

```math
\operatorname{perm}(A)+6t\det(A)
\le\operatorname{perm}(A)+6|t|\,|\det(A)|
\le\operatorname{perm}(A)+6t_2|\det(A)|
\le\frac2{\sqrt3}\prod_i\|f_i\|_{\ell^2}
```

is strict when `det(A) != 0`. Of the endpoint equality cases just classified, only the constant configurations have zero determinant. A zero row makes both sides of (18) zero. This completes the classification. QED.

**Theorem 7 (general quadratic saturation obstruction).** Let `n>=2`, `p>2`, and let `nu` be **any** probability law on `S_n` (no marginal condition is needed). Suppose `sigma,tau\in S_n` differ by transposing the images of precisely two rows and that

```math
\nu(\sigma)=n^{-n/p},\qquad \nu(\tau)>0. \tag{29}
```

Then the normalized `L^p` permanent inequality **fails** for some nonnegative rows.

**Proof.** Relabel the columns so `sigma=id`, and suppose `tau` swaps rows 1 and 2. Set

```math
f_1=(1,\varepsilon,0,\ldots,0),\quad
f_2=(\varepsilon,1,0,\ldots,0),\quad
f_i=\mathbf 1_{\{i\}}\ (3\le i\le n).
```

Only `sigma` and `tau` contribute. Their products are `1` and `epsilon^2`; the right side equals `n^{-n/p}(1+epsilon^p)^{2/p}`. At (29), the desired inequality would require

```math
\nu(\tau)\varepsilon^2
\le n^{-n/p}\big((1+\varepsilon^p)^{2/p}-1\big)
\le (2/p)n^{-n/p}\varepsilon^p.
```

The last step uses concavity of `x^(2/p)` for `p>2`. The inequality is impossible for all sufficiently small `epsilon>0`, since `p-2>0`. QED.

**Corollary 8 (a strict upper bound for `S_3` when `2<p<3`).** Write

```math
c_p=3^{-3/p},\quad t_p=c_p-\frac16,\quad
b_p=\frac13-c_p,\quad
e_p=\min\left\{\frac12,
 \left(\frac{p b_p}{4c_p}\right)^{1/(p-2)}\right\}. \tag{30}
```

Then `t_p>0`, `b_p>0`, `0<e_p<=1/2`, and

```math
\begin{aligned}
3t_2\ \le\ R_3(p)
&\le 3\,\frac{
 c_p(1+e_p^p)^{2/p}-(1+e_p^2)/6
}{1-e_p^2}\\
&\le 3\left(t_p-\frac{b_pe_p^2}{2(1-e_p^2)}\right)
\ <\ 3t_p. \tag{31}
\end{aligned}
```

Thus the singleton upper bound `R_3(p)<=3(3^{-3/p}-1/6)`, which is **attained at `p=2`**, becomes **strictly non-sharp at every `2<p<3`**.

**Proof.** Every law with uniform one-point marginals on `S_3` is `nu_t), and its TV distance is `3|t|`. Increasing `p` enlarges normalized `L^p` norms, so Theorem 4 implies `R_3(p)>=3t_2`. In the two-row test of Theorem 7, for `nu_t` the left side equals `(1/6+t)+(1/6-t)e^2` and the right side equals `c_p(1+e^p)^{2/p}`. For fixed `0<e<1`, the inequality therefore forces

```math
t\le U_p(e):=\frac{c_p(1+e^p)^{2/p}-(1+e^2)/6}{1-e^2}. \tag{32}
```

Consequently `R_3(p)<=3U_p(e)`: every slightly larger admissible `t` gives a concrete violation. Subtracting `t_p` yields

```math
U_p(e)-t_p
=\frac{c_p((1+e^p)^{2/p}-1)-b_pe^2}{1-e^2}
\le\frac{(2c_p/p)e^p-b_pe^2}{1-e^2}. \tag{33}
```

The definition of `e_p` gives `(2c_p/p)e_p^{p-2}<=b_p/2`, proving (31). The threshold values are valid probability laws because `0<t_p<1/6` for `2<p<3`. QED.

**Exact rational counterexample to singleton sufficiency.** Take `p=5/2`, `t=1009/10000`, and `e=1/16`. The law `nu_t` has uniform one-point marginals and `TV(nu_t,u)=3027/10000`. Its even singleton masses are `a=8027/30000`. The singleton test is **satisfied** because

```math
\left(\frac{8027}{30000}\right)^5<\frac1{729}
=c_p^5. \tag{34}
```

Nevertheless the two-row perturbation violates the `L^{5/2}` permanent inequality, as certified by the strict **integer-rational** comparison

```math
\left(\frac{411377}{1536000}\right)^5
>\frac1{729}\left(\frac{1025}{1024}\right)^4. \tag{35}
```

Indeed the left base is `a+(1/6-t)/256`, while the right is the fifth power of the normalized row-norm product. Both strict signs are checked using fractions only by `code/check_s3_phase.py`.

## 11. An exact six-variable entropy criterion for the remaining exponent problem

The unresolved interval `q_3<p<2` can be translated, without approximation, into a finite-dimensional entropy inequality with a complete bipartite sum. This exact reduction identifies the role of mixed-parity distributions and limits the number of distinct coordinates at interior stationary obstructions.

**Theorem 9 (entropy duality and the `K_{3,3}` reduction).** Fix `|t|<1/6`, let `a=1/6+t`, `b=1/6-t`, and let `p>=1`. The three-row normalized `L^p` permanent inequality for `nu_t` holds for **all** nonnegative row functions if and only if, for **every** six nonnegative numbers `e_1,e_2,e_3,o_1,o_2,o_3` with total sum one,

```math
3\log3+\sum_{i=1}^3\sum_{j=1}^3
 (e_i+o_j)\log(e_i+o_j)
\le
p\left[
\sum_i e_i\log\frac{e_i}{a}
+\sum_j o_j\log\frac{o_j}{b}
\right]. \tag{36}
```

Here `0 log 0=0`. Equivalently, the critical row exponent is the **exact** finite variational quantity

```math
p_*(t)=
\sup_{\substack{e_i,o_j\ge0,\ \sum_i e_i+\sum_j o_j=1\\
 (e,o)\ne(a,a,a,b,b,b)}}
\frac{3\log3+\sum_{i,j}(e_i+o_j)\log(e_i+o_j)}
{\sum_i e_i\log(e_i/a)+\sum_j o_j\log(o_j/b)}. \tag{37}
```

The quotient is evaluated only where its denominator is positive.

**Proof.** For any full-support probability law `nu` on a finite space `Omega` and maps `X_i:Omega->[n]`, the usual finite Gibbs variational formula says

```math
\log\mathbb E_\nu\exp\Big(\sum_i g_i(X_i)\Big)
=\sup_\mu\Big(\sum_i\mathbb E_{\mu_i}g_i
 -D(\mu\|\nu)\Big).
```

Consequently the normalized product-norm inequality

```math
\mathbb E_\nu\exp\big(\sum_i g_i(X_i)\big)
\le\prod_i\big(\mathbb E_u e^{pg_i}\big)^{1/p}
```

for all real `g_i` is equivalent to entropy subadditivity

```math
\sum_iD(\mu_i\|u)\le pD(\mu\|\nu)
\quad\text{for every probability }\mu. \tag{38}
```

For clarity, in one direction insert (38) into the Gibbs formula, then apply the scalar variational formula separately to each marginal. In the reverse direction, the full relative entropy bounds the restricted Gibbs supremum:
`D(mu||nu)>=sum_i E_mu_i g_i-log E_nu exp(sum g_i)`.
Apply the product-norm inequality and take the supremum over all `g_i`; the independent scalar suprema give `(1/p)sum_i D(mu_i||u)`. Zero-valued functions follow by nonnegative approximation.

Enumerate the three even permutations of `S_3` with masses `e_i` under `mu`, and the three odd permutations with masses `o_j`. Any even and any odd permutation agree at **exactly one** row, because their relative permutation is a transposition. Hence, across the three single-coordinate marginals, the nine probabilities `e_i+o_j` each appear exactly once. Therefore

```math
\sum_{r=1}^3D(\mu_r\|u_3)
=3\log3+\sum_{i,j}(e_i+o_j)\log(e_i+o_j).
```

Since `nu_t` assigns mass `a` to each even permutation and `b` to each odd one, `D(mu||nu_t)` is exactly the right bracket of (36). Formula (38) proves (36), and taking the supremum of the quotient proves (37). QED.

**Proposition 10 (parity-pure obstructions are precisely singleton obstructions).** Suppose `1<=p<3` and `|t|<1/6`. Inequality (36) holds for every probability measure supported entirely on the **even** permutations if and only if `a<=3^{-3/p}`. It holds for every measure supported entirely on the **odd** permutations if and only if `b<=3^{-3/p}`.

**Proof.** If `mu` is supported on even permutations, let `z=(e_1,e_2,e_3)` be its probability vector and put `d=D(z||u_3)\in[0,\log3]`. Each coordinate marginal is a permutation of `z`, giving `sum_r D(mu_r||u_3)=3d`, while

```math
D(\mu\|\nu_t)=d+\log\frac1{3a}.
```

For `p<3`, the inequality `3d<=p(d+log(1/(3a)))` for **all** `d\in[0,log3]` is equivalent to its endpoint `d=log3`, which rearranges to `a<=3^{-3/p}`. The odd case is identical with `b`. QED.

**Proposition 11 (two positive levels per parity at interior stationary points).** Fix `0<p<3` and `|t|<1/6`. At every interior stationary point of the difference between the left and right sides of (36), subject to the total-mass constraint, the triple `(e_1,e_2,e_3)` has at most **two distinct values**, and likewise `(o_1,o_2,o_3)`.

**Proof.** With `o_j>0` fixed, the stationarity equations for the `e_i`, after cancellation of constants, have the form

```math
\phi(e_i)=C,\qquad
\phi(x)=\sum_{j=1}^3\log(x+o_j)-p\log x.
```

For `x>0`,

```math
x\phi'(x)=\sum_{j=1}^3\frac{x}{x+o_j}-p.
```

The right side increases strictly from `-p` to `3-p`. Thus `phi` first strictly decreases and then strictly increases: each horizontal level has at most two positive preimages. The same argument interchanges the `e` and `o` roles. QED.

**Research boundary.** Theorem 9 is an **exact reformulation**, not a closed-form solution for `p_*(t)`. Proposition 11 applies only to strictly positive stationary points; boundary extrema must still be checked. The conjecture that the singleton threshold is sufficient throughout `q_3<p<2` is supported by numerical discovery but **not established** by the results in this section. Section 10 rigorously disproves its extension to `2<p<3`.


## 12. Exact critical radius on an entire interval below two

The endpoint classification in Theorem 6 also settles an **open interval of exponents** rather than an isolated endpoint. The argument below is entirely analytic: no numerical optimization, discretization, or computer-assisted compactness search is used.

**Theorem 12 (one-sided exact-radius interval).** There exists `p_0\in(q_3,2)` such that for every `p_0\le p\le2`, the exact uniform-marginal total-variation robustness radius on `S_3` is

```math
\boxed{R_3(p)=3\left(3^{-3/p}-\frac16\right).} \tag{39}
```

Equivalently, throughout this interval the three-row normalized `L^p` permanent inequality holds for **every** uniform-one-point-marginal law `nu_t` exactly when

```math
|t|\le3^{-3/p}-\frac16. \tag{40}
```

The constant `p_0` is **existential**: this proof does not produce a numerical lower endpoint. Together with Corollary 8, the theorem shows that singleton saturation is exact throughout some interval immediately **below** exponent two, but is strictly **non-sharp above** two.

**Proof.** Put `q=q_3`, `c_p=3^{-3/p}`, `t_p=c_p-1/6`, and `b_p=1/3-c_p`. For `q\le p\le2`, one has

```math
\frac16\le c_p\le\frac1{3\sqrt3},\qquad
0\le t_p\le t_2,\qquad
b_p>0. \tag{41}
```

It suffices to prove the inequality at `nu_{t_p}`, since exchanging two columns handles `nu_{-t_p}`, interpolation handles every intermediate `t`, and singleton indicators force the converse `|t|\le t_p`.

We establish a **uniform strict local inequality** near the two types of endpoint extremizers of Theorem 6, valid for *every* `p\in[q,2]`. We then apply compactness **only to the complement**, where the exact `p=2` theorem already has a strict gap.

**(a) Neighborhood of the constant triple.** By row homogeneity, write all rows sufficiently close to constants as `f_i=1+g_i`, with `\mathbb E_{j\in[3]}g_i(j)=0` and `\|g_i\|_\infty\le h`. Put `V_i=\mathbb E_jg_i(j)^2` and `V=\sum_iV_i`. For uniform `u`, sampling without replacement gives

```math
\sum_{i<j}\mathbb E_u g_i(\pi(i))g_j(\pi(j))
=\frac14\left(V-\Big\|\sum_i g_i\Big\|_2^2\right)
\le\frac V4.
```

The cubic term in the uniform product expansion is bounded in absolute value by `hV/2`. From `P_{\nu_t}(A)=P_u(A)+t\det(A)` and the expansion of the determinant in the row perturbations,

```math
\det(1+g_1,1+g_2,1+g_3)
=\sum_{i<j}\det(\ldots,1,\ldots,g_i,\ldots,g_j,\ldots)
+\det(g_1,g_2,g_3),
```

where the first sum means precisely the three determinants obtained by taking two `g` rows and the all-ones row. Hadamard's determinant bound gives

```math
\left|\sum_{i<j}\det(\ldots,1,\ldots,g_i,\ldots,g_j,\ldots)\right|
\le3\sqrt3\,V,
\qquad
|\det(g_1,g_2,g_3)|\le \frac{3\sqrt3}{2}hV.
```

(The normalized variance satisfies `\|g_i\|_{\ell^2}=\sqrt{3V_i}`, and `\sqrt{V_iV_j}\le(V_i+V_j)/2`.) Since `0\le t_p\le t_2`, there is an absolute constant `C` such that

```math
P_{\nu_{t_p}}(1+g_1,1+g_2,1+g_3)
\le 1+\left(\frac14+3\sqrt3\,t_2+Ch\right)V. \tag{42}
```

Uniform Taylor expansion of the normalized `L^p` norms for `p\in[q,2]` and `h\le1/2` yields

```math
\prod_i\|1+g_i\|_p
\ge1+\left(\frac{p-1}{2}-Ch\right)V. \tag{43}
```

Here `C` may be enlarged and is independent of `p`, because the derivatives of `x^p` are uniformly bounded on `[1/2,3/2]\times[q,2]`. A strict uniform gap exists: the exact integer comparison `3^{15}>6^9` gives `q>9/5`, hence `(p-1)/2>2/5`; while

```math
\frac14+3\sqrt3\,t_2
=\frac54-\frac{\sqrt3}{2}
<\frac25,
```

since `\sqrt3>17/10`. Choose `h>0` sufficiently small to absorb both `Ch` terms. Equations (42)--(43) prove the required uniform local inequality, with equality only when `V=0`, i.e. at the constant triple.

**(b) Neighborhood of each even-permutation singleton triple.** By permutation symmetry and row scaling, take the dominant entries to be `f_i(i)=1` and denote the six off-diagonal entries by `z_{ij}\in[0,h]` for `i\ne j`, where `0<h<1`. Define

```math
s_i=\sum_{j\ne i}z_{ij}^{p},\qquad
S=\sum_i s_i\le6h^q.
```

The three even-permutation monomials consist of the identity contribution `1` and two 3-cycle monomials; the three odd-permutation monomials consist of three transposition products. By `xy\le(x^2+y^2)/2`, `z_{ij}^2\le z_{ij}^p` for `p\le2`, and the bound `z_{ij}\le h`,

```math
\sum_{\substack{\pi\text{ even}\\\pi\ne id}}
 \prod_i f_i(\pi(i))\le\frac h2 S,
\qquad
\sum_{\pi\text{ odd}}\prod_i f_i(\pi(i))\le\frac12 S.
```

Therefore

```math
P_{\nu_{t_p}}(A)\le c_p\left(1+\frac h2 S\right)+\frac{b_p}{2}S. \tag{44}
```

For the normalized row norm product, the elementary inequality `\prod_i(1+s_i)\ge1+S` and Taylor's theorem for `0<1/p<1` imply

```math
\begin{aligned}
\prod_i\|f_i\|_p
&=c_p\prod_i(1+s_i)^{1/p}
\ge c_p(1+S)^{1/p}\\
&\ge c_p\left(1+\frac S p-\frac{S^2}{8}\right). \tag{45}
\end{aligned}
```

The last estimate holds for every `S\ge0` because the second derivative of `x^{1/p}` on `[1,\infty)` is at least `-1/4`. Crucially, the coefficient

```math
d_p:=\frac{c_p}{p}-\frac{b_p}{2}
=\frac12\left[c_p\left(1+\frac2p\right)-\frac13\right]
```

is **strictly positive** for every `p\in[q,2]`: indeed `c_p\ge1/6` and `1+2/p\ge2`, and the two equalities cannot hold simultaneously because `q<2`. By compactness of this scalar parameter interval, `d=\min_{p\in[q,2]}d_p>0`. Choose `h>0` so small that

```math
\frac{c_2h}{2}+\frac{6c_2h^q}{8}<d.
```

Equations (44)--(45) then give the **strict** lower deficit

```math
\prod_i\|f_i\|_p-P_{\nu_{t_p}}(A)
\ge S\left(d_p-\frac{c_ph}{2}-\frac{c_pS}{8}\right)>0
\quad\text{if }S>0. \tag{46}
```

The same neighborhood argument applies to the other two even-permutation singleton triples by relabeling rows and columns.

**(c) Global completion by a strict compact complement.** Normalize each nonzero row by its normalized `L^2` norm and set

```math
\mathcal K=\{A\in[0,\infty)^{3\times3}:
\|f_i\|_2=1\text{ for }i=1,2,3\}.
```

This is compact. The ratio

```math
\mathcal F(p,A)
=\frac{P_{\nu_{t_p}}(A)}{\prod_i\|f_i\|_p}
```

is jointly continuous on `[q,2]\times\mathcal K`. At `p=2`, Theorems 4 and 6 give `\mathcal F(2,A)\le1`, with equality **only** at the constant triple and the three even-permutation singleton triples. Parts (a)--(b) yield a fixed relatively open neighborhood `U\subset\mathcal K` of these four normalized configurations on which `\mathcal F(p,A)\le1` **for every** `p\in[q,2]`.

On the compact complement `\mathcal K\setminus U`, the function `\mathcal F(2,\cdot)` has maximum strictly less than one. Joint continuity consequently supplies `\delta>0` such that `\mathcal F(p,A)<1` on that complement whenever `2-\delta\le p\le2`. Reduce `\delta` if necessary to ensure `2-\delta>q`. Combining the complement with `U`, we obtain the endpoint law inequality for every `p\in[2-\delta,2]` and every `A\in\mathcal K`, and hence (by homogeneity) for all nonnegative row functions, including zero rows.

Finally, an odd column permutation converts `nu_{t_p}` into `nu_{-t_p}`. Every `nu_t` with `|t|\le t_p` is a convex combination of these two endpoint laws. The indicator test gives failure whenever `|t|>t_p` (for an even or odd permutation according to sign), proving (39)--(40). Set `p_0=2-\delta`. QED.

**Remark.** The positive gaps in (42)--(46) are explicit up to harmless uniform Taylor constants. The **remaining compact complement** is handled qualitatively, so Theorem 12 is a genuine infinite-interval theorem but does not certify a specified rational value of `p_0`. A rational endpoint requires a separate effective bound or a replayable interval certificate; plotting a numerical optimizer is not sufficient.

## 13. Exact infinitesimal entropy obstruction

The entropy reformulation gives an independent, *sharp at quadratic order*, necessary condition for every full-support `nu_t`.

**Proposition 13 (local entropy threshold).** Let `|t|<1/6`, `a=1/6+t`, `b=1/6-t`. If the normalized `L^p` permanent inequality holds for `nu_t`, then necessarily

```math
p\ge9\max(a,b)=\frac32+9|t|
=\frac32+3\|\nu_t-u\|_{TV}. \tag{47}
```

The coefficient on the right is **exactly** the supremum of the ratio of the quadratic terms of the two relative entropies in (38) at `\mu=\nu_t`. This is a statement about the local second variation, **not** sufficiency for the global inequality.

**Proof.** Perturb the six masses in (36) as `e_i=a+x_i`, `o_j=b+y_j`, where `\sum_i x_i+\sum_j y_j=0`, and put `S_x=\sum_i x_i=-\sum_j y_j`. Both sides of (36) have vanishing first variation at this base point. Their second-order terms are

```math
\begin{aligned}
\frac32\sum_{i,j}(x_i+y_j)^2
 &=\frac92\left(\sum_i x_i^2+\sum_j y_j^2\right)-3S_x^2,\\
\frac12\left(\sum_i\frac{x_i^2}{a}
 +\sum_j\frac{y_j^2}{b}\right).
\end{aligned}
```

Write `x_i=x_i^0+S_x/3` and `y_j=y_j^0-S_x/3`, where both centered triples have sum zero. The first quadratic expression reduces exactly to

```math
\frac92\left(\sum_i(x_i^0)^2+\sum_j(y_j^0)^2\right),
```

and the second becomes

```math
\frac12\left[
\frac{\sum_i(x_i^0)^2}{a}
+\frac{\sum_j(y_j^0)^2}{b}
+\frac{S_x^2}{3}\left(\frac1a+\frac1b\right)\right].
```

Their quotient is at most `9\max(a,b)`, with equality for perturbations entirely within the zero-sum coordinates of the heavier parity block (setting `S_x=0`). Any smaller `p` would violate (36) for sufficiently small positive and negative such perturbations. This proves (47) and its stated exact second-variation interpretation. QED.

This gives the separate necessary estimate `R_3(p)\le(p-3/2)/3` for `q_3<p<3`, though the singleton bound is stronger on the known exact interval of Theorem 12.


## 14. Fully rational local stability neighborhoods

The two local neighborhoods used in Theorem 12 admit explicit rational sizes and uniform *rational lower deficits*. Thus only the compact complement remains non-effective.

**Proposition 14 (uniform local certificates).** Put \(q=q_3\), \(c_p=3^{-3/p}\), \(t_p=c_p-1/6\), and let \(q\le p\le 2\).

**(a) Constant neighborhood.** If \(f_i=1+g_i\), every \(g_i\) has uniform mean zero, and \(\max_{i,j}|g_i(j)|\le1/1000\), then with \(V=\sum_i\mathbb E_jg_i(j)^2\),

\[
\prod_i\|f_i\|_p-P_{\nu_{t_p}}(f_1,f_2,f_3)\ \ge\ \frac{V}{100}. \tag{48}
\]

**(b) Even-permutation singleton neighborhood.** If \(f_i(i)=1\) and \(0\le f_i(j)\le1/100\) for \(j\ne i\), then with \(S=\sum_{i\ne j}f_i(j)^p\),

\[
\prod_i\|f_i\|_p-P_{\nu_{t_p}}(f_1,f_2,f_3)\ \ge\ \frac{S}{1200}. \tag{49}
\]

The same bound holds after relabeling around either other even-permutation singleton configuration. Both estimates hold for **all real** \(p\in[q,2]\).

**Proof.** The necessary arithmetic comparisons are

\[
3^{15}>6^9,\qquad 3^{30}<6^{19},\qquad
100^{19}>17^{19}3^{30},\qquad 173^2<3\cdot100^2. \tag{50}
\]

Thus \(9/5<q<19/10\), \(3^{-30/19}>17/100\), and \(\sqrt3>173/100\).

For (a), let \(h=1/1000\). The uniform-permutation cubic term in the expansion at constants has absolute value at most \(hV/2\). Hadamard's inequality bounds the cubic determinant term by \((3\sqrt3/2)hV\). Since \(0\le t_p\le t_2\) and \(3\sqrt3 t_2=1-\sqrt3/2<1\), the total cubic contribution is at most \(hV\). The quadratic estimate of Theorem 12(a) therefore reads

\[
P_{\nu_{t_p}}(f_1,f_2,f_3)
\le 1+\left(\frac54-\frac{\sqrt3}{2}+h\right)V. \tag{51}
\]

Write \(V_i=\mathbb E_jg_i(j)^2\) and \(A_i=\mathbb E_j(1+g_i(j))^p-1\). Taylor's theorem on \([1/2,3/2]\), using \(|p(p-1)(p-2)x^{p-3}|\le8\), gives

\[
\left|A_i-\frac{p(p-1)}2V_i\right|\le2hV_i. \tag{52}
\]

As \(p>9/5\) and \(h\le1/2\), one has \(0\le A_i\le 2V_i\) and \(V_i\le h^2\). For \(\alpha=1/p\in(0,1)\) and \(A\ge0\), Taylor's theorem gives \((1+A)^\alpha\ge1+\alpha A-A^2/8\), since the second derivative on \([1,\infty)\) is at least \(-1/4\). Consequently,

\[
\begin{aligned}
\|1+g_i\|_p
&\ge1+\frac{p-1}{2}V_i-\frac{2h}{p}V_i-\frac{A_i^2}{8}\\
&\ge1+\left(\frac{p-1}{2}-3h\right)V_i.
\end{aligned}
\]

Each norm is at least one by Jensen, so their product is at least \(1+((p-1)/2-3h)V\). Combining with (51) and using \(p>9/5\) and \(\sqrt3>173/100\) yields

\[
\prod_i\|f_i\|_p-P_{\nu_{t_p}}(A)
\ge\left(\frac{\sqrt3}{2}-\frac{17}{20}-4h\right)V
>\left(\frac3{200}-\frac4{1000}\right)V
>\frac V{100}.
\]

For (b), recall from Theorem 12(b) that the deficit is at least \(S(d_p-c_ph/2-c_pS/8)\), where \(d_p=c_p/p-(1/3-c_p)/2\). We first prove the explicit bound \(d_p>1/300\).

If \(q\le p\le19/10\), then \(c_p\ge1/6\), \(1/3-c_p\le1/6\), and \(1/p\ge10/19\). Therefore

\[
d_p\ge\frac16\frac{10}{19}-\frac1{12}=\frac1{228}>\frac1{300}.
\]

If \(19/10\le p\le2\), then \(1/p\ge1/2\), so by (50),

\[
d_p\ge c_p-\frac16
\ge3^{-30/19}-\frac16
>\frac{17}{100}-\frac16=\frac1{300}.
\]

Take \(h=1/100\). Since \(c_p\le c_2=1/(3\sqrt3)<1/5\) and \(q>1\), the off-diagonal \(p\)-power sum satisfies \(S\le6h^q\le6h\), hence

\[
\frac{c_ph}{2}+\frac{c_pS}{8}
\le\frac15\left(\frac1{200}+\frac6{800}\right)
=\frac1{400}.
\]

The deficit is thus at least \(S(1/300-1/400)=S/1200\), proving (49). QED.

The exact integer comparisons (50) are independently replayed by the small checker in code/check_local_gaps.py. **Limit of effectiveness:** although these neighborhoods and margins are explicit, the strict bound on the complement of their union in the normalized matrix compactum is still qualitative. A verified global complement margin would make the interval endpoint \(p_0\) effective.


## 15. A sharp atom-modulus theorem for all doubly transitive groups

The fixed-point argument in Section 8 extends beyond the symmetric groups. The correct invariant is the **minimal degree** of the permutation action, and the sharpness mechanism works for every finite doubly transitive group. This is a separate infinite-family structural statement, independent of the uniform permanent bound and the special three-row analysis.

Let a finite group \(G\le S_\Omega\) act faithfully and doubly transitively on a set \(\Omega\) of \(n\ge3\) points. Write \(u_G\) for its uniform measure and let

\[
m(G)=\min_{g\in G\setminus\{1\}}
\big|\{i\in\Omega:g(i)\ne i\}\big|,
\qquad \beta_G=\frac{n-m(G)}n. \tag{54}
\]

Because the point stabilizer in a doubly transitive action has at least \(n-1\ge2\) elements, some nonidentity element fixes a point; thus \(2\le m(G)\le n-1\) and \(\beta_G>0\).

**Theorem 15 (optimal atom-TV modulus for doubly transitive permutation groups).** Let \(\nu\) be any probability measure on \(G\) with the same one-point marginals as \(u_G\), namely

\[
\nu\{g:g(i)=j\}=\frac1n \qquad(i,j\in\Omega).
\]

Then, for every \(\sigma\in G\),

\[
\boxed{\left|\nu(\sigma)-\frac1{|G|}\right|
\le\beta_G\,\|\nu-u_G\|_{\mathrm{TV}}.} \tag{55}
\]

The coefficient \(\beta_G\) is the **smallest possible universal coefficient**. More precisely, let \(M=\{g\in G:|\operatorname{supp}(g)|=m(G)\}\). For every \(\sigma\in G\) and every

\[
0\le\delta\le \frac{|M|}{|G|}, \tag{56}
\]

there exists a probability measure \(\nu_{\sigma,\delta}\) with uniform one-point marginals for which

\[
\|\nu_{\sigma,\delta}-u_G\|_{\mathrm{TV}}=\delta,\qquad
\nu_{\sigma,\delta}(\sigma)=\frac1{|G|}+\beta_G\delta. \tag{57}
\]

The proof is elementary and makes no assumption of conjugacy-invariance on an arbitrary \(\nu\).

**Proof.** For a fixed \(\sigma\in G\), define the agreement count

\[
F_\sigma(g)=|\{i:g(i)=\sigma(i)\}|=\operatorname{Fix}(\sigma^{-1}g).
\]

This equals \(n\) for \(g=\sigma\), and at most \(n-m(G)\) for every \(g\ne\sigma\). Set \(v=\nu-u_G=v_+-v_-\) with positive and negative parts of equal total mass \(\delta=\|\nu-u_G\|_{\mathrm{TV}}\). Uniform one-point marginals imply

\[
\sum_{g\in G}v(g)F_\sigma(g)
=\sum_{i\in\Omega}
\left(\nu\{g:g(i)=\sigma(i)\}-\frac1n\right)=0.
\]

If \(v(\sigma)>0\), the positive \(F_\sigma\)-weighted mass is at least \(nv(\sigma)\), while the negative contribution is at most \((n-m(G))\delta\), because its support excludes \(\sigma\). This gives \(nv(\sigma)\le(n-m(G))\delta\). If \(v(\sigma)<0\), exchange the positive and negative parts. This proves (55).

For sharpness, let \(D\subseteq G\) be the derangements (elements fixing no point). It is nonempty: Burnside's orbit-counting identity for a transitive action says \(\sum_{g\in G}\operatorname{Fix}(g)=|G|\); if every element fixed a point, the identity with \(n\) fixed points and all other elements with at least one fixed point would make the sum strictly exceed \(|G|\). Define

\[
P=\left(1-\frac{m(G)}n\right)\delta_1+
\frac{m(G)}n\,U_D,\qquad Q=U_M, \tag{58}
\]

where \(U_D,U_M\) are uniform measures on the indicated sets. Both \(D\) and \(M\) are invariant under conjugation in \(G\). Since \(G\) is **doubly transitive**, any conjugacy-invariant probability law has constant probability for all diagonal pairs \(g(i)=i\), and constant probability for all ordered off-diagonal pairs \(g(i)=j\) with \(i\ne j\). Every element of \(M\) fixes exactly \(n-m(G)\) points, so under \(Q\),

\[
Q\{g:g(i)=i\}=1-\frac{m(G)}n,\qquad
Q\{g:g(i)=j\}=\frac{m(G)}{n(n-1)}\quad(i\ne j).
\]

Under \(U_D\), these probabilities are \(0\) and \(1/(n-1)\), respectively. Hence \(P\) has **exactly the same** one-point marginals as \(Q\).

Because \(m(G)<n\), every \(g\in M\) is nonidentity and has a fixed point, while \(P\) is supported on the identity and derangements. Thus \(P,Q\) have disjoint supports. For \(0\le\delta\le |M|/|G|\), define

\[
\nu_\delta=u_G+\delta(P-Q). \tag{59}
\]

It is a nonnegative probability law: at every \(g\in M\), its mass is \(|G|^{-1}-\delta|M|^{-1}\ge0\), and at all other elements no mass is subtracted. Its one-point marginals agree with \(u_G\), since \(P\) and \(Q\) have identical marginals. Disjointness gives \(\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta\), and

\[
\nu_\delta(1)=\frac1{|G|}+
\left(1-\frac{m(G)}n\right)\delta.
\]

Left translation by \(\sigma\) sends the identity atom to \(\sigma\), preserves the uniform law and total variation, and preserves uniform one-point marginals. This establishes (57) and proves sharpness. QED.

**Concrete infinite families.**

* **Symmetric groups.** For \(G=S_n\), \(m(G)=2\); (55) is precisely the optimal constant \((n-2)/n\) proved in Section 8. Here \(M\) is the set of transpositions.
* **Alternating groups.** For \(G=A_n\) in its natural action with \(n\ge4\), double transitivity holds and \(m(G)=3\), attained by three-cycles. The exact optimal constant is \((n-3)/n\). In particular, the constants for \(A_4,A_5,A_6\) are \(1/4,2/5,1/2\). The sharp construction mixes identity/derangements against the three-cycle class.
* **Affine groups.** For \(G=\operatorname{AGL}(1,\mathbb F_q)\), \(q\) any prime power at least three, the natural action is doubly transitive and \(m(G)=q-1\). The exact coefficient is therefore \(1/q\), attained by contrasting nontrivial translations with affine maps having exactly one fixed point.

The finite independent checker code/check_doubly_transitive.py exhaustively verifies the signed-measure construction, one-point marginals, TV values, and optimal atom excess in several small symmetric, alternating and affine examples. The **theorem for all finite doubly transitive groups is proved above** and does not rest on those finite enumerations.

**Publication and novelty scope.** Minimal degree and derangements are classical objects; this paper claims only the stated exact distributional inequality with its displayed proof, not that the minimal-degree invariant or derangement existence is new. No generalization of Bristiel--Caputo's permanent bound to arbitrary group-uniform permutation laws is asserted.


## 16. Exact non-doubly-transitive obstruction: the edge action of \(S_5\)

Double transitivity in Theorem 15 is not merely a convenience for its extremizing construction. In a natural **transitive but not doubly transitive** action, the fixed-point/minimal-degree coefficient is **strictly non-sharp**. Moreover, the true optimal constant can still be determined exactly by a short primal-dual certificate.

Let \(G=S_5\) act on the \(n=10\) edges \(\Omega=\binom{[5]}2\) of the complete graph \(K_5\). This action is transitive but not doubly transitive: ordered pairs of edges fall into the equal, adjacent and disjoint orbitals. A vertex transposition moves six of the ten edges, so \(m(G)=6\), giving the general fixed-point upper coefficient \((10-6)/10=2/5\).

**Theorem 16 (sharp non-doubly-transitive atom modulus).** Let \(u_G\) be uniform on the 120 permutations of \(S_5\), viewed in their action on \(\Omega\). If a law \(\nu\) on \(S_5\) satisfies

\[
\nu\{g:g(E)=F\}=\frac1{10}\qquad(E,F\in\Omega),
\]

then for every \(\sigma\in S_5\),

\[
\boxed{\left|\nu(\sigma)-\frac1{120}\right|
\le\frac13\,\|\nu-u_G\|_{\mathrm{TV}}.} \tag{60}
\]

The coefficient \(1/3\) is optimal. For every \(\sigma\in S_5\) and every \(0\le\delta\le1/12\), there exists such a law with TV distance exactly \(\delta\) and atom excess exactly \(\delta/3\). Consequently, the minimal-degree bound \(2/5\) is **not sharp** for this transitive action.

**Proof (exact dual certificate).** For \(g\in S_5\), let \(F(g)\) be the number of edges \(E\in\Omega\) fixed setwise by \(g\), and let \(A(g)\) be the number of edges \(E\) whose image \(g(E)\) is **adjacent** to \(E\) (shares exactly one vertex).

Both counts depend only on the vertex-cycle type of \(g\). Directly applying a representative of each of the seven cycle types to the ten unordered pairs gives the following complete table. Every row can also be checked using the independent integer enumerator in code/check_edge_action_s5.py.

| Cycle type in \(S_5\) | Number of elements | \(F(g)\) | \(A(g)\) | \(h(g)\) |
| --- | ---: | ---: | ---: | ---: |
| \(1^5\) | 1 | 10 | 0 | \(4/9\) |
| \(2\,1^3\) | 10 | 4 | 6 | \(1/9\) |
| \(2^2\,1\) | 15 | 2 | 4 | \(1/9\) |
| \(3\,1^2\) | 20 | 1 | 9 | \(4/9\) |
| \(3\,2\) | 20 | 1 | 3 | \(1/9\) |
| \(4\,1\) | 30 | 0 | 8 | \(4/9\) |
| \(5\) | 24 | 0 | 5 | \(5/18\) |

Here the certificate function is

\[
h(g)=\mathbf1_{\{g=1\}}-\frac{F(g)-A(g)}{18}. \tag{61}
\]

The table proves, **for all 120 group elements**, the exact pointwise interval

\[
\frac19\le h(g)\le\frac49. \tag{62}
\]

Set \(v=\nu-u_G\). Uniform one-point marginals imply \(\sum_g v(g)F(g)=0\), because \(F(g)\) is a sum of diagonal marginal indicators. They also imply \(\sum_g v(g)A(g)=0\), because \(A(g)\) is a sum of indicators of specified **adjacent** image edges. Hence

\[
\nu(1)-\frac1{120}=\sum_{g\in G}v(g)h(g).
\]

Since \(v\) has total mass zero and its positive and negative parts each have mass \(\delta=\|\nu-u_G\|_{\mathrm{TV}}\), any function whose range is contained in an interval of length \(L\) has \(|\sum_g v(g)h(g)|\le L\delta\). Here \(L=4/9-1/9=1/3\), proving (60) at the identity. Left translation by \(\sigma^{-1}\) reduces any other atom to the identity while preserving the uniform edge-marginal condition.

**Proof (matching sharp construction).** Let \(T\) denote the set of the ten vertex transpositions, and \(C\) the class of twenty vertex 3-cycles. Define probability laws

\[
P=\frac13\delta_1+\frac23 U_C,\qquad Q=U_T, \tag{63}
\]

where \(U_C\) and \(U_T\) are uniform on their respective conjugacy classes. Both laws are conjugation-invariant. Because the action on ordered edge pairs has exactly the three orbitals (equal, adjacent, disjoint), their complete one-point marginal matrices are determined by the average counts of \(F\) and \(A\). From the table,

\[
\mathbb E_P F=\frac13(10)+\frac23(1)=4=\mathbb E_Q F,
\qquad
\mathbb E_P A=\frac23(9)=6=\mathbb E_Q A.
\]

The disjoint-image count is the complement to ten, so it also agrees. It follows that \(P\) and \(Q\) have **exactly the same** one-point marginals for each ordered pair of edges.

The supports of \(P\) and \(Q\) are disjoint. For \(0\le\delta\le |T|/|G|=10/120=1/12\), the signed perturbation

\[
\nu_\delta=u_G+\delta(P-Q) \tag{64}
\]

is nonnegative because every transposition retains mass \(1/120-\delta/10\ge0\). All edge-marginals remain uniform, \(\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta\), and

\[
\nu_\delta(1)=\frac1{120}+\frac{\delta}{3}.
\]

The construction attains (60) at every stated \(\delta\), and left translation again handles any \(\sigma\). This completes the exact optimality proof. QED.

**Structural interpretation.** The fixed-point argument alone sees the maximum of \(F(g)\) among nonidentity elements (four fixed edges) and gives \(2/5\). The additional adjacent-edge orbital supplies a new linear constraint. The dual function \(h\) in (61) gives the better coefficient \(1/3\), while (63)--(64) attain that coefficient. The result illustrates why extending Theorem 15 to arbitrary transitive actions requires the full *orbital-marginal geometry*, rather than minimal degree alone.

The table, explicit dual range, equal marginal matrices, nonnegative perturbation, exact TV value and atom excess are replayed with Python integer/Fraction arithmetic in code/check_edge_action_s5.py. No linear-programming solver output is used as final evidence. A floating-point LP was used only to discover the certificate, and the proof above replaces it entirely.


## 17. Exact sharp atom modulus for every two-subset action of \(S_n\)

The exact \(S_5\) theorem has an **all-\(n\) closed-form extension**. The dual obstacle and the matching primal probability measures admit elementary polynomial proofs for both parities. This yields an infinite family of non-doubly-transitive actions whose atom-concentration constant is completely determined.

Write \(\Omega_n=\binom{[n]}2\), \(N=\binom n2\), and let \(G=S_n\) act on \(\Omega_n\) in the natural way. Let \(u\) be uniform on the \(n!\) elements of \(G\). A probability law \(\nu\) on \(G\) has *uniform edge-image marginals* if

\[
\nu\{g:g(E)=H\}=\frac1N\quad(E,H\in\Omega_n).
\]

**Theorem 17 (the complete two-subset atom-modulus law).** For every integer \(n\ge4\) define

\[
\boxed{
C_n=
\begin{cases}
\displaystyle\frac{n^2-2n+8}{(n+2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac{n^2-n+4}{(n+3)(n+4)},&n\text{ odd}.
\end{cases}} \tag{65}
\]

If \(\nu\) has uniform edge-image marginals, then for **every** \(\sigma\in S_n\),

\[
\left|\nu(\sigma)-\frac1{n!}\right|
\le C_n\,\|\nu-u\|_{\mathrm{TV}}. \tag{66}
\]

The coefficient \(C_n\) is **optimal for every \(n\ge4\)**. More precisely, for every \(\sigma\) there exists \(\delta_0(n)>0\) such that for every \(0\le\delta\le\delta_0(n)\) a uniform-edge-marginal law attains the positive equality

\[
\|\nu-u\|_{\mathrm{TV}}=\delta,\qquad
\nu(\sigma)=\frac1{n!}+C_n\delta. \tag{67}
\]

In particular,

\[
C_{2r}=1-\frac{8(2r)}{(2r+2)(2r+4)},\qquad
C_{2r+1}=1-\frac{8(2r+2)}{(2r+4)(2r+5)}.
\]

Thus \(C_n=1-8/n+O(n^{-2})\). In contrast, for this action the fixed-point/minimal-degree estimate is \(1-4(n-2)/(n(n-1))=1-4/n+O(n^{-2})\), which is strictly larger for every \(n\ge5\). The \(n=5\) case specializes to Theorem 16.

### 17.1. Two conjugacy statistics control all edge marginals

For a vertex permutation \(g\in S_n\), let \(x=x(g)\) be its number of fixed vertices, and \(y=y(g)\) its number of 2-cycles. Define \(F(g)\) as the number of unordered vertex pairs fixed as *sets*, and \(A(g)\) as the number of pairs whose images share exactly one vertex with the original pair. Then

\[
F(g)=\binom x2+y,\qquad
A(g)=(x+1)(n-x)-2y. \tag{68}
\]

To see the first identity, a fixed edge consists either of two fixed vertices or of one transposition cycle. For the second, edges joining a fixed to a moved vertex contribute \(x(n-x)\). Among edges joining moved vertices, those whose images intersect in exactly one vertex are exactly the consecutive pairs in each cycle of length at least three, one for each vertex in these cycles, giving \(n-x-2y\). All other edges are disjoint from their images.

Because simultaneous relabeling of the two edges has precisely three orbitals—equal, adjacent, and disjoint—any *conjugation-invariant* probability measure on \(S_n\) has its complete edge-image transition matrix determined by \(\mathbb EF\) and \(\mathbb EA\). No invariance is assumed for the arbitrary law \(\nu\) in (66).

Let \(T\) be the class of vertex transpositions. Then

\[
(F_T,A_T)=(N-2(n-2),\,2(n-2)). \tag{69}
\]

Let \(K_k\) be the class of one \(k\)-cycle with all other vertices fixed, \(3\le k\le n\). Then

\[
(F_{K_k},A_{K_k})
=\left(\binom{n-k}{2},\ k(n-k+1)\right),\quad
D_{K_k}:=N-F_{K_k}-A_{K_k}=\frac{k(k-3)}2. \tag{70}
\]

Let \(H\) denote the class of perfect vertex matchings if \(n\) is even (cycle type \(2^{n/2}\)), or of one 3-cycle together with \((n-3)/2\) transpositions if \(n\) is odd (cycle type \(3\,2^{(n-3)/2}\)). Its relevant statistics are

\[
(F_H,A_H,D_H)=
\begin{cases}
\left(n/2,0,n(n-2)/2\right),&n\text{ even},\\[2pt]
\left((n-3)/2,3,(n-3)(n+1)/2\right),&n\text{ odd}.
\end{cases} \tag{71}
\]

### 17.2. Explicit sharp measures for every \(n\)

Choose

\[
k=\begin{cases}
n/2+1,&n\text{ even},\\
(n+3)/2,&n\text{ odd},
\end{cases}
\qquad
s_n=\begin{cases}
\displaystyle\frac{2(n-4)}{(n-2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac2{n+4},&n\text{ odd}.
\end{cases} \tag{72}
\]

For all \(n\ge4\), \(0<C_n<1\), \(0\le s_n<1\), and the following are probability laws on \(S_n\):

\[
P=C_n\delta_{\mathrm{id}}+(1-C_n)\,U_{K_k},
\qquad
Q=(1-s_n)U_T+s_n U_H. \tag{73}
\]

Their supports are disjoint (at \(n=4\), \(s_n=0\)). We claim that \(P,Q\) have **identical edge-image marginals**. Both are conjugation-invariant, so it suffices to check the two expectations \(F,A\) discussed above.

Put \(w=1-C_n\). Formulae (69)–(72) give, in both parity cases,

\[
w\frac{k(k-3)}2=s_nD_H,\qquad
wk(n-k+1)=(1-s_n)\,2(n-2)+s_n A_H. \tag{74}
\]

For even \(n\), these identities follow by substituting
\(w=8n/((n+2)(n+4))\), \(k=(n+2)/2\), and
\(D_H=n(n-2)/2\). For odd \(n\), substitute
\(w=8(n+1)/((n+3)(n+4))\), \(k=(n+3)/2\), and \(D_H=(n-3)(n+1)/2\). The first identity matches the mean number of disjoint edge-images, while the second matches adjacent images. The fixed-image mean agrees automatically, since these three counts sum to \(N\). Therefore all marginal probabilities agree.

Because \(P,Q\) are disjoint, for any sufficiently small \(\delta\ge0\) the signed perturbation

\[
\nu_\delta=u+\delta(P-Q) \tag{75}
\]

remains a probability law. Specifically, one may take

\[
0\le\delta\le \delta_0(n):=
\left(n!\max_{g\in S_n}Q(g)\right)^{-1}>0.
\]

It has uniform edge-image marginals, TV distance exactly \(\delta\), and \(\nu_\delta(\mathrm{id})=1/n!+C_n\delta\). Left translation extends this to any \(\sigma\). Thus to complete Theorem 17 it remains only to prove the universal upper bound (66).

### 17.3. Exact even-degree dual certificate

Suppose \(n\ge4\) is even. Define

\[
L_e(g)=4F(g)-(n-4)A(g),\qquad
D_e=(n-2)(n+2)(n+4),
\quad h_e(g)=\mathbf1_{\{g=\mathrm{id}\}}-\frac{4L_e(g)}{D_e}. \tag{76}
\]

For any nonidentity permutation \(g\), \(0\le x(g)\le n-2\) and
\(0\le y(g)\le(n-x(g))/2\). By (68),

\[
L_e(x,y)=
(n-2)x^2-(n-2)(n-3)x-n(n-4)+2(n-2)y. \tag{77}
\]

The positive coefficient of \(y\) and the quadratic minimum at
\(x=(n-3)/2\) show that for integer \(x\), \(L_e(x,y)\ge L_e(K_k)\), attained by either adjacent integer closest to that half-integer. Our chosen \(K_k\), for which \(x=(n-2)/2\) and \(y=0\), is one such minimizer.

For the other side, insert \(y\le(n-x)/2\) in (77). Elementary factorization gives

\[
L_e(x,y)\le 2n-(n-2)x(n-2-x)\le2n=L_e(T)=L_e(H). \tag{78}
\]

Thus every \(g\ne\mathrm{id}\) satisfies \(L_e(K_k)\le L_e(g)\le2n\). Direct substitution also gives

\[
4\big(L_e(\mathrm{id})-L_e(K_k)\big)=D_e. \tag{79}
\]

Consequently \(h_e\) lies **everywhere on \(S_n\)** in the interval

\[
-\frac{8n}{D_e}
\ \le\ h_e(g)\ \le\
1-\frac{16N}{D_e},
\]

whose length is exactly

\[
\left(1-\frac{16N}{D_e}\right)+\frac{8n}{D_e}
=\frac{n^2-2n+8}{(n+2)(n+4)}=C_n. \tag{80}
\]

Since \(v=\nu-u\) has zero total mass and the same edge-image marginals as zero, it annihilates both \(F\) and \(A\). Therefore

\[
\nu(\mathrm{id})-\frac1{n!}
=\sum_{g\in S_n}v(g)h_e(g),
\]

whose absolute value is at most \(C_n\|v\|_{\mathrm{TV}}\), because the positive and negative parts of \(v\) have equal total mass \(\|v\|_{\mathrm{TV}}\) and the range length of \(h_e\) is \(C_n\).

### 17.4. Exact odd-degree dual certificate

Suppose \(n\ge5\) is odd. Put

\[
L_o(g)=\frac{n^2-6n+11}{2}\,A(g)-(2n-7)\,F(g),\quad
D_o=\frac{(n-3)(n-2)(n+3)(n+4)}8,
\quad h_o(g)=\mathbf1_{\{g=\mathrm{id}\}}+\frac{L_o(g)}{D_o}. \tag{81}
\]

We claim that for all nonidentity \(g\),

\[
L_o(T)=L_o(H)\le L_o(g)\le L_o(K_k). \tag{82}
\]

For the upper bound, the coefficient of \(y\) in \(L_o(x,y)\) is exactly \(-(n-2)^2<0\), so \(L_o(x,y)\le L_o(x,0)\). The latter is a concave quadratic in \(x\), with real maximum at

\[
x_*=\frac{n-3}{2}+\frac{3}{2(n-2)}.
\]

Because \(x\) is an integer and \(n\ge5\) is odd, its maximum is attained at \(x=(n-3)/2\) (also at the adjacent integer when \(n=5\)). This is exactly the fixed-vertex count of \(K_k\), proving the upper bound.

For the lower bound first assume \(1\le x\le n-2\). Because \(y\le(n-x)/2\) and its coefficient is negative, direct factorization gives

\[
\begin{aligned}
L_o(x,y)-L_o(T)
&\ge L_o\!\left(x,\frac{n-x}{2}\right)-L_o(T)\\
&=\frac{n-2}{2}(n-2-x)\big((n-2)x-3\big)\ge0, \tag{83}
\end{aligned}
\]

where the final inequality uses \(n\ge5\) and \(x\ge1\). If \(x=0\), the number of 2-cycles satisfies \(y\le(n-3)/2\): otherwise the odd number \(n-2y\) of remaining vertices would equal one and create a fixed point. Therefore

\[
L_o(0,y)\ge L_o\!\left(0,\frac{n-3}{2}\right)=L_o(T). \tag{84}
\]

This proves (82) for every nonidentity element. Direct substitution also verifies

\[
L_o(K_k)-L_o(\mathrm{id})=D_o,\qquad
L_o(K_k)-L_o(T)=
\frac{(n-3)(n-2)(n^2-n+4)}8. \tag{85}
\]

Hence the identity attains the same **maximum** of \(h_o\) as \(K_k\), and the transposition class attains its minimum. Their difference is

\[
\frac{L_o(K_k)-L_o(T)}{D_o}
=\frac{n^2-n+4}{(n+3)(n+4)}=C_n. \tag{86}
\]

As in the even case, the difference \(v=\nu-u\) annihilates both \(F,A\) and has equal positive/negative total variation masses. Integrating \(h_o\) proves
\(\left|\nu(\mathrm{id})-1/n!\right|\le C_n\|v\|_{\mathrm{TV}}\).
Left translation again treats arbitrary \(\sigma\). This concludes the universal inequality, while the matching construction (73)–(75) gives sharpness. **Theorem 17 is proved for all \(n\ge4\).** QED.

**Why minimal degree is genuinely weaker.** For the edge action, the vertex transposition fixes \(N-2(n-2)\) edges and maximizes the number of fixed edges among nonidentity vertex permutations (use \(F=\binom x2+y\), \(x\le n-2\), \(y\le(n-x)/2\)). The resulting upper coefficient is \(1-4(n-2)/(n(n-1))\). Subtracting \(C_n\) gives

\[
\begin{cases}
\displaystyle\frac{4(n-4)(n^2-2n-4)}{n(n-1)(n+2)(n+4)},&n\text{ even},\\[5pt]
\displaystyle\frac{4(n^3-5n^2+24)}{n(n-1)(n+3)(n+4)},&n\text{ odd},
\end{cases}
\]

strictly positive for every \(n\ge5\). The improvement is of order \(4/n\).

**Reproducibility.** The checker code/check_all_two_subset_actions.py exhausts all conjugacy types (integer partitions) for \(4\le n\le40\), checks the exact rational dual range and all four moment/positivity conditions for the primal construction, and matches the closed formula \(C_n\). This finite replay is **not** the proof for arbitrary \(n\); the symbolic quadratic estimates (77)–(86) and the explicit measures (73)–(75) supply that proof. In particular, the original floating-point LP exploration is discovery-only and no solver result is used as a theorem premise.


## 18. Universal orbital primal-dual theorem for finite permutation actions

Theorems 15–17 are instances of a general exact principle: **the sharp single-atom response to marginal-preserving perturbations is determined by a finite rational linear program on the conjugacy classes and the orbitals of the permutation representation**. In a doubly transitive action there are only two orbitals; in the two-subset action there are three. This explains the difference between the minimal-degree formula and the exact edge-action law.

Let \(G\) be a finite group acting (not necessarily transitively or faithfully) on a finite nonempty set \(\Omega\), with \(e\in G\) its identity. Write \(u_G\) for the uniform law on \(G\), and let \(\mathcal V\) be the real vector space of signed functions \(v:G\to\mathbb R\) satisfying

\[
\sum_{g\in G}v(g)=0,\qquad
\sum_{\substack{g\in G\\g(x)=y}}v(g)=0
\quad\text{for all }x,y\in\Omega. \tag{87}
\]

Let \(\mathcal O_1,\ldots,\mathcal O_r\) be the orbitals of the action, i.e. the orbits of \(G\) on \(\Omega\times\Omega\) under simultaneous relabeling. Define their *orbital displacement counts*

\[
F_j(g)=\#\{x\in\Omega:(x,g(x))\in\mathcal O_j\}. \tag{88}
\]

Each \(F_j\) is constant on conjugacy classes of \(G\). Let \(C_1,\ldots,C_s\) be those conjugacy classes, with \(C_1=\{e\}\), and put

\[
M_{ji}=\frac1{|C_i|}\sum_{g\in C_i}F_j(g),\qquad
M\in\mathbb Q^{r\times s}. \tag{89}
\]

For \(\mathcal V\ne\{0\}\), define

\[
\mathcal C(G,\Omega)=\sup_{\substack{v\in\mathcal V\\v\ne0}}
\frac{|v(e)|}{\tfrac12\sum_g|v(g)|}. \tag{90}
\]

For \(\mathcal V=\{0\}\), set \(\mathcal C(G,\Omega)=0\). The supremum is finite and \(0\le\mathcal C(G,\Omega)\le1\).

**Theorem 18 (exact orbital primal-dual characterization).** The following four quantities are all equal:

\[
\begin{aligned}
\mathcal C(G,\Omega)
&=\max_{\substack{P,Q\text{ probability laws on }G\\
P\{g:gx=y\}=Q\{g:gx=y\}\ \forall x,y}}
\big(P(e)-Q(e)\big)\\
&=\max_{\substack{p,q\in\mathbb R_{\ge0}^{s}\\
\mathbf1^Tp=\mathbf1^Tq=1,\ Mp=Mq}}
(p_1-q_1)\\
&=\min_{\lambda\in\mathbb R^r}
\left[
\max_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
-\min_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
\right]\\
&=\min_{\varphi\in\mathrm{span}_{\mathbb R}\{F_1,\ldots,F_r\}}
\operatorname{osc}_{g\in G}\big(\mathbf1_{\{g=e\}}-\varphi(g)\big).
\tag{91}
\end{aligned}
\]

Both finite LPs in the middle have **rational optimal solutions**, so \(\mathcal C(G,\Omega)\in\mathbb Q\). If \(\mathcal C(G,\Omega)>0\), there exist two **conjugation-invariant, disjointly supported** probability laws \(P,Q\) with identical one-point marginals and \(P(e)-Q(e)=\mathcal C(G,\Omega)\). Hence for all sufficiently small \(\delta\ge0\),

\[
\nu_\delta=u_G+\delta(P-Q) \tag{92}
\]

is a probability law with exactly the same one-point marginals as \(u_G\) and

\[
\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta,\qquad
\nu_\delta(e)-u_G(e)=\mathcal C(G,\Omega)\delta. \tag{93}
\]

For an arbitrary probability law \(\nu\) whose marginals match \(u_G\), and any \(\sigma\in G\),

\[
\left|\nu(\sigma)-\frac1{|G|}\right|
\le\mathcal C(G,\Omega)\|\nu-u_G\|_{\mathrm{TV}}, \tag{94}
\]

with this constant optimal whenever it is positive. Left translation moves the sharp construction from \(e\) to any prescribed \(\sigma\).

**Proof.** First formulate a finite **unreduced** LP. Choose \(P,Q\) as nonnegative probability vectors indexed by \(G\), impose their equality of all one-point marginals, and maximize \(P(e)-Q(e)\). Call its optimum \(\gamma\).

For any feasible pair, \(v=P-Q\in\mathcal V\), \(\|v\|_{\mathrm{TV}}\le1\), so \(P(e)-Q(e)\le\mathcal C(G,\Omega)\). Conversely, for any nonzero \(v\in\mathcal V\), its Jordan parts \(v_+,v_-\) each have mass \(d=\|v\|_{\mathrm{TV}}>0\), and the probability measures \(P=v_+/d,\ Q=v_-/d\) have identical marginals. Exchanging them if necessary, they give objective \(|v(e)|/d\). Hence \(\gamma=\mathcal C(G,\Omega)\). If \(\mathcal V=\{0\}\), the two quantities are both zero.

The unreduced primal is a rational finite LP. Its dual has one unrestricted multiplier \(\lambda_{xy}\) for each marginal equality and two normalization multipliers \(a,b\). Write

\[
\phi(g)=\sum_{x,y\in\Omega}\lambda_{xy}\,\mathbf1_{\{g(x)=y\}}.
\]

Dual feasibility is exactly

\[
a\ge\mathbf1_{\{g=e\}}-\phi(g),\qquad
b\ge-\mathbf1_{\{g=e\}}+\phi(g)
\quad\text{for all }g\in G.
\]

Minimizing \(a+b\) for fixed \(\phi\) gives
\(\max_g(\mathbf1_{\{g=e\}}-\phi(g))-
\min_g(\mathbf1_{\{g=e\}}-\phi(g))\), its oscillation. The primal is feasible (take \(P=Q=u_G\)) and bounded, so **finite-dimensional LP strong duality** gives equality with the minimum oscillation. The LP has rational coefficients and a finite attained optimum; standard rational Gaussian elimination at a basic feasible optimum gives rational primal and dual certificates.

Next average an optimal primal pair under simultaneous conjugation by \(h\in G\): replace \(P,Q\) by the averages of their pushforwards under \(g\mapsto hgh^{-1}\). Equal one-point marginals remain equal because conjugating both pairs of image coordinates by \(h\) permutes the constraints. The identity atom and the objective are unchanged. Thus a conjugation-invariant optimal pair exists. Such pairs assign a constant probability density to each conjugacy class, and their equality of one-point marginals is equivalent to the reduced moment equation \(Mp=Mq\): for a central law, each entry \(\Pr(gx=y)\) is constant on the orbital containing \((x,y)\), and its orbital average is \(\mathbb EF_j/|\mathcal O_j|\). This proves the second line of (91).

Similarly, average any dual function \(\phi\) over conjugations. The indicator \(\mathbf1_{\{g=e\}}\) is conjugacy invariant, while oscillation is convex and invariant under conjugation; the average cannot increase oscillation. A conjugation-averaged linear combination of the image indicators has coefficients constant on their simultaneous \(G\)-orbits in \(\Omega\times\Omega\). Therefore it lies in \(\mathrm{span}\{F_j\}\). This proves the fourth line of (91). Evaluating the same oscillation on conjugacy classes gives the third line, whose entries are precisely (89).

When the optimum \(\gamma>0\), an optimal reduced pair \(P,Q\) must be **mutually singular**. Otherwise \(d=\|P-Q\|_{\mathrm{TV}}<1\), and its Jordan parts normalized by \(d\) would form an admissible pair with strictly larger objective \(\gamma/d>\gamma\), contradiction. Thus the supports of an optimal central \(P,Q\) are disjoint and (92) is a probability measure for every
\(0\le\delta\le(|G|\max_gQ(g))^{-1}\), with all the stated identities.

Finally, for any law \(\nu\) with the uniform law's one-point marginals, \(v=\nu-u_G\in\mathcal V\) and the defining norm bound gives (94) at the identity. Replacing \(\nu\) by its left translate by \(\sigma^{-1}\) preserves marginal equality with \(u_G\), total variation and atom excess, proving (94) for every \(\sigma\). The same translation transports the attained equality. QED.

**Consequences and scope.** Theorem 18 gives a fully finite **exact certificate interface** for *every* finite permutation group action: exhibit a central primal pair of matching orbital moments and a dual orbital linear combination whose oscillation equals the primal atom excess. It also explains Theorem 15 (rank-two orbital geometry and a single fixed-point statistic), Theorem 16 (rank-three geometry in degree ten), and Theorem 17 (a full parity-dependent family of exact rank-three optima). The theorem does **not** assert a similarly explicit symbolic formula for arbitrary higher-rank actions. Determining a closed analytic optimum for \(S_n\) acting on \(k\)-subsets with \(k\ge3\) is a natural next target; numerical LP output there must be converted to rational primal-dual certificates before any theorem claim.


## 19. A complete certified three-subset spectrum through degree 23

The general orbital principle of Theorem 18 also yields an exact finite classification in the **next Johnson rank**, namely \(S_n\) acting on its three-element subsets. In this case, ordered pairs of subsets have four orbitals, indexed by their intersection sizes \(0,1,2,3\). The optimal coefficient is no longer given by the simple parity formula of Theorem 17, but a complete fixed rational certificate has been constructed for **every degree \(3\le n\le23\)**.

Define \(C_n^{(3)}\) to be the optimal atom-vs-TV coefficient for \(S_n\) on \(\binom{[n]}3\) under marginal preservation, as in Theorem 18. For \(n=3\), the subset action is trivial and \(C_3^{(3)}=1\). For \(n=4\), the complement map identifies the action with the natural doubly transitive action of \(S_4\), so \(C_4^{(3)}=1/2\) by Theorem 15. For \(n=5\), complementation identifies the triple action with the pair action, giving \(C_5^{(3)}=C_5=1/3\) by Theorem 17.

**Theorem 19 (complete exact small-degree triple-action classification).** For every \(6\le n\le23\), the exact optimum is given in the following table. Together with the three elementary cases above, this determines **every degree \(3\le n\le23\)**.

| \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) | \(n\) | \(C_n^{(3)}\) |
|---:|---:|---:|---:|---:|---:|
|6|5/14|12|97/232|18|5656/11331|
|7|5/14|13|283/661|19|3859/7609|
|8|89/244|14|1328/2975|20|169/322|
|9|259/691|15|14311/31629|21|7411/13909|
|10|368/935|16|5579/11744|22|2485/4554|
|11|1027/2593|17|1679/3469|23|6219/11242|

The exact statement includes **attainment** of each bound by a sufficiently small marginal-preserving rational perturbation of the uniform law. No claim for every \(n>23\) or of an all-\(n\) closed formula is made.

### 19.1. Fixed primal-dual certificates

For each \(n=6,\ldots,23\), the public file

\[
\text{certificates/three\_subset\_n6\_23.json} \tag{95}
\]

contains **fixed exact fractions** specifying:

- two conjugation-invariant probability measures \(P_n,Q_n\), each as weights on explicit \(S_n\) conjugacy classes (cycle partitions);
- three rational dual coefficients \(\lambda_0,\lambda_1,\lambda_2\), associated with the three nonidentity-intersection orbital counts;
- two rational dual extrema \(\ell_n,u_n\);
- the proposed exact optimum \(c_n=u_n-\ell_n=P_n(e)-Q_n(e)\).

The supports are disjoint, and no entry is a decimal approximation.

For clarity, if \(g\in S_n\), set

\[
F_j(g)=\#\left\{E\in\binom{[n]}3:\ |E\cap g(E)|=j\right\},
\qquad j=0,1,2,3. \tag{96}
\]

Each \(F_j\) is constant on conjugacy classes. The certificate verifier independently checks for every \(n\) that

\[
\begin{aligned}
&\sum_{g}P_n(g)=\sum_{g}Q_n(g)=1,\qquad P_n,Q_n\ge0,\qquad
\operatorname{supp}P_n\cap\operatorname{supp}Q_n=\varnothing,\\
&\mathbb E_{P_n}F_j=\mathbb E_{Q_n}F_j\quad(0\le j\le3),\\
&\ell_n\le
\mathbf1_{\{g=e\}}-\sum_{j=0}^{2}\lambda_jF_j(g)
\le u_n\quad\text{for every conjugacy class }[g]\subseteq S_n,\\
&\left(\mathbf1_{\{g=e\}}-\sum_{j=0}^{2}\lambda_jF_j(g)\right)
=\begin{cases}u_n,&g\in\operatorname{supp}P_n,\\
\ell_n,&g\in\operatorname{supp}Q_n,
\end{cases}\\
&u_n-\ell_n=P_n(e)-Q_n(e)=c_n.
\tag{97}
\end{aligned}
\]

Because the action on ordered pairs of triples has exactly the four intersection-size orbitals, equality of the four moments is **equivalent to equality of all one-point triple-image marginals** for the central measures \(P_n,Q_n\). The central dual function in (97) is a linear combination of the marginal indicators. Its oscillation bounds the atom defect of *any* marginal-preserving law, central or not. Conversely, for all sufficiently small \(\delta>0\),

\[
\nu_\delta=u_{S_n}+\delta(P_n-Q_n)
\]

is nonnegative, retains uniform triple-image marginals, has TV distance \(\delta\), and its identity atom increases by exactly \(c_n\delta\). Thus (97) supplies both the universal upper bound and an attaining lower bound for each degree.

### 19.2. Reproducible finite exhaustive proof

The fixed JSON certificate file and the **separate optimizer-free checker**

\[
\text{code/check\_three\_subset\_certificates.py} \tag{98}
\]

form the complete finite proof evidence. The checker uses only standard-library integer and \(\mathrm{fractions.Fraction}\) arithmetic, not SciPy, SymPy, a numerical optimizer, randomization, or floating-point values. It independently enumerates every integer partition of every \(n=6,\ldots,23\). Integer partitions parameterize **all** \(S_n\) conjugacy classes, so verifying (97) on one canonical cycle representative of each partition checks the dual inequality on **every permutation**. For each representative it enumerates every three-element subset, explicitly counts the four intersection orbitals, and evaluates all primal and dual assertions as rational equalities or inequalities. It additionally verifies the exact conjugacy-class cardinalities sum to \(n!\), positive perturbation margins, all certificate contact equalities and the values in the table.

The program verifies a **finite, fixed** mathematical assertion, not an infinite family inferred from sample data. Termination is manifest from the bounded partition/subset loops. A separate script, code/generate_three_subset_certificates.py, reconstructs the fixed fractions by rational Gaussian elimination on predetermined class supports. The **checker does not call or trust this generator** and accepts only the separately published fixed JSON data.

A fresh-copy Windows replay downloaded both the published JSON and the standalone checker into a new isolated directory, ran the checker, and returned

\[
\texttt{EIGHTEEN EXACT THREE-SUBSET CERTIFICATES REPLAYED}
\]

followed by a successful fresh-public-source completion marker. The full independent replay and its boundaries are recorded in VERIFICATION.md.

**Scope and open continuation.** Unlike Theorem 17, this is an **exact finite classification**, not a universal closed expression for \(C_n^{(3)}\). The increasingly varied conjugacy-class supports suggest phase changes in the rank-four orbital convex hull. Determining an all-\(n\) algebraic formula, stabilization ranges, or rigorous asymptotic expansion is the next natural theoretical step. Any conjecture about \(n>23\) must remain labelled computational until its own proof or independently verified certificates exist.


## 20. An exact three-cycle-statistic compression theorem

The rank-four orbital data for the natural \(S_n\)-action on its three-element subsets have a much simpler representation than full conjugacy-class partitions suggest. **Only the counts of cycles of lengths 1, 2 and 3 matter.** This fact gives a finite rational LP with \(O(n^3)\) candidate types and makes exact certificates for substantially larger degrees practical.

Let \(n\ge3\), \(\Omega=\binom{[n]}3\), and let \(g\in S_n\) have \(x\) fixed points, \(y\) two-cycles and \(z\) three-cycles. For \(j=0,1,2,3\), write

\[
F_j(g)=\#\{E\in\Omega:|E\cap g(E)|=j\},
\qquad N=\binom n3.
\]

**Theorem 20 (three-cycle compression).** Define

\[
\begin{aligned}
M_1(x)&=x\binom{n-1}{2}+(n-x)(n-2)
     =\frac{n-2}{2}\,[2n+(n-3)x],\\
M_2(x,y)&=(n-2)\binom x2+x(n-x)+(n-2)y+(n-x-2y)\\
        &=(n-2)\binom x2+(x+1)(n-x)+(n-4)y,\\
M_3(x,y,z)&=\binom x3+xy+z.
\tag{99}
\end{aligned}
\]

Then

\[
\boxed{
\begin{aligned}
F_3&=M_3,\\
F_2&=M_2-3M_3,\\
F_1&=M_1-2M_2+3M_3,\\
F_0&=N-M_1+M_2-M_3.
\end{aligned}} \tag{100}
\]

In particular, all four orbital counts depend **only** on \((x,y,z)\), not on the remaining cycle structure.

Moreover, a triple of nonnegative integers \((x,y,z)\) occurs for some permutation in \(S_n\) **if and only if**

\[
r:=n-x-2y-3z\quad\text{equals \(0\) or is at least \(4\)}. \tag{101}
\]

Every feasible triple has the canonical representative with cycle type
\(1^x2^y3^z\), supplemented by one \(r\)-cycle if \(r\ge4\).
Consequently the *full* rational primal-dual LP of Theorem 18 can be compressed, **without changing its optimum**, to the finite set

\[
\mathcal T_n=
\{(x,y,z)\in\mathbb Z_{\ge0}^3:
n-x-2y-3z\in\{0\}\cup[4,\infty)\}. \tag{102}
\]

Here \(|\mathcal T_n|=O(n^3)\), instead of the partition number \(p(n)\) conjugacy classes. Each compressed primal variable represents a central probability mass distributed uniformly on its canonical conjugacy class. Group elements with the same \((x,y,z)\) have identical dual evaluations, so no constraint is lost.

**Proof.** Let \(K(E)=|E\cap g(E)|\) for \(E\in\Omega\). Binomial inversion on \(K\in\{0,1,2,3\}\) shows that the four \(F_j\) are determined by

\[
M_a=\sum_{E\in\Omega}\binom{K(E)}a,\qquad a=1,2,3,
\]

together with \(M_0=N\); solving this triangular system gives (100).

To count \(M_1\), fix a vertex \(v\). If \(g(v)=v\), then \(v\) lies in \(E\cap g(E)\) exactly when \(v\in E\), giving \(\binom{n-1}{2}\) triples. Otherwise, both \(v\) and its distinct preimage \(g^{-1}(v)\) must be in \(E\), giving \(n-2\) triples. Summing over the \(x\) fixed and \(n-x\) moved vertices gives the first formula in (99).

For \(M_2\), count unordered pairs \(\{v,w\}\subset E\cap g(E)\). There are four disjoint cases:

- Both are fixed: \(\binom x2\) possible vertex pairs, each in \(n-2\) triples.
- Exactly one is fixed: \(x(n-x)\) pairs, each determining its unique required third vertex \(g^{-1}(w)\) (or \(g^{-1}(v)\)).
- They are the two vertices of the same transposition: \(y\) pairs, each in \(n-2\) triples.
- They are consecutive in a cycle of length at least three: every such cycle contributes exactly its length many unordered adjacent pairs, so \(n-x-2y\) pairs overall; each has exactly one completing third vertex.

There are no other pairs for which the four vertices \(v,w,g^{-1}(v),g^{-1}(w)\) occupy at most three distinct positions. This establishes \(M_2\).

Finally, \(K(E)=3\) precisely when \(g(E)=E\). A three-point invariant set is a union of cycles of total size three, hence is either three fixed points, a fixed point plus a transposition, or one three-cycle. There are exactly \(\binom x3+xy+z\) such sets. This is \(M_3\).

Cycles of length at least four account for \(r\) vertices. Their total size is either zero or at least four; conversely one \(r\)-cycle realizes every \(r\ge4\). This proves (101). Theorem 18 already reduces the marginal-constrained optimization to conjugation-invariant probability distributions and conjugacy-invariant orbital dual functions. Since their orbital data factor through \((x,y,z)\), aggregating probabilities over classes with identical triples preserves all constraints and the distinguished identity atom; conversely each feasible triple has the displayed representative. Thus this aggregation preserves the optimum. QED.

**Note on complexity.** The theorem changes the *number of distinct constraints* from \(p(n)\) to \(O(n^3)\). It does not say that an optimizer is trustworthy by itself: any claimed optimum still requires exact primal weights and a dual function whose inequalities are checked for all types in (102).

## 21. Complete exact rank-four atom-modulus classification through degree 120

The compression theorem enables a substantial extension of Theorem 19 while retaining a short, **independent and optimizer-free** integer checker.

**Theorem 21 (finite exact triple-action classification).** The sharp coefficient \(C_n^{(3)}\) for \(S_n\) acting on \(\binom{[n]}3\), under preservation of all triple-image one-point marginals, is now determined **exactly for every \(3\le n\le120\)**.

Degrees \(3\le n\le23\) are covered by Theorems 15, 17 and 19 and their earlier fixed certificates. For each degree \(24\le n\le120\), the additional fixed public certificate file

\[
\texttt{certificates/three\_subset\_n24\_120.json} \tag{103}
\]

contains an explicit pair of *conjugation-invariant*, disjointly supported probability measures \(P_n,Q_n\), each described by rational masses on canonical cycle types of the form \((x,y,z,r)\), together with three rational coefficients \(\lambda_{0,n},\lambda_{1,n},\lambda_{2,n}\), dual extrema \(\ell_n,u_n\), and the exact fraction

\[
C_n^{(3)}=P_n(e)-Q_n(e)=u_n-\ell_n. \tag{104}
\]

For clarity, selected newly certified values are

| \(n\) | Exact \(C_n^{(3)}\) | \(n\) | Exact \(C_n^{(3)}\) |
|---:|:---|---:|:---|
|24|32461/57220|25|80848/140761|
|26|108592/185523|30|102746/165985|
|40|284639/416012|50|555884/760975|
|60|822469/1074757|70|4211614/5317095|
|80|18639283/22912384|90|38205728/45980475|
|100|3177111/3758198|120|53562383/61708904|

Every one of the other exact fractions for \(24\le n\le120\) appears in (103). No extrapolation beyond degree 120 is asserted.

**Proof by independently checkable finite rational certificates.** For each \(n=24,\ldots,120\), the fixed JSON file records three positive rational masses for \(P_n\) (one on the identity class) and two for \(Q_n\), summing to one on each side. The verifier checks that their canonical conjugacy-class supports are disjoint and that all four orbital moments match:

\[
\mathbb E_{P_n}F_j=\mathbb E_{Q_n}F_j\qquad(0\le j\le3). \tag{105}
\]

Since both are class-invariant, these four equalities imply equality of **every** triple-image marginal (Theorem 18). For the recorded dual data, define

\[
h_n(g)=\mathbf1_{\{g=e\}}-
\sum_{j=0}^2\lambda_{j,n}F_j(g). \tag{106}
\]

The public checker then verifies **for every** \((x,y,z)\in\mathcal T_n\),

\[
\ell_n\le h_n(x,y,z)\le u_n, \tag{107}
\]

and equality with \(u_n\) on all \(P_n\)-support classes and \(\ell_n\) on all \(Q_n\)-support classes. By Theorem 20, this is an exhaustive check over **all possible** \(S_n\) conjugacy classes, including those having many cycles of length at least four. No unexamined real or integer parameter remains in the stated finite degree range.

All dual denominators are cleared first, so (107) is verified by **integer comparisons**; the only fractions handled are the five primal weights and three dual coefficients per degree. The checker also verifies normalizations, all moment equations, positive class cardinalities and an explicit small rational \(\delta>0\) for which \(u_{S_n}+\delta(P_n-Q_n)\) is a probability law. Theorem 18 now proves the upper bound \(C_n^{(3)}\le u_n-\ell_n\), while this actual attaining perturbation proves the reverse inequality. The exact identity (104) is checked for each degree. Hence every advertised coefficient is rigorously established by a finite replayable certificate. QED.

**Computational trust boundary.** The published standalone program
\(\texttt{code/check\_three\_subset\_compressed\_24\_120.py}\)
uses **only Python 3 standard-library integers and fractions**. Its loops cover the 97 degrees and all \(\mathcal T_n\), amounting to exactly **1,489,083 compressed type evaluations** in the fixed range. It uses no optimizer, floating-point comparison, Sage, SciPy, SymPy or solver oracle. The original support discovery *did* use floating-point linear programming, followed by exact rational reconstruction; that discovery history is not used by the checker or as a logical premise of Theorem 21.

This is a **large but finite** exact classification. Neither the observed apparent support periodicity nor the numerical trend of \(C_n^{(3)}\) justifies claiming an all-degree formula or asymptotic expansion. The next frontier is to prove an infinite parameterized primal-dual family, ideally by factorization of the cubic polynomial (106) in the constrained cycle-count region (102).


## 22. Sharp universal first-order asymptotics for all three-subset actions

The exact finite classification through \(n=120\) does **not** by itself imply a uniform formula. Nevertheless, the orbital compression theorem permits a genuine **infinite-parameter asymptotic theorem** with a sharp leading constant.

**Theorem 22 (universal sharp first-order asymptotic).** For the sharp marginal-preserving single-atom total-variation coefficient \(C_n^{(3)}\) of the \(S_n\) action on three-element subsets,

\[
\boxed{\displaystyle
C_n^{(3)}=1-\frac{18}{n}+O(n^{-2}),
\qquad
\lim_{n\to\infty}n\bigl(1-C_n^{(3)}\bigr)=18.} \tag{108}
\]

The upper bound has the following **explicit** universal version: for every integer \(n\ge2048\),

\[
C_n^{(3)}\le
1-\frac{18}{n}+\frac{406304}{n^2}. \tag{109}
\]

The lower bound in (108) is supplied by explicit, exactly moment-matched positive rational probability measures for **every sufficiently large** \(n\), not by extrapolation from finite optimization.

### 22.1. A uniform analytic dual bound

For every \(n\ge3\), set

\[
\lambda_0=-\frac6{n^3}+\frac{18}{n^4},\qquad
\lambda_1=\frac{12}{n^3}-\frac{436}{n^4},\qquad
\lambda_2=-\frac{18}{n^3}+\frac{198}{n^4}
\tag{110}
\]

and define the central dual function

\[
h_n(g)=\mathbf1_{\{g=e\}}-\sum_{j=0}^2\lambda_jF_j(g),
\tag{111}
\]

where \(F_j\) are the exact triple-action orbital counts of Theorem 20. Evidently \(h_n(e)=1\), because \(F_0(e)=F_1(e)=F_2(e)=0\).

For nonidentity \(g\), let \(x,y,z\) count its 1-, 2- and 3-cycles, and introduce

\[
a=x/n,\qquad b=y/n,\qquad c=z/n.
\]

Then \(0\le a\le1-2/n\), \(0\le b\le(1-a)/2\), and \(0\le c\le1/3\). Substituting the **polynomial identities (99)–(100)** into (111), and collecting exact powers of \(1/n\), gives

\[
h_n(g)=H(a)+\frac{J(a,b)}n+\frac{R_2(a,b,c)}{n^2}
                   +\frac{R_3(a,b,c)}{n^3}, \tag{112}
\]

where

\[
\begin{aligned}
H(a)&=(1-a)(4a-1)^2
     =1-a(4a-3)^2,\\
J(a,b)&=320a^3-592a^2+296a-24+48b(1-2a),\\
R_2(a,b,c)&=1216a^2+1920ab-1765a-1280b-96c+549,\\
R_3(a,b,c)&=2(1001a+2176b+960c-1001).
\end{aligned} \tag{113}
\]

These are exact identities, not asymptotic fits. The sum of the absolute integer coefficients in \(R_2,R_3\) is \(6826+10276=17102\). Since \(0\le a,b,c\le1\),

\[
\left|\frac{R_2}{n^2}+\frac{R_3}{n^3}\right|
\le\frac{17102}{n^2}
\qquad(n\ge1). \tag{114}
\]

Put \(J_0(a)=J(a,0)\). Its derivative satisfies \(|J_0'(a)|\le2440\) on \([0,1]\), and

\[
J_0(1/4)=18,\qquad J_0(3/4)=0.
\tag{115}
\]

For any fixed \(a\), the coefficient of \(b\) in \(J\) is \(48(1-2a)\). Thus, using \(0\le b\le(1-a)/2\),

\[
\begin{array}{ll}
a\le1/2:&
J_0(a)\le J(a,b)\le J_0(a)+24(1-a)(1-2a)
=32a(1-a)(7-10a),\\[2pt]
a\ge1/2:&
32a(1-a)(7-10a)\le J(a,b)\le J_0(a).
\end{array} \tag{116}
\]

We now establish the fully uniform bounds

\[
\frac{18}{n}-\frac{203152}{n^2}
\le h_n(g)\le
1+\frac{203152}{n^2}
\quad\text{for every }g\ne e,\quad n\ge2048. \tag{117}
\]

**Upper bound.** When \(a\le1/2\), (116) gives \(J(a,b)\le224a\), while
\(1-H(a)=a(4a-3)^2\ge a\). Hence \(H+J/n\le1\) for \(n\ge224\).

When \(a\ge1/2\), (115)–(116) give
\(J(a,b)\le2440|a-3/4|\), while
\(1-H(a)=16a(a-3/4)^2\ge8(a-3/4)^2\). Completing the square,

\[
H(a)+J(a,b)/n\le
1+\frac{2440^2}{32n^2}
=1+\frac{186050}{n^2}.
\]

Combine with (114) to get the upper half of (117), with
\(186050+17102=203152\).

**Lower bound, \(a\le1/2\).** By (115)–(116),
\(J(a,b)\ge18-2440|a-1/4|\).
Also \(H(a)=16(1-a)(a-1/4)^2\ge8(a-1/4)^2\).
Another completion of the square yields
\(H+J/n\ge18/n-186050/n^2\); use (114).

**Lower bound, \(1/2\le a\le15/16\).**
Put \(s=1-a\in[1/16,1/2]\).
From (116), \(J(a,b)\ge-96s\).
Since \(H=s(3-4s)^2\ge s\),

\[
H+J/n\ge s(1-96/n)\ge\frac1{16}(1-96/n)
\ge\frac{18}{n}\quad(n\ge384).
\]

Again (114) suffices.

**Lower bound, \(15/16\le a<1\).**
Now \(2/n\le s=1-a\le1/16\), because a nonidentity permutation moves at least two vertices. Equations (113), (116) yield

\[
H+J/n\ge
(9-96/n)s-24s^2.
\]

The right side is a concave quadratic on \([2/n,1/16]\), so its minimum lies at an endpoint. At \(s=2/n\) it equals \(18/n-288/n^2\). At \(s=1/16\) it equals \(15/32-6/n\), which is at least \(18/n-288/n^2\) for \(n\ge2048\). Use (114) to complete (117).

Theorem 18 now bounds the sharp coefficient by the **oscillation** of any central orbital dual function. Since \(h_n(e)=1\), (117) gives the explicit upper bound (109).

### 22.2. Matching rational probability constructions in all four congruence classes

For the reverse bound, write \(n=4m+r\) with \(0\le r\le3\), and let \(m\) be sufficiently large. Consider the following **five concrete conjugacy classes** of \(S_n\):

| \(r\) | \(K\) | \(H\) | \(E\) |
|:---:|:---|:---|:---|
|0| \((m+2)1^{3m-2}\) | \(2^{2m}\) | \(3^{m+1}1^{m-3}\) |
|1| \((m+2)1^{3m-1}\) | \(3\,2^{2m-1}\) | \(3^{m+1}1^{m-2}\) |
|2| \((m+3)1^{3m-1}\) | \(2^{2m+1}\) | \(4\,3^m1^{m-2}\) |
|3| \((m+3)1^{3m}\) | \(3\,2^{2m}\) | \(5\,3^m1^{m-2}\) |

Together with \(I=1^n\) (identity) and \(T=2\,1^{n-2}\), define *unknown rational probability weights*
\(p_I,p_K,p_H,q_T,q_E\) uniquely by the five linear equations

\[
\begin{aligned}
p_I+p_K+p_H&=1,\qquad q_T+q_E=1,\\
p_I F_j(I)+p_KF_j(K)+p_HF_j(H)
&=q_TF_j(T)+q_EF_j(E),\quad j=0,1,2.
\tag{118}
\end{aligned}
\]

The entries \(F_j\) are the explicit integer polynomials (99)–(100), so (118) is a **completely specified \(5\times5\) rational linear system**. It requires no optimization and determines exact rational numbers for every sufficiently large integer \(m\).

Elementary determinant expansion of (118), for *each* of the four residues \(r\), yields the same leading term

\[
\det A_r(m)=-192m^9+O(m^8), \tag{119}
\]

so the system is invertible for all sufficiently large \(m\). Cramer's rule, again applied to the displayed five columns, gives the uniform leading expansions

\[
\begin{aligned}
p_I&=1-\frac{9}{2m}+O(m^{-2}),\\
p_K&=\frac4m+O(m^{-2}),&
p_H&=\frac1{2m}+O(m^{-2}),\\
q_E&=\frac4{3m}+O(m^{-2}),&
q_T&=1-\frac4{3m}+O(m^{-2}).
\tag{120}
\end{aligned}
\]

The determinant identities and every limit in (119)–(120) can be replayed by *exact symbolic arithmetic*; an independent script is given in
\(\texttt{code/check_three_subset_asymptotic_algebra.py}\).
The leading coefficients in (120) ensure **all five weights are strictly positive for all sufficiently large \(m\)**, and their exact normalizations and orbital moments are already built into (118).

Define conjugation-invariant probability measures

\[
P_n=p_I U_I+p_KU_K+p_HU_H,\qquad
Q_n=q_TU_T+q_EU_E, \tag{121}
\]

where \(U_\mathcal C\) denotes the uniform distribution on a conjugacy class. Their supports are disjoint for sufficiently large \(m\). Because the action on ordered triples has exactly the four orbitals determined by their intersection sizes, (118) implies that \(P_n,Q_n\) have the same **complete triple-image marginals**. Thus the exact signed perturbation
\(u_{S_n}+\delta(P_n-Q_n)\) is a probability law for every sufficiently small rational \(\delta>0\), with TV distance \(\delta\) and atom increase \(p_I\delta\).

The general orbital theorem therefore gives

\[
C_n^{(3)}\ge p_I
=1-\frac{9}{2m}+O(m^{-2})
=1-\frac{18}{n}+O(n^{-2}),
\tag{122}
\]

uniformly over all four residues modulo four.

### 22.3. Sharp asymptotic completion

Combine (122) with (109), valid for all \(n\ge2048\). The two bounds match at order \(1/n\), giving (108) with an error \(O(n^{-2})\) and the **exact first-order constant \(18\)**.

The asymptotic theorem is logically independent of the fixed \(n\le120\) table. Its proof consists of a universal orbital dual, an exact polynomial expansion and global real-variable inequalities, and four rational primal families with directly checkable full moment equations. It does **not** prove that those particular families are exactly optimal at every sufficiently large finite degree; proving eventual exact support stabilization and explicit parity-wise formulas remains open.


## 23. General \(k\)-subset orbital Bernstein limits and a Chebyshev research direction

The first-order constants \(2,8,18\) in the one-, two-, and three-subset actions have a common structure. The orbital basis of **every fixed subset rank** converges to the Bernstein polynomial basis, while the explicit duals in ranks \(1,2,3\) converge to *shifted Chebyshev polynomials*. The first observation is a rigorously proved general theorem. Its extension to a sharp all-\(k\) atom-TV asymptotic remains a conjecture.

Let \(1\le k\le n\), let \(\Omega_{n,k}=\binom{[n]}k\), and define

\[
F_j^{(k)}(g)
=\#\{E\in\Omega_{n,k}:|E\cap g(E)|=j\}
\quad(0\le j\le k).
\]

Write \(x(g)\) for the number of fixed vertices and \(a(g)=x(g)/n\). Define the Bernstein basis
\(B_{j,k}(a)=\binom kj a^j(1-a)^{k-j}\).

**Theorem 23 (uniform Bernstein orbital approximation).** For every \(n\ge\max(k,2)\), every permutation \(g\in S_n\), and every \(0\le j\le k\),

\[
\boxed{
\left|\frac{F_j^{(k)}(g)}{\binom nk}
       -B_{j,k}(a(g))\right|
\le\frac{k(k-1)}{n-1}+\frac{k(k-1)}{2n}.
} \tag{123}
\]

Indeed the **total variation distance between the entire two distributions** on \(j=0,\ldots,k\) satisfies the same bound. Consequently for every fixed \(k\), the \(k+1\) normalized orbital statistics converge uniformly over \(g\in S_n\), at rate \(O_k(n^{-1})\), to the Bernstein basis of polynomials of degree at most \(k\).

**Proof.** Choose a uniformly random \(k\)-subset \(E\), and let \(X=|E\cap g(E)|\). Let \(S\) be the fixed-vertex set of \(g\), with \(|S|=x\), and put \(Y=|E\cap S|\). Every fixed vertex in \(E\) also belongs to \(g(E)\), hence \(X\ge Y\). Any extra element \(v\in E\cap g(E)\setminus S\) requires the two **distinct** vertices \(v\) and \(g^{-1}(v)\) both to belong to \(E\). For each moved vertex \(v\), the probability of this pair event is exactly \(k(k-1)/(n(n-1))\). By the union bound,

\[
\mathbb P(X\ne Y)
\le (n-x)\frac{k(k-1)}{n(n-1)}
\le\frac{k(k-1)}{n-1}. \tag{124}
\]

The variable \(Y\) has the hypergeometric distribution of the number of successes in \(k\) draws without replacement from a population of \(n\) with \(x\) successes. Draw instead \(k\) vertices independently and uniformly with replacement, and let \(Z\sim\operatorname{Binomial}(k,x/n)\) count successes. The distribution of the ordered independent sample **conditioned on distinctness** is exactly that of ordered sampling without replacement. The probability of a collision is at most \(\binom k2/n=k(k-1)/(2n)\); thus the total variation distance between \(Y\) and \(Z\) is at most this probability. By the coupling characterization and the triangle inequality,

\[
d_{\mathrm{TV}}\bigl(\mathcal L(X),\mathcal L(Z)\bigr)
\le\mathbb P(X\ne Y)+
d_{\mathrm{TV}}\bigl(\mathcal L(Y),\mathcal L(Z)\bigr),
\]

which is (123) for the full distributions and hence for each coordinate. QED.

**Proposition 24 (Chebyshev limiting duals in ranks \(1,2,3\)).** Let \(T_k\) denote the Chebyshev polynomial of the first kind, \(T_k(\cos\theta)=\cos(k\theta)\). In each of the already proved ranks \(k=1,2,3\), the leading nonidentity orbital dual polynomial of the sharp or sharp-order certificates is

\[
\boxed{H_k(a)=\frac{1-T_k(2a-1)}2,}
\]

namely

\[
H_1(a)=1-a,\qquad
H_2(a)=4a(1-a),\qquad
H_3(a)=(1-a)(4a-1)^2.
\tag{125}
\]

All satisfy \(0\le H_k(a)\le1\) for \(0\le a\le1\), \(H_k(1)=0\), and the endpoint derivative identity

\[
-H_k'(1)=k^2. \tag{126}
\]

**Proof.** The polynomial identities follow by substituting \(T_1(t)=t\), \(T_2(t)=2t^2-1\), and \(T_3(t)=4t^3-3t\). For \(k=1\), the fixed-point dual \(h(g)=\mathbf1_{\{g=e\}}+(n-x(g))/n\) has nonidentity profile \(H_1(x/n)\) exactly. For \(k=2\), the exact duals (76) and (81) have the common leading nonidentity profile \(4a(1-a)\): substitute the leading terms of (68) with \(x=an\) and \(y=O(n)\). For \(k=3\), equation (113) provides the exact leading polynomial \(H_3\). The range and derivative statements follow from \(|T_k(t)|\le1\) on \([-1,1]\) and \(T_k'(1)=k^2\). QED.

This exhibits why the exact first-order constants are

\[
\begin{array}{c|c}
k & \displaystyle\lim_{n\to\infty}n(1-C_n^{(k)})\\ \hline
1&2\quad\text{(Theorem 15)},\\
2&8\quad\text{(Theorem 17)},\\
3&18\quad\text{(Theorem 22)}.
\end{array}
\tag{127}
\]

A nonidentity vertex permutation must move at least two vertices, so the closest possible fixed-point fraction to \(1\) is \(1-2/n\). For a shifted Chebyshev dual, the endpoint loss is therefore \(2k^2/n+O_k(n^{-2})\). This interpretation is exact for the three established ranks; it motivates but **does not prove** the following general question.

**Historical conjecture (now proved in Theorem 25).** For every fixed \(k\ge4\), the optimal coefficient for \(S_n\) acting on its \(k\)-subsets satisfies

\[
C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2})
\qquad(n\to\infty). \tag{128}
\]

A viable proof must address **both sides**: construct a uniformly valid orbital dual with the appropriate subleading corrections, and match it by genuine nonnegative class measures with exactly equal \(k\)-subset image marginals. Theorem 23 alone proves only Bernstein convergence; it does not control the \(1/n\) coefficient or justify a Chebyshev optimizer. Numerical LP output at fixed degrees also cannot establish (128). **Status update:** this was the research conjecture at the time of Section 23; the full fixed-rank statement is now **proved** in Theorem 25, Section 24. The finite-n exact classification remains open.


## 24. Resolution of the fixed-rank Chebyshev atom-modulus conjecture

The conjecture in Section 23 admits a **complete affirmative proof for every fixed subset rank**. The argument has three independent parts: a uniform first-order orbital expansion, a corrected Chebyshev dual giving an upper bound, and genuine positive probability measures at Chebyshev–Lobatto nodes giving the matching lower bound. None of these uses the finite LP computations as a proof premise.

For fixed \(k\ge1\), denote by \(C_n^{(k)}\) the optimal single-atom versus total-variation coefficient for the natural \(S_n\)-action on \(\binom{[n]}k\), under preservation of every one-point subset-image marginal, as defined by Theorem 18.

**Theorem 25 (sharp universal fixed-rank law).** For **every fixed integer \(k\ge1\)**,

\[
\boxed{ C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2})\qquad(n\to\infty). } \tag{129}
\]

In particular,

\[
\boxed{\lim_{n\to\infty}n(1-C_n^{(k)})=2k^2.} \tag{130}
\]

Both sides of the asymptotic bound follow from independently specified, rigorous constructions. The primal measures have **exactly** matching subset-image marginals, not merely asymptotically matching ones.

### 24.1. A uniform first-order orbital expansion

For \(n\ge2k\), \(g\in S_n\), let \(x\) and \(y\) be its numbers of 1-cycles and 2-cycles, and set \(a=x/n\), \(b=y/n\). Necessarily \(0\le a\le1\) and \(0\le b\le(1-a)/2\). Choose uniformly \(E\in\binom{[n]}k\), put \(X=|E\cap g(E)|\), and write

\[
G_{n,g}(t)=\mathbb E[t^X],\qquad B(t)=1-a+at.
\]

**Lemma 26 (uniform orbital generating expansion).** For each fixed \(k\ge2\),

\[
\begin{aligned}
G_{n,g}(t)
={}&B(t)^k+\frac{k(k-1)}{n}B(t)^{k-2}
\Big[(1-a)(t-1)\\
&\hspace{56pt}+\big(b-\tfrac12a(1-a)\big)(t-1)^2\Big]
+O_k(n^{-2}). \tag{131}
\end{aligned}
\]

The remainder is **uniform in every permutation** \(g\in S_n\), and is bounded coefficientwise as a polynomial in \(t\), with a constant depending only on fixed \(k\). For \(k=1\), \(G_{n,g}(t)=1-a+at\) exactly.

**Proof.** Let \(S\) be the fixed-vertex set, and put \(Y=|E\cap S|\). This is hypergeometric, and

\[
\mathbb E(1+u)^Y
=\sum_{j=0}^k\binom kj\frac{(x)_j}{(n)_j}u^j.
\]

For fixed \(j\le k\) and all integers \(0\le x\le n\), the falling-factorial ratio has the uniform expansion

\[
\frac{(x)_j}{(n)_j}
=a^j-\frac{\binom j2}{n}a^{j-1}(1-a)+O_k(n^{-2});
\]

the apparent \(a^{-1}\) singularity does not occur because \(j\ge2\) in the correction. This follows by multiplying out the fixed-degree falling factorial polynomials and using \((n)_j=n^j(1-\binom j2/n+O_k(n^{-2}))\) for \(n\ge2k\). Summing over \(j\) gives

\[
\mathbb E[t^Y]
=B(t)^k-\frac{k(k-1)}{2n}a(1-a)(t-1)^2B(t)^{k-2}
+O_k(n^{-2}). \tag{132}
\]

Now \(X-Y\) counts moved vertices \(v\in E\) for which \(g^{-1}(v)\in E\). In cycles of length at least three, the directed edges \(g^{-1}v\to v\) give \(L=n-x-2y\) *distinct unordered selected-pair events*, each of which adds **one** to \(X-Y\). A transposition gives only one unordered pair event, but when selected, contributes **two** to \(X-Y\). There are \(y\) such events. Each individual pair is contained in \(E\) with probability

\[
\frac{k(k-1)}{n(n-1)}=\frac{k(k-1)}{n^2}+O_k(n^{-3}).
\]

Distinct event edges form a graph of maximum vertex degree two. There are \(O(n)\) pairs of event edges that share a vertex; selecting their three distinct endpoints has probability \(O_k(n^{-3})\). There are \(O(n^2)\) disjoint event-edge pairs; selecting their four endpoints has probability \(O_k(n^{-4})\). Therefore the probability of **two or more distinct pair events** is \(O_k(n^{-2})\), uniformly in \(g\).

Conditioned on a particular selected pair, both its vertices are moved, and the remaining \(k-2\) chosen vertices form a uniform \((k-2)\)-subset of the other \(n-2\) vertices. Their fixed-point count has generating polynomial \(B(t)^{k-2}+O_k(n^{-1})\) coefficientwise, by the same finite hypergeometric approximation. Discarding the multiple-event configurations, whose contribution is coefficientwise \(O_k(n^{-2})\), gives

\[
\begin{aligned}
\mathbb E[t^X]-\mathbb E[t^Y]
={}&\frac{k(k-1)}{n}B(t)^{k-2}
\big[(1-a-2b)(t-1)+b(t^2-1)\big]\\
&+O_k(n^{-2})\\
={}&\frac{k(k-1)}{n}B(t)^{k-2}
\big[(1-a)(t-1)+b(t-1)^2\big]+O_k(n^{-2}). \tag{133}
\end{aligned}
\]

The coefficientwise estimates are legitimate because \(k\) is fixed, \(X\le k\), and any sum of selected-edge indicators on a \(k\)-set is bounded by \(k\). Combining (132) and (133) proves (131). QED.

Every polynomial \(P(a)\) of degree at most \(k\) has a unique Bernstein representation

\[
P(a)=\sum_{j=0}^k\beta_j\binom kj a^j(1-a)^{k-j}.
\]

Define

\[
\mathcal L_{n,g}(P)=
\sum_{j=0}^k\beta_j\frac{F_j^{(k)}(g)}{\binom nk}.
\]

**Corollary 27 (universal first correction).** For each fixed \(k\ge2\),

\[
\mathcal L_{n,g}(P)=P(a)+\frac{J_P(a,b)}n+O_{k,P}(n^{-2}), \tag{134}
\]

uniformly in \(g\), where

\[
\boxed{J_P(a,b)=(k-1)(1-a)P'(a)
+\left(b-\frac32a(1-a)\right)P''(a).} \tag{135}
\]

**Proof.** Apply the coefficient functional \(t^j\mapsto\beta_j\) to (131). The Bernstein differentiation identities give

\[
\sum_j\beta_j[t^j]\big((t-1)^2B(t)^{k-2}\big)
=\frac{P''(a)}{k(k-1)}
\]

and

\[
\sum_j\beta_j[t^j]\big((t-1)B(t)^{k-2}\big)
=\frac{P'(a)}k-\frac{aP''(a)}{k(k-1)}.
\]

The asserted expression (135) follows directly, retaining the uniform coefficientwise error. QED.


### 24.2. An explicitly corrected Chebyshev dual for every rank

For each integer \(k\ge2\), let

\[
H(a)=\frac{1-T_k(2a-1)}2,\qquad
a_j=\frac{1+\cos(j\pi/k)}2\quad(j=0,\ldots,k), \tag{136}
\]

where \(T_k\) is the first Chebyshev polynomial. Then

\[
1=a_0>a_1>\cdots>a_k=0,\qquad
H(a_j)=\begin{cases}0,&j\text{ even},\\1,&j\text{ odd},\end{cases}
\qquad H'(1)=-k^2. \tag{137}
\]

All interior nodes \(a_1,\ldots,a_{k-1}\) are nondegenerate extrema: \(H''(a_j)<0\) at odd \(j\) and \(H''(a_j)>0\) at even \(j\). At the left endpoint,

\[
H'(0)=(-1)^k k^2,\qquad
\operatorname{sgn}H''(0)=(-1)^{k+1} \quad(k\ge2). \tag{138}
\]

Put \(\rho=2k^2\). Let \(J_H\) be the correction (135) with \(P=H\). Prescribe

\[
b_j=0\quad(1\le j<k),\qquad
b_k=\tfrac12,\qquad
\tau_j=\begin{cases}0,&j\text{ odd},\\\rho,&j\text{ even}.\end{cases} \tag{139}
\]

There is a **unique polynomial \(R\) of degree at most \(k\)** satisfying

\[
R(1)=0,\qquad
R(a_j)=\tau_j-J_H(a_j,b_j)
\quad(1\le j\le k), \tag{140}
\]

because these specify its values at \(k+1\) distinct nodes. Define

\[
J(a,b)=J_H(a,b)+R(a).
\tag{141}
\]

The first-correction contacts are therefore

\[
J(a_j,0)=\tau_j\ (1\le j<k),\quad
J(0,\tfrac12)=\tau_k,\quad
J(1,0)=0,\quad
\partial_bJ(a,b)=H''(a). \tag{142}
\]

Write the degree-\(k\) Bernstein coefficients of \(H,R\) as \(\beta_0,\ldots,\beta_k\) and \(\gamma_0,\ldots,\gamma_k\). Since \(H(1)=R(1)=0\), one has \(\beta_k=\gamma_k=0\). Define the **finite, explicit orbital dual function**

\[
h_{n,k}(g)=\mathbf1_{\{g=e\}}
+\sum_{j=0}^{k-1}
\left(\beta_j+\frac{\gamma_j}{n}\right)
\frac{F_j^{(k)}(g)}{\binom nk}. \tag{143}
\]

At the identity \(h_{n,k}(e)=1\) **exactly**. By Corollary 27, for every nonidentity permutation, with \(a=x(g)/n\), \(b=y(g)/n\),

\[
h_{n,k}(g)=H(a)+\frac{J(a,b)}n+O_k(n^{-2})
\tag{144}
\]

uniformly over the entire feasible region \(0\le a\le1-2/n\), \(0\le b\le(1-a)/2\).

**Lemma 28 (uniform corrected-dual bound).** For each fixed \(k\ge2\), there is \(D_k<\infty\) such that for all sufficiently large \(n\) and all nonidentity \(g\in S_n\),

\[
\boxed{
\frac{\rho}{n}-\frac{D_k}{n^2}
\le h_{n,k}(g)\le
1+\frac{D_k}{n^2}.} \tag{145}
\]

**Proof.** By (144), it suffices to prove the claim for \(H(a)+J(a,b)/n\); the uniform remainder can be absorbed into \(D_k\). We cover the compact feasible parameter region by neighborhoods of the finitely many extrema of \(H\) and their complement. Every constant below may depend on fixed \(k\), but not on \(n,a,b\).

**Interior maxima.** For odd \(1\le j<k\), choose a neighborhood of \(a_j\) on which \(H''<0\) and \(H(a)\le1-c(a-a_j)^2\) for some \(c>0\). By (142), \(J(a,b)\le J(a,0)\) for \(b\ge0\). Since \(J(a_j,0)=0\), smoothness gives \(J(a,0)\le M|a-a_j|\). Completing the square,

\[
H(a)+J(a,b)/n
\le1-c(a-a_j)^2+\frac{M|a-a_j|}{n}
\le1+\frac{M^2}{4cn^2}.
\]

The lower bound is automatic nearby because \(H\) stays bounded above zero.

**Interior minima.** For even \(1\le j<k\), choose a neighborhood on which \(H''>0\) and \(H(a)\ge c(a-a_j)^2\). Then \(J(a,b)\ge J(a,0)\ge\rho-M|a-a_j|\), by (142) and the contact \(J(a_j,0)=\rho\). Thus

\[
H(a)+J(a,b)/n
\ge c(a-a_j)^2+\frac{\rho-M|a-a_j|}{n}
\ge\frac{\rho}{n}-\frac{M^2}{4cn^2}.
\]

The upper bound is automatic because \(H\) stays away from one.

**Endpoint \(a=0\).** If \(k\) is odd, \(H(0)=1\), \(H'(0)=-k^2\), \(H''(0)>0\). Near zero, \(J(a,b)\le J(a,(1-a)/2)\), because \(b\le(1-a)/2\) and the slope in \(b\) is positive. The latter function vanishes at \(a=0\) by (142), so is at most \(Ma\); meanwhile \(H(a)\le1-ca\). Hence the upper bound holds for large \(n\), with the lower bound automatic.

If \(k\) is even, \(H(0)=0\), \(H'(0)=k^2\), \(H''(0)<0\). Then \(J(a,b)\ge J(a,(1-a)/2)\ge\rho-Ma\) near zero. Since \(H(a)\ge ca\), the lower bound holds for large \(n\), while the upper bound is automatic.

**Endpoint \(a=1\).** Here \(H(1)=0\), \(H'(1)=-k^2\), and \(J(1,0)=0\). Put \(s=1-a\), so \(b\le s/2\), and choose \(M\) large enough that for all sufficiently small \(s\ge0\),

\[
H(1-s)\ge k^2s-Ms^2,\qquad
J(1-s,b)\ge-Ms.
\]

For nonidentity permutations \(s\ge2/n\). Choose a fixed small neighborhood and then \(n\) large enough that \(f_n(s)=k^2s-Ms^2-Ms/n\) is **increasing** there. Thus

\[
H(a)+J(a,b)/n\ge f_n(2/n)
=\frac{2k^2}{n}+O_k(n^{-2}).
\]

The upper bound is automatic near this zero of \(H\).

**Compact complement.** Away from all these finitely many nodes, continuity gives a constant \(\eta>0\) with \(\eta\le H(a)\le1-\eta\). The polynomial \(J\) is bounded uniformly on the compact feasible triangle. Both desired inequalities hold with fixed slack for all large \(n\).

Together these neighborhoods cover all \(g\ne e\), proving (145). QED.

By Theorem 18, the sharp coefficient is no greater than the **oscillation** of any dual function consisting of the identity indicator plus a linear combination of orbital statistics. Since \(h_{n,k}(e)=1\), (145) implies

\[
\boxed{C_n^{(k)}\le1-\frac{2k^2}{n}+O_k(n^{-2}).} \tag{146}
\]

The case \(k=1\) is already given exactly by Theorem 15: \(C_n^{(1)}=(n-2)/n\).


### 24.3. Matching exact positive probability measures

We now obtain the reverse inequality in (129), for **every sufficiently large \(n\)** and fixed \(k\). Crucially, this constructs genuinely nonnegative probability measures whose subset-image marginals agree **exactly**, not just in an asymptotic expansion.

Let \(a_0=1>a_1>\cdots>a_k=0\) be the nodes (136). For each \(1\le j\le k\), choose an integer \(x_j(n)\) with

\[
|x_j(n)-na_j|\le1.
\]

Let \(g_{j,n}\in S_n\) have exactly \(x_j(n)\) fixed vertices and one additional cycle of length \(n-x_j(n)\). Because \(k\) is fixed and every \(a_j<1\), for sufficiently large \(n\) all these long cycles have length at least \(k+1\). The \(k\) cycle types are mutually distinct, nonidentity and not transpositions. Let \(I_n\) denote the identity, and \(T_n\) a transposition.

Define the **rational orbital vector** in \(k\) coordinates

\[
V_n(g)=
\left(
\frac{F_0^{(k)}(g)}{\binom nk},\ldots,
\frac{F_{k-1}^{(k)}(g)}{\binom nk}
\right). \tag{147}
\]

Thus \(V_n(I_n)=0\). Form the \(k\times k\) matrix \(D_n\) with columns

\[
D_{n,j}=
\begin{cases}
V_n(g_{j,n})-V_n(I_n),&j\text{ odd},\\
V_n(T_n)-V_n(g_{j,n}),&j\text{ even},
\end{cases}
\quad(1\le j\le k), \tag{148}
\]

and consider the **specified rational linear system**

\[
D_n w_n=V_n(T_n)-V_n(I_n),\qquad
w_n=(w_{1,n},\ldots,w_{k,n})^T. \tag{149}
\]

We prove that \(D_n\) is invertible, that **all** weights \(w_{j,n}\) are strictly positive, and that

\[
\sum_{j\ \mathrm{odd}}w_{j,n}
=\frac{2k^2}{n}+O_k(n^{-2}) \tag{150}
\]

for all sufficiently large \(n\).

Write \(B_j(a)=\binom kj a^j(1-a)^{k-j}\) and
\(\mathbf B(a)=(B_0(a),\ldots,B_{k-1}(a))\). The uniform Bernstein approximation in Theorem 23, together with the rounding of \(x_j(n)\), gives

\[
V_n(g_{j,n})=\mathbf B(a_j)+O_k(n^{-1}).
\tag{151}
\]

The exact transposition count is

\[
\Pr_{E\in\binom{[n]}k}(|E\cap T_n(E)|=k-1)
=\frac{2\binom{n-2}{k-1}}{\binom nk}
=\frac{2k(n-k)}{n(n-1)}
=\frac{2k}{n}+O_k(n^{-2}),
\]

and every other changed-image orbital has probability zero. Equivalently,

\[
V_n(T_n)-V_n(I_n)
=-\frac2n\mathbf B'(1)+O_k(n^{-2}). \tag{152}
\]

The limiting matrix \(D_\infty\) has columns \(+\mathbf B(a_j)\) at odd \(j\) and \(-\mathbf B(a_j)\) at even \(j\). It is invertible: every \(B_i(a)\) with \(0\le i<k\) contains the factor \((1-a)\). Dividing the evaluation matrix at the \(k\) distinct points \(a_1,\ldots,a_k<1\) by these nonzero row factors leaves an evaluation matrix for a basis of polynomials of degree at most \(k-1\), which is invertible by the Vandermonde theorem. Therefore \(D_n\) is invertible for all large \(n\), and its inverses are uniformly bounded in \(n\).

For each \(j=0,\ldots,k\), let \(\ell_j(a)\) be the degree-\(k\) **Lagrange cardinal polynomial** for the nodes \(a_0,\ldots,a_k\). Thus for every polynomial \(P\) of degree at most \(k\),

\[
P'(1)=\sum_{j=0}^k\ell_j'(1)P(a_j). \tag{153}
\]

For \(j\ge1\) the sign of \(\ell_j'(1)\) is \((-1)^j\): indeed

\[
\ell_j'(1)=
\frac{\prod_{i\notin\{0,j\}}(1-a_i)}
{\prod_{i\ne j}(a_j-a_i)},
\]

and exactly \(j\) denominator factors are negative, since the nodes are strictly decreasing. Put

\[
u_j=2|\ell_j'(1)|>0,\qquad1\le j\le k. \tag{154}
\]

Applying (153) to \(B_0,\ldots,B_{k-1}\), all of which vanish at \(a_0=1\), shows that \(u\) solves the **limiting** equation

\[
D_\infty u=-2\mathbf B'(1).
\]

Now \(D_n=D_\infty+O_k(n^{-1})\) from (151) and \(n[V_n(T_n)-V_n(I_n)]=-2\mathbf B'(1)+O_k(n^{-1})\) from (152). Uniform boundedness of \(D_n^{-1}\) therefore gives

\[
\boxed{
w_{j,n}=\frac{u_j}{n}+O_k(n^{-2})\quad(1\le j\le k).}
\tag{155}
\]

Since every \(u_j>0\), this proves **strict positivity of the exact rational solution** \(w_{j,n}\) for sufficiently large \(n\).

Finally, the Chebyshev polynomial \(H\) has \(H(a_j)=1\) for odd \(j\) and \(0\) for even \(j\), while \(H(1)=0\). Applying (153) to \(H\) and using \(H'(1)=-k^2\),

\[
\sum_{j\ \mathrm{odd}}u_j
=-2\sum_{j\ \mathrm{odd}}\ell_j'(1)
=-2H'(1)=2k^2. \tag{156}
\]

Equation (150) follows.

Now define actual **central probability laws**

\[
\begin{aligned}
P_n={}&
\left(1-\sum_{j\ \mathrm{odd}}w_{j,n}\right)U_{\{I_n\}}
+\sum_{j\ \mathrm{odd}}w_{j,n}U_{[g_{j,n}]},\\
Q_n={}&
\left(1-\sum_{j\ \mathrm{even}}w_{j,n}\right)U_{[T_n]}
+\sum_{j\ \mathrm{even}}w_{j,n}U_{[g_{j,n}]},
\end{aligned}
\tag{157}
\]

where \(U_{[g]}\) is uniform probability on the conjugacy class of \(g\). By (155), every coefficient is positive for sufficiently large \(n\); the two supports are disjoint.

Equation (149) is **exact** and says that all \(k\) orbital coordinates of \(P_n\) and \(Q_n\) match. The final orbital coordinate matches automatically because the \(k+1\) normalized coordinates sum to one. Since the measures are conjugation-invariant, equality of all orbital moments is equivalent to equality of **every** \(k\)-subset one-point image marginal (Theorem 18).

For every sufficiently small rational \(\delta>0\), the signed perturbation
\(\nu_\delta=u_{S_n}+\delta(P_n-Q_n)\) is therefore a nonnegative probability measure with **exact uniform subset-image marginals**, total variation exactly \(\delta\), and

\[
\nu_\delta(I_n)-\frac1{n!}
=\delta P_n(I_n)
=\delta\left(1-\frac{2k^2}{n}+O_k(n^{-2})\right).
\]

Consequently Theorem 18 supplies the reverse estimate

\[
\boxed{C_n^{(k)}\ge1-\frac{2k^2}{n}+O_k(n^{-2}).} \tag{158}
\]

Together with the matching dual bound (146), this proves Theorem 25 for every fixed \(k\ge2\). For \(k=1\), the already proved exact identity \(C_n^{(1)}=(n-2)/n\) finishes the statement. **Theorem 25 is completely proved.** QED.

### 24.4. Exact four-subset example and the remaining finite-degree problem

In the first previously unresolved rank \(k=4\),

\[
H(a)=16a(1-a)(2a-1)^2,
\]

and the interpolation system (140) yields the explicitly checkable **integer-coefficient correction**

\[
R(a)=16(a-1)(200a^3-232a^2+63a-4). \tag{159}
\]

Their degree-four Bernstein coefficient vectors are

\[
(\beta_0,\ldots,\beta_4)=(0,4,-16/3,4,0),
\]

\[
(\gamma_0,\ldots,\gamma_4)=(64,-204,944/3,-108,0).
\tag{160}
\]

The published exact checker in code/check_k4_chebyshev_dual.py independently verifies the first-order orbital expansion, every Chebyshev contact, and the Bernstein coefficients using algebraic arithmetic in \(\mathbb Q(\sqrt2)\); it additionally constructs **strictly positive rational primal weights** at several larger finite degrees and checks the moment equations exactly.

**Precisely what is now closed.** Equation (129) settles the sharp first-order asymptotic coefficient for **every fixed \(k\)**, not merely \(k=1,2,3\), and proves the higher-rank conjecture previously stated in Section 23. It does **not** determine the individual exact value of \(C_n^{(k)}\) for arbitrary finite \(n,k\); nor does the qualitative proof specify a common explicit threshold in \(n\) beyond which all primal weights are positive. Those stronger effective/finite problems remain open, and no novelty or external-peer-review claim is implied.


### 24.5. Explicit asymptotic masses at every Chebyshev node

The construction in (149)–(157) admits closed, positive leading weights, not merely an existence argument.

**Corollary 29 (universal Chebyshev–Lobatto mass formula).** In Theorem 25, define
\(c_j=1\) for \(1\le j<k\) and \(c_k=2\). For the nodes
\(a_j=(1+\cos(j\pi/k))/2\), the unique asymptotic solution to (149) has

\[
\boxed{
w_{j,n}=\frac{1}{n}
\frac{4}{c_j(1-a_j)}+O_k(n^{-2})
=\frac1n\frac{8}{c_j[1-\cos(j\pi/k)]}
+O_k(n^{-2})
\quad(1\le j\le k).} \tag{161}
\]

Consequently the constructed central primal measures satisfy

\[
\boxed{
P_n(I_n)=1-\frac{2k^2}{n}+O_k(n^{-2}),\qquad
Q_n([T_n])=1-\frac{2(k^2-1)}{3n}+O_k(n^{-2}),}
\tag{162}
\]

where \(Q_n([T_n])\) denotes the total mass of the transposition conjugacy class. In particular, \(w_{k,n}=2/n+O_k(n^{-2})\) for every \(k\), and the entire leading mass profile is **explicit**.

**Proof.** For Chebyshev–Lobatto nodes in decreasing order, the Lagrange barycentric weights are proportional to \((-1)^j/c_j\), with both endpoint denominators equal to \(2\) and all interior denominators equal to \(1\). The derivative formula for a Lagrange cardinal polynomial at \(a_0=1\) is therefore

\[
\ell_j'(1)=\frac{(-1)^j\,2}{c_j(1-a_j)},\qquad j\ge1.
\]

Combining with (154)–(155) gives (161), including the endpoint mass \(w_{k,n}=2/n+O_k(n^{-2})\).

The odd-weight identity is already (156). For the even weights, interpolation of the complementary polynomial \(1-H\) gives

\[
\sum_{\substack{j\ge2\\j\ \mathrm{even}}}\ell_j'(1)
=(1-H)'(1)-\ell_0'(1)=k^2-\ell_0'(1).
\]

But
\(\ell_0'(1)=\sum_{j=1}^k(1-a_j)^{-1}=(2k^2+1)/3\).
For completeness, the node polynomial for \(a_1,\ldots,a_k\), under \(t=2a-1\), is proportional to \((t+1)U_{k-1}(t)\), where \(U_{k-1}\) is the Chebyshev polynomial of the second kind. Logarithmic differentiation at \(t=1\), using \(U_{k-1}(1)=k\) and \(U_{k-1}'(1)=k(k^2-1)/3\), gives exactly
\(\ell_0'(1)=1+2(k^2-1)/3=(2k^2+1)/3\).
Hence

\[
\sum_{j\ \mathrm{even}}u_j
=2\left(k^2-\frac{2k^2+1}{3}\right)
=\frac{2(k^2-1)}3,
\]

which, with (155), yields the second formula in (162). QED.

The weights in (161) are the *leading asymptotics* of strictly positive, **exactly rational** solutions of (149). They are not claimed to be the exact finite-\(n\) weights at all \(n\), and not every leading coefficient is rational.


## 25. An exact cycle-index and transfer-matrix compression theorem for every rank

The earlier rank-three compression theorem (Theorem 20) is a special case of a general exact identity. For **every** fixed subset size \(k\), the full orbital vector of a permutation depends only on its cycle counts of lengths **at most \(k\)**. This observation is stronger than the first-order Bernstein approximation: it is an identity over integers for **every finite \(n\)** and provides an exact proof/certificate interface for higher-rank finite classifications.

Write \(c_\ell(g)\) for the number of length-\(\ell\) cycles of \(g\in S_n\). Let \(u,t\) be commuting formal variables and define the \(2\times2\) transfer matrix

\[
M(u,t)=\begin{pmatrix}1&u\\1&ut\end{pmatrix}. \tag{163}
\]

Let \(\lambda_+(u,t)\in\mathbb Q[t][[u]]\) be the unique formal-power-series root with constant coefficient \(1\) of

\[
\lambda^2-(1+ut)\lambda+u(t-1)=0.
\tag{164}
\]

Thus \(\lambda_+=1+u+(t-1)u^2+\cdots\). Define the **complete rank-\(k\) orbital polynomial**

\[
\mathcal F_{n,k,g}(t)
=\sum_{j=0}^k F_j^{(k)}(g)t^j.
\]

**Theorem 30 (exact all-rank cycle compression).** For every integer \(1\le k\le n\),

\[
\boxed{\displaystyle
\mathcal F_{n,k,g}(t)
=[u^k]\left\{
\lambda_+(u,t)^{\,n-\sum_{\ell=1}^k\ell c_\ell(g)}
\prod_{\ell=1}^k
\big(\operatorname{tr}M(u,t)^\ell\big)^{c_\ell(g)}
\right\}.} \tag{165}
\]

Only the coefficients through \(u^k\) of the formal power series are required. In particular, **if two permutations have the same \(c_1,\ldots,c_k\), then all their \(k\)-subset orbital statistics agree exactly**:

\[
c_\ell(g)=c_\ell(h)\ (1\le\ell\le k)
\quad\Longrightarrow\quad
F_j^{(k)}(g)=F_j^{(k)}(h)\ (0\le j\le k). \tag{166}
\]

Furthermore, nonnegative integers \(c_1,\ldots,c_k\) arise from a permutation of \(n\) points if and only if

\[
r=n-\sum_{\ell=1}^k\ell c_\ell\in\{0\}\cup\{k+1,k+2,\ldots\}. \tag{167}
\]

Consequently the general orbital primal-dual program of Theorem 18 can be compressed **without any loss in optimality** to at most \(O_k(n^k)\) short-cycle-count vectors, instead of enumerating every integer partition of \(n\). Every feasible vector has a canonical representative of cycle type \(1^{c_1}\cdots k^{c_k}r\) when \(r\ge k+1\), or \(1^{c_1}\cdots k^{c_k}\) when \(r=0\).

**Proof.** Restrict \(g\) to a cycle of length \(\ell\), written as the cyclic vertex list \(v_1,\ldots,v_\ell\). Choosing a subset of its vertices is equivalent to choosing a cyclic binary word \(\epsilon=(\epsilon_1,\ldots,\epsilon_\ell)\), where \(\epsilon_i=1\) means \(v_i\) is selected. Its contribution to the size of the selected set is \(\sum_i\epsilon_i\); its contribution to \(|E\cap g(E)|\) is \(\sum_i\epsilon_i\epsilon_{i+1}\), indices taken cyclically.

For a transition from current binary state \(r\in\{0,1\}\) to next state \(s\in\{0,1\}\), the matrix entry \(M_{rs}=u^s t^{rs}\) is exactly the weight for the next selected vertex and an adjacent selected pair. Consequently the partition function of the cycle is

\[
Z_\ell(u,t)
=\sum_{\epsilon\in\{0,1\}^\ell}
u^{\sum_i\epsilon_i}t^{\sum_i\epsilon_i\epsilon_{i+1}}
=\operatorname{tr}M(u,t)^\ell.
\]

Different permutation cycles contribute independently to the combinatorial subset generating function. Therefore the following identity is **exact** before truncation:

\[
\sum_{E\subseteq[n]}u^{|E|}t^{|E\cap g(E)|}
=\prod_{\ell=1}^nZ_\ell(u,t)^{c_\ell(g)}.
\tag{168}
\]

The determinant and trace of \(M\) are \(u(t-1)\) and \(1+ut\). Thus its characteristic roots are precisely \(\lambda_+\) from (164) and a second formal root \(\lambda_-=u(t-1)/\lambda_+\), satisfying \(\lambda_-\in u\mathbb Q[t][[u]]\). Cayley–Hamilton, or the standard two-root trace recurrence, gives

\[
Z_\ell=\lambda_+^\ell+\lambda_-^\ell.
\]

If \(\ell>k\), the polynomial/series \(\lambda_-^\ell\) is divisible by \(u^{\ell}\) and hence by \(u^{k+1}\). Therefore in the quotient ring modulo \(u^{k+1}\),

\[
Z_\ell\equiv\lambda_+^\ell\quad(\ell>k).
\]

Replace every factor corresponding to a long cycle in (168) by \(\lambda_+^\ell\) modulo \(u^{k+1}\), multiply, and extract the coefficient of \(u^k\). This proves (165).

The dependence on \(c_1,\ldots,c_k\) and their total contribution to \(n\) is now explicit, proving (166). All remaining cycles have lengths at least \(k+1\), so their sum is either zero or at least \(k+1\). Conversely any such remainder \(r\) is realized by one \(r\)-cycle, proving (167).

For the LP compression, Theorem 18 permits primal measures invariant under conjugation and dual functions in the orbital-count span. By (166), both their marginal constraints and their dual objective values are constant on any aggregate of conjugacy classes with the same short-cycle counts; all such types are realized by the canonical representatives. Aggregating class masses preserves feasibility and the identity atom, so the sharp LP optimum does not change. The number of nonnegative integer short-cycle vectors is at most \(\prod_{\ell=1}^k(1+\lfloor n/\ell\rfloor)=O_k(n^k)\). QED.

**Effective exact arithmetic.** This theorem is directly implementable without symbolic eigensolvers. The trace polynomials satisfy

\[
Z_0=2,\quad Z_1=1+ut,\quad
Z_\ell=(1+ut)Z_{\ell-1}-u(t-1)Z_{\ell-2}, \tag{169}
\]

while coefficients \(\lambda_+=\sum_{m\ge0}A_m(t)u^m\), \(A_0=1\), satisfy the integer-polynomial recurrence

\[
A_m=tA_{m-1}
-\sum_{i=1}^{m-1}A_iA_{m-i}
-\mathbf1_{\{m=1\}}(t-1)\quad(m\ge1).
\tag{170}
\]

Truncating every polynomial multiplication at \(u^{k+1}\) yields (165) using **integer arithmetic only**.

The independent public checker
code/check_all_k_orbital_compression.py
implements both recurrences using sparse integer dictionaries. It crosschecks the coefficients against an unrelated, direct \(k\)-subset enumeration on one representative of **every integer partition** for \(3\le n\le12\) and every \(1\le k\le\min(n,6)\). This finite check is supplementary; the transfer-matrix argument proves (165) for **all** \(n,k\).

**Next finite classification frontier.** Theorem 30 gives a rigorous compression layer for the exact \(k=4\) primal-dual problem, while Theorem 25 has already resolved its sharp asymptotic coefficient \(32\). It does not itself give the complete exact finite-\(n\) optimum at \(k=4\), which remains a separate classification problem.
