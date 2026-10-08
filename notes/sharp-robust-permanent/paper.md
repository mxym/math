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
