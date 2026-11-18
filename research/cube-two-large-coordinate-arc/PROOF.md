# A unique interior critical point on the two-large-coordinate arc of cube sections

Research draft with independent internal AI review, not external peer review or proof-assistant verification. No claim of priority. Two reproducible integer/rational verifiers accompany the analytic proof; see [certificate guide](CERTIFICATE.md) and [replay](CHECKS.md).

**Theorem.** For every integer $n\ge4$, among the normals
$$
 v=(a,a,b,\dots,b),\qquad 2a^2+(n-2)b^2=1,\quad 0<b<a,
$$
there is precisely one critical point of the central hyperplane section volume of the unit cube, with this coordinate ordering. It is the strict global minimum along the open arc (also smaller than both endpoint values) and a saddle on the sphere, the latter conclusion being due to Ambrus–Gárgyán. Its larger coordinate $a_n$ tends to $y_*/\sqrt{12+2y_*^2}\approx0.6401740$, where $y_*>0$ is the unique positive solution of
$$
 (12+y^2)(1-e^{-y^2/2})=6y\int_0^y e^{-u^2/2}\,du .
$$
The new point is uniqueness on the specified arc in all dimensions (and a limit), not existence of a saddle, already known in every dimension; the dimension-four classification was also already known. This addresses the unnumbered suspicion after Lemma 5.3/Table 3 of [Ambrus–Gárgyán](https://doi.org/10.1016/j.aim.2024.109524), **not** their broader Conjecture 1.3 or their separate question about three or more large coordinates.

## 1. A truncated first-moment equation

Put $m=n-2$, $x=2a/b$, so $2<x<\infty$. Use independent uniforms on $[-1,1]$ and let $S$ be the sum of $m$ of them. By slicing (and scaling the cube by 2), the section volume is twice the density at zero of the normalized linear form $v\cdot U$. The density of $(x/2)(U_1+U_2)$ at $s$ is $(x-|s|)_+/x^2$. Hence up to a fixed positive factor the arc functional is
$$
 f(x)=\sqrt{m+x^2/2}\,(xF(x)-M(x))/x^2,
\quad F=P(|S|\le x),\quad M=E[|S|\,1_{|S|\le x}].
$$
The derivative of $xF-M$ is $F$. Multiplying the derivative by positive factors shows its sign is that of
$$
 D_m(x)=(x^2+4m)M(x)-2mxF(x).
$$
The whole-sphere derivative vanishes precisely when the arc derivative does: the tangent gradient at an interior two-block normal is fixed by permutations within each block, so is forced into its one-dimensional invariant tangent subspace. The section function is differentiable on the positive orthant, e.g. from convolution of uniform densities: it is locally a finite sum of powers $(\sum_i\pm v_i)_+^{n-1}$ divided by $\prod_i v_i$ times smooth factors. This follows by inclusion–exclusion on the density of a weighted sum of uniforms, or [AG, §2]. Likewise full permutation symmetry gives $f'(2)=0$.

## 2. Finite dimensions $2\le m\le63$

This step uses exact sign variation, not sampled values. Write
$$
 A(x)=\sum_{j=0}^m(-1)^j{m\choose j}(x+m-2j)_+^m,
\quad B(x)=\sum_{j=0}^m(-1)^j{m\choose j}(x+m-2j)_+^{m+1}.
$$
$A/(2^m m!)$ is the distribution function of $S$ by inclusion–exclusion on $[0,2]^m$. By symmetry $F$ is twice its increment from zero. Set $C=2^{m-1}m!$. Then $(m+1)C F(x)=(m+1)(A(x)-A(0))$. By integration by parts and $B'=(m+1)A$, we have $(m+1)C M(x)=(m+1)xA(x)-B(x)+B(0)=:V(x)$. Consequently $(m+1)C D_m(x)$ is the following polynomial on each knot interval above 2:
$$
 (x^2+4m)V(x)-2m(m+1)x(A(x)-A(0)).
$$
Use all knots $2<L\le m$ with $L+m$ even. At each interior knot test its value separately. For each finite cell $(L,H)$, form $(1+u)^dP((L+Hu)/(1+u))$, $d=\deg P$; for the last cell use $P(L+u)$. Zero coefficients are deleted before counting sign changes. Descartes' rule certifies zero or one positive root counting multiplicity when the number of changes is respectively zero or one. The supplied script constructs the polynomials from binomial coefficients, fails if any count exceeds one, and sums all cell and knot counts excluding $x=2$. There are 1,023 cells including rays across the 62 values of $m$; the total for each individual $m$ is exactly one. The certificate also checks that the first nonzero coefficient on the first cell is negative and the leading coefficient on the last ray is positive. Therefore $D_m$ starts negative just right of 2 and is positive near infinity. By continuity and its single interior root, its signs are strictly negative and then strictly positive everywhere else. This proves the strict arc minimum, without importing any endpoint-extremality result.

## 3. An explicit local central limit estimate for all $m\ge64$

Write $Y=S/\sqrt{m/3}$, $q_m(z)=\sqrt{2\pi}\,p_Y(z)$, $h=1/m$. We shall use
$$
 q_m(z)=e^{-z^2/2}\{1-h(z^4-6z^2+3)/20\}+R_m(z),\qquad
 \|R_m^{(j)}\|_\infty\le E_j/m^2,
$$
for $j=0,2,4$, with $E_0=1/2,E_2=13/4,E_4=31$. Here are details, including the numerical constants.

The characteristic function of $Y$ is $\operatorname{sinc}(w)^m$ for $w=u\sqrt{3/m}$. The approximating transform is $e^{-u^2/2}(1-u^4/(20m))$: Fourier inversion of $u^4$ multiplies the Gaussian by its fourth Hermite polynomial. For $|w|\le2$ the product for sine gives
$$
 -\log(\operatorname{sinc}w)=w^2/6+w^4/180+r(w),
 \qquad 0\le r(w)\le w^6/1500.
$$
Indeed its even coefficient of order $2j$ is $\zeta(2j)/(j\pi^{2j})$, so successive coefficients have ratio at most $1/\pi^2$. The order-six coefficient is $1/2835$ by Taylor expansion of sine and log; $1/[2835(1-4/\pi^2)]<1/1500$. Using $0\le e^{-s}-1+s\le s^2/2$ and $0\le1-e^{-s}\le s$ for $s\ge0$, the absolute transform error here is bounded by
$$
 m^{-2}e^{-u^2/2}\big(27u^6/1500+u^8/800\big).
$$
After inverse Fourier transformation the normalized error norm for derivative $j$ is bounded by $\sqrt{2/\pi}\int_0^\infty u^j|\mathrm{error}(u)|du$. Extending this low-frequency bound to the full half-line to evaluate it only costs an overestimate. The constant obtained is $27(j+5)!!/1500+(j+7)!!/800$.

For the actual missing tail $w>2$, $u>\sqrt{4m/3}>9$. On $w<\pi$, the same sine product yields $|\operatorname{sinc}w|^m\le e^{-u^2/2}$; on $w\ge\pi$ use $w^{-m}$. Thus the tail, after multiplication by $m^2$, costs at most the normalized integral over $u>9$ of
$$
 u^j e^{-u^2/2}(9u^4/8+3u^6/80)
$$
plus the integral on $w\ge\pi$ of $m^2 u^j w^{-m}$. The first is $<1/1000$: factor out $e^{-81/4}$ and bound the rest by $2\sqrt{2/\pi}\int_0^\infty u^{10}e^{-u^2/4}du=2\sqrt2\,2^5\,9!!<122000$ since on $u>9$ all indicated powers are at most $u^{10}$. The second is at most
$$
 m^2(m/3)^{(j+1)/2}\pi^{j+1-m}/(m-j-1)
 \le m^5 3^{5-m}<1/1000
$$
for $m\ge64$, by monotonicity after 64. Summing the two tails with the low-frequency constant gives the asserted $E_j$. Absolute integrability through order 4 justifies differentiation. The normalizing factor and both tails are accounted for.

## 4. Sign certification at all large dimensions

Use $y=x\sqrt{3/m}$, $t=y^2$. The lower endpoint becomes $t_0=12/m$. From the formula for $D_m$, after scaling and division by positive quantities, its sign equals the sign of
$$
 K_m(t)=(12+t)\int_0^1 u\,q_m(u\sqrt t)du-6\int_0^1 q_m(u\sqrt t)du.
$$
Exactly $K_m(0)=0$ and $K_m(t_0)=0$ (the latter by full diagonal symmetry, not by approximating its value). Define $K_h^G$ by replacing $q_m$ with the displayed Gaussian and fourth-Hermite approximation of §3.

For an even $C^4$ remainder $R$, on $t\ge0$ the first and second $t$-derivatives of $R(u\sqrt t)$ are bounded in absolute value by $u^2\|R''\|/2$ and $u^4\|R^{(4)}\|/12$. The first follows by integrating $R''$ from zero; the second follows from $zR''(z)-R'(z)=\int_0^z sR'''(s)ds$ and $|R'''(s)|\le s\|R^{(4)}\|$ for $z,s\ge0$, extending by continuity at zero. Consequently the uniform bounds for $|K_m^{(j)}-(K_h^G)^{(j)}|$, in orders $j=0,1,2$, are $h^2$ times, respectively,
$$
 E_0((12+t)/2+6),\quad E_0/2+E_2((12+t)/8+1),\quad
 E_2/4+E_4((12+t)/72+1/10).
$$

The following finite, rational sign certificates correspond to the four closed intervals. The polynomial $P_h$ below denotes $K_h^G$ after replacing the exponential $e^{-z/2}$, where $z=t u^2$, by the degree-400 Taylor polynomial at zero. The margins are **before** the errors just described.
 
| closed interval for $t$ | signed inequality for $P_h$ |
|---|---|
| $[0,1]$ | $-P_h''>1/400$ |
| $[1,20]$ | $-P_h>1/300$ |
| $[20,36]$ | $P_h'>3/500$ |
| $[36,196]$ | $P_h>1/64$ |

To verify exactly, it suffices to check $h=0,1/64$ by affine dependence. The Taylor coefficients $c_i$ of the polynomial in $z$ are the product of the coefficients $(-1)^j/(2^j j!)$ for $0\le j\le400$ with the polynomial $1-h(z^2-6z+3)/20$. Thus
$$
 P_h(t)=\sum_i c_i\left[\frac{6i}{(i+1)(2i+1)}t^i+\frac{1}{2i+2}t^{i+1}\right].
$$
In each row subtract the margin from the signed polynomial on the left. All coefficients after the same Möbius substitution of §2 are strictly positive for each endpoint $h$ of its allowed interval, including constant and leading coefficients. This proves the strict sign on the **closed** interval. All eight coefficient checks run using the standard-library verifier.

For clarity, no infinite Taylor tail is discarded. In derivatives $j=0,1,2$ the exponential approximation on $0\le z\le196$ has error $\le 98^{401-j}/[2^j(401-j)!]$ by the Lagrange remainder. Each of these is $<10^{-12}$, as checked exactly. The quadratic multiplier and its first two derivatives are bounded there in absolute value by 40, 1, 1, respectively. The product errors in these derivatives are thus $<10^{-9}$, and integrating, multiplying by $12+t$, and differentiating at most twice gives error $<10^{-6}$ for $P_h^{(j)}-(K_h^G)^{(j)}$. The preceding explicit bounds at $h=1/64$ plus this $10^{-6}$ are smaller than the indicated margins in each row of the table (the script checks the rational inequalities). Thus the indicated derivative/value signs hold strictly for $K_m$.

Because $0<t_0<1$, strict concavity on $[0,1]$ and the two exact roots at $0,t_0$ imply $K_m<0$ for $t_0<t\le 1$. The next interval remains negative; $[20,36]$ has exactly one zero by strict increase and opposite endpoint signs, and the following interval is strictly positive. Finally for $y\ge14$, in the original standardized criterion the sign is that of
$$
 (12+y^2)E(|Y|1_{|Y|\le y})-6yP(|Y|\le y).
$$
We have $EY^2=1$, $EY^4=3-6/(5m)\le3$. Hölder implies $E|Y|\ge1/\sqrt3$. Since $E(|Y|1_{|Y|>y})\le1/y$, the truncated mean exceeds $1/2$ for $y\ge14$. The last display is positive. This covers the whole ray, irrespective of the support cutoff.

## 5. Limiting location

The explicit estimates imply uniform convergence to $K_0^G$ on compact intervals, so every accumulation point of the unique roots $t_m\in(20,36)$ solves the limiting equation. The same sign certificate at $h=0$, or the elementary argument below, gives a unique root there. Hence $t_m\to y_*^2$, and $a_n=y_m/\sqrt{12+2y_m^2}$.

With $I(y)=\int_0^y e^{-s^2/2}ds$, the limiting equation is $G(y)=(12+y^2)(1-e^{-y^2/2})-6yI(y)=0$. Differentiation twice gives $G''(y)=2-(2+y^2+y^4)e^{-y^2/2}$. For $y>0$, with $z=y^2/2$, its sign changes from negative to positive exactly once: $(e^z-1-z)/z^2$ increases strictly from $1/2$ to infinity and must equal 2. Since $G(0)=G'(0)=0$, and $G'(y)\sim2y,G(y)\sim y^2$ at infinity, both successive integrations preserve the one-change-from-negative-to-positive property. Thus the positive root is unique and simple. Numerical values $y_*\approx5.22186138$, $a_*\approx0.64017405$ are for orientation, not proof inputs.
