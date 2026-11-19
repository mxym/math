# Quartic Gaussian stability for subcubic real Rademacher moments

Let $2<p<3$, $Z\sim N(0,1)$, $\varepsilon_j$ independent equiprobable signs, and $S=\sum_{j=1}^n a_j\varepsilon_j$ for real coefficients with $\sum a_j^2=1$. There is $b_p>0$, independent of the coefficients and $n$, such that
$$
 m_p-\mathbb E|S|^p\ \ge\ b_p\sum_j a_j^4,\qquad m_p:=\mathbb E|Z|^p.
 \tag{1}
$$
This is the Gaussian (unrestricted-length) Rademacher conjecture of Jakimiuk–Tang–Tkocz, §3, in the remaining open exponent range. It says nothing about the best finite-list comparator or the sharp value of $b_p$. The qualitative inequality, its integral reduction and the single-crossing input below are prior results of Haagerup, Nazarov–Podkorytov and Mordhorst. The argument is a quantitative use of those results.

## 1. The Haagerup–Mordhorst integral

Ignore zero coefficients. Define $f(u)=|\cos u|$, $g(u)=\exp(-u^2/2)$, and
$$
 D(s)=c_p\int_0^\infty [e^{-t^2/2}-f(t/\sqrt s)^s]\,t^{-p-1}\,dt
     =c_p s^{-p/2}H(s),\quad
 H(s)=\int_0^\infty [g(u)^s-f(u)^s]u^{-p-1}\,du .
$$
Here $c_p^{-1}=\int_0^\infty (\cos t-1+t^2/2)t^{-p-1}dt$ is positive and finite: the integrand's numerator is nonnegative, is $O(t^4)$ at zero and $O(1+t^2)$ at infinity. Scaling and Tonelli give a formula for $\mathbb E|S|^p$ and $m_p$ using this kernel. Their quadratic terms cancel as both variances are one. Independence and weighted arithmetic–geometric mean give $\mathbb E\cos(tS)=\prod_j\cos(a_jt)\le\sum_j a_j^2 f(a_jt)^{1/a_j^2}$. Consequently, as in Mordhorst's Lemma 2.1,
$$
 m_p-\mathbb E|S|^p\ \ge\ \sum_j a_j^2D(1/a_j^2).
 \tag{2}
$$
The integrals for $D$ are continuous in $s$ on compact subintervals of $(0,\infty)$ by domination: the bracket is uniformly $O(t^4)$ near zero by Taylor expansion and bounded in absolute value by two everywhere.

**Strictness at fixed exponents.** Write $s_0=\sqrt2$, $d\mu=u^{-p-1}du$ and $W(y)=\mu\{f<y\}-\mu\{g<y\}$, $0<y<1$. We use the following nontrivial inputs from O. Mordhorst, *The optimal constants in Khintchine's inequality for the case $2<p<3$*, Colloq. Math. 147 (2017), 203–216, §§3–5:
1. $H(s_0)\ge0$ (the base estimate, §5).
2. For some $y_0\in(0,1)$, $W\le0$ below $y_0$ and $W\ge0$ above $y_0$. Moreover $W$ is strictly negative on an interval adjacent to zero (Lemma 4.1).

Here is why the resulting estimate is strict when $s>s_0$, even if one uses only a nonstrict base estimate. Signed layer-cake gives $H(s)/s=\int_0^1 y^{s-1}W(y)dy$. Fubini with the pointwise difference of the sublevel indicators is justified since its integrated absolute value, with weight $sy^{s-1}$, is $\int |g^s-f^s|d\mu<\infty$. Then
$$
 \frac{H(s)}{s}-y_0^{s-s_0}\frac{H(s_0)}{s_0}
 =\int_0^1 y^{s_0-1}(y^{s-s_0}-y_0^{s-s_0})W(y)\,dy>0.
$$
The integrand is nonnegative on both sides and is strictly positive on a nonempty interval below $y_0$. This proves $D(s)>0$ for every $s>s_0$.

**Uniformity as $s\to\infty$.** Choose $u_0>0$ small enough that $\log f(u)\le-u^2/2-cu^4$ on $|u|\le u_0$ for some $c>0$; the coefficient of $u^4$ is $-1/12$. For $0\le t\le u_0\sqrt s$ the integrand difference defining $D(s)$ is nonnegative. For large $s$ the fixed interval $[1,2]$ contributes at least $c'_p/s$, since there the difference is at least $e^{-t^2/2}(1-e^{-ct^4/s})$. The remaining region $t>u_0\sqrt s$ can subtract at most $(u_0\sqrt{s})^{-p}/p$ from the integral. Although cosine does not decay, this last bound is $o(1/s)$ precisely because $p>2$. Thus $D(s)\ge c''_p/s$ for large $s$. Together with continuity and strictness this gives
$$
 \inf_{s\ge s_1} sD(s)>0\qquad\text{for each fixed }s_1>s_0.
 \tag{3}
$$

## 2. Dominant coefficients give a uniform gap

Independence gives $\mathbb ES^4=3-2\sum a_j^4$. Hölder interpolation between moments of orders 2 and 4 gives
$$
 \mathbb E|S|^p\le(3-2\sum a_j^4)^{(p-2)/2}.
$$
At $s_0=\sqrt2$ one has $3-2/s_0^2=2$, whereas
$$
 m_p=\frac{2^{p/2}\Gamma((p+1)/2)}{\sqrt\pi}
       > 2^{(p-2)/2}.
$$
Indeed $\Gamma$ is increasing on $[3/2,\infty)$: its logarithmic derivative $\psi$ is increasing, and $\psi(3/2)=\lim_{N\to\infty}(\log N-\sum_{k=0}^{N-1}(k+3/2)^{-1})>0$. To see the strict lower bound, apply the strict midpoint inequality for $1/x$ to the intervals $[k+1,k+2]$: the sum is at most $\log(N+1)-(\log 2-2/3)$, retaining the positive first-interval slack. Finally $\Gamma(3/2)=\sqrt\pi/2$.

By continuity choose $s_1>\sqrt2$ sufficiently close that $\eta_p=m_p-(3-2/s_1^2)^{(p-2)/2}>0$. If any $1/a_j^2<s_1$, then $\sum a_j^4>1/s_1^2$, so the moment gap is at least $\eta_p\ge\eta_p\sum a_j^4$. Otherwise all $1/a_j^2\ge s_1$ and (2)–(3) imply (1). Taking the smaller of the two positive constants completes the proof. ∎
