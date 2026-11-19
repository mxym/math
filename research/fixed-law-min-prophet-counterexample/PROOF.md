# One bounded i.i.d. cost law with an unbounded optimal prophet ratio

## Statement

In the one-choice i.i.d. cost prophet problem, the law is known, the $n$ samples are independent, stopping is irrevocable, and exactly one observation must be selected (the last is forced if none was selected earlier). Write $G_n$ for the *minimum* expected cost among all online rules and $M_n=\mathbb E\min_{i\le n}X_i$ for the prophet's expected cost. The comparison is the ratio of expectations, not the expectation of a samplewise ratio.

For **each fixed** $a>0$, take the atomless probability law supported on $[0,1]$ with survival
$$
 S_a(x)=
 \begin{cases}1,&x\le0,\\
 \exp\{-1/[\log(1/x)]^a\},&0<x<1,\\
 0,&x\ge1 .
 \end{cases}
$$
The survival is continuous, strictly decreasing from 1 to 0 and smooth in the open interval; hence this is a bounded nonnegative law with finite, strictly positive mean. It is not required that its density be bounded at the left endpoint. Put $r=1/(a+1)$. As $n\to\infty$,
$$
 \frac{\log(G_n/M_n)}{n^r}
 \longrightarrow (1+1/a)a^r-(a+1)^r>0.                         \tag{1}
$$
Thus even one fixed continuous law has unbounded optimal ratio along the entire sequence of horizons. For $a=1$ the limit is $2-\sqrt2$. Varying the law gives every stretched-exponential exponent $0<r<1$.

## Prophet: one exact integral

Since the minimum has survival $S_a^n$, setting $y=-\log x$ and then $u=y/n^r$ gives
$$
 M_n=\int_0^\infty e^{-y-n/y^a}\,dy
     =n^r\int_0^\infty \exp[-n^r f(u)]\,du,
 \qquad f(u)=u+u^{-a}.
$$
This continuous function has a unique minimum at $u_*=a^r$, of value $m=(1+1/a)a^r$. On a fixed positive-length interval about $u_*$ its value is at most $m+\epsilon$; this gives $\limsup[-\log M_n]/n^r\le m+\epsilon$. Conversely, split at any fixed $A>m$. On $(0,A)$ the integral before its factor $n^r$ is at most $A e^{-n^r m}$; on $[A,\infty)$ use $f(u)\ge u$ to bound it by $e^{-A n^r}/n^r$. Letting $n\to\infty$ and then $\epsilon\downarrow0$ proves $-\log M_n\sim mn^r$.

## Online: the exact Bellman recursion

With one draw $G_1=\mathbb E X$. At the first of $n+1$ draws one can choose the observed $X$ or continue with conditional expected cost $G_n$, independent of the entire history. Taking the smaller of the two is optimal, even among randomized policies. Consequently
$$
 G_{n+1}=\mathbb E\min(X,G_n)=\int_0^{G_n} S_a(x)\,dx.
$$
All $G_n$ are in $(0,1)$, decrease strictly, and tend to zero: any positive limiting fixed point $g$ would have $\int_0^g S_a(x)\,dx<g$. Write $L_n=-\log G_n$, which tends to infinity. If $E$ is exponential of mean one, the substitution $x=G_n e^{-s}$ yields
$$
 G_{n+1}/G_n=\mathbb E\exp[-(L_n+E)^{-a}].
$$
For $L\to\infty$, the integrand $L^a(1-e^{-(L+E)^{-a}})$ converges to 1 and is in $[0,1]$ because $1-e^{-v}\le v$. Dominated convergence and $-\log(1-v)\sim v$ therefore give
$$
 L_{n+1}-L_n\sim L_n^{-a}.
$$
By the mean-value theorem $L_{n+1}^{a+1}-L_n^{a+1}\to a+1$, since $L_{n+1}/L_n\to1$. Summing proves $L_n\sim(a+1)^r n^r$. Subtracting this from $-\log M_n$ proves (1): the ratio of the two leading constants $m/(a+1)^r=(1+1/a)^{a/(a+1)}$ is greater than one.

## Where the general finite-mean comparison fails

[Livanos and Mehta, SODA 2024, Theorem 1.1](https://doi.org/10.1137/1.9781611977912.17) ([open proceedings PDF](https://par.nsf.gov/servlets/purl/10511091)) asserts that for each law on a nonnegative interval with finite mean there are constants $n_0,\lambda$ giving a $\lambda$-factor guarantee for every $n\ge n_0$. Equation (1) contradicts that assertion as printed. There are no atoms, horizon-dependent parameters, infinitely costly realizations or zero denominators in this example.

The proof of Lemma 3.5 uses a uniform upper bound on $\mu_{2:n}/M_n$ by its two-sample value, with $\mu_{2:n}$ the expected second-smallest cost ($n\ge2$). This bound does not hold here. Indeed the probability that at most one observation lies at or below $x$ equals $S(x)^n+n(1-S(x))S(x)^{n-1}$; integrating gives the identity
$$
 \mu_{2:n}/M_n-1=n(M_{n-1}/M_n-1).
$$
If the left side were bounded by a constant $C$ for all sufficiently large $n$, then $M_{n-1}/M_n\le1+C/n$. Multiplying these inequalities and using $\sum_{j\le n}1/j\le1+\log n$ would give $M_n\ge c n^{-C}$ for some $c>0$. This contradicts its stretched-exponential decay. This pinpoints a failure in the comparison under the stated hypotheses; it does not require a diagnosis of every other proof step.

The [earlier 2023 arXiv version](https://arxiv.org/abs/2209.07988) instead assumes an Entire cumulative hazard for its positive constant-factor theorem. Our $H(x)=1/[\log(1/x)]^a$ is not asymptotically a positive power of $x$ and does not satisfy that assumption. Nor does this example challenge the later [EC 2025 extreme-value-domain theorem](https://doi.org/10.1145/3736252.3742682). To see the distinction directly, for each target survival level $e^{-v}$, $v>0$, the minimum has corresponding quantile $x_n(v)=\exp[-(n/v)^{1/a}]$. For any $0<v_1<v_2<v_3$, the ratio $(x_n(v_3)-x_n(v_2))/(x_n(v_2)-x_n(v_1))$ tends to infinity. Common affine normalization preserves that ratio; any nondegenerate classical continuous extreme-value limit would instead give finite positive limits for both normalized spacings at these interior quantiles. Hence these costs are outside the assumed domains of attraction for minima.

There is also an elementary distinction from worst-case, horizon-dependent exponential lower bounds. For any *fixed* nonnegative integrable law with $q=\Pr(X>0)>0$, the policy waiting for zero or otherwise taking the final draw costs $q^{n-1}\mathbb E X$. For every $x>0$ with $S(x)>0$, $M_n\ge x S(x)^n$. Thus $0\le\limsup_n n^{-1}\log(G_n/M_n)\le\log(q/S(x))$. Sending $x\downarrow0$ shows that every such fixed law has subexponential ratio. The family above has all strictly sublinear power exponents for its log ratio but no exponential-in-$n$ ratio is asserted for a fixed law.
