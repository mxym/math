# The tolerance dependence in the uniform medium-divisor window problem

For integers $n,y\ge1$ and $x\ge0$, let $B(n,x,y)$ be the number of integers in the open interval $(x,x+y)$ with an integer divisor strictly between $n$ and $2n$. Write
$$
D(n,y)=\sup_{x\in\mathbb Z_{\ge0}}B(n,x,y)/y,\qquad
Y_\epsilon(n)=\min\{Y:\ D(n,y)\le\epsilon\ \text{for every integer }y\ge Y\}.
$$
The minimum is $\infty$ if the set is empty. This is the uniform and eventual interpretation in [Formal Conjectures #450](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/450.lean). [Snyder's Lean work](https://www.starfleetmath.com/solutions/84485327-f75e-4876-a9de-651a67efe31a) gives $Y_\epsilon(n)\asymp_\epsilon n$ for fixed $0<\epsilon<1$ and sufficiently large $n$. Its public report explicitly leaves the dependence on $\epsilon$ open.

Put $\delta=1-(1+\log\log2)/\log2=0.086071\ldots$ and $h=\min(n,y/n)$. We prove the following bounds with absolute implicit constants, uniformly for $y\ge n$ and $h$ sufficiently large:
$$
\frac{1}{(\log h)^\delta(\log\log h)^{3/2}}
\ll D(n,y)
\ll \frac{(\log\log h)^\delta}{(\log h)^\delta}.
\tag{1}
$$
Thus the logarithmic exponent in the maximal local density is exactly $\delta$ along every path on which $h\to\infty$. In particular, if
$$
K_-(\epsilon)=\liminf_{n\to\infty}\frac{Y_\epsilon(n)}n,\qquad
K_+(\epsilon)=\limsup_{n\to\infty}\frac{Y_\epsilon(n)}n,
$$
then as $\epsilon\downarrow0$, both satisfy
$$
\frac{\log\log K_\pm(\epsilon)}{\log(1/\epsilon)}
\longrightarrow\frac1\delta.
\tag{2}
$$
These results do not fix the remaining secondary factors or the exact threshold.

## 1. Uniform upper bound

Let $w=\exp(\log h/(100\log\log h))$, let $\mathcal P$ be the primes at most $w$, and set $S=\sum_{p\in\mathcal P}1/p$. By Mertens,
$$
S=\log\log h-\log\log\log h+O(1).
\tag{3}
$$
For $m\ge1$, write $\omega(m)=\#\{p\in\mathcal P:p\mid m\}$. We will use the following elementary interval bound for any weights $0\le\lambda_p\le1$:
$$
\sum_{m\in I\cap\mathbb Z}\prod_{p\in\mathcal P}(1-\lambda_p1_{p\mid m})
\le |I|\left(\prod_{p\in\mathcal P}(1-\lambda_p/p)+e^{-5S}\right)+O(h^{1/5}).
\tag{4}
$$
Here $I$ is any interval of positive reals, including the quotient intervals below, and $|I|$ is its length. To prove (4), take the even Bonferroni truncation at the smallest even integer $J\ge10S$. It is valid for these weighted factors, for example by taking independent Bernoulli thinnings of the divisibility events at each fixed $m$. Each intersection counts the multiples of the product of its primes, giving its expected count with error $O(1)$. Thus rounding costs $O((J+1)w^J)=O(h^{1/5})$. The difference between truncated and full main products is at most $\sum_{\ell>J}S^\ell/\ell!\le e^{-5S}$, by Stirling and a geometric tail. None of the constants depends on the translate, prime weights, or length.

Set
$$
a=1/\log2,\qquad t=a/2,\qquad \mathcal I(a)=a\log a-a+1=\delta.
$$
First remove the points in $(x,x+y)$ with $\omega(m)\ge aS$. Take $r=\lceil aS\rceil$ and $j=\lfloor(a-1)S\rfloor$. The $j$-th binomial moment of $\omega$ over this interval is bounded by $yS^j/j!+O(w^j)$, again by counting multiples of products. Divide by $\binom rj$. The main normalized bound is at most
$$
\frac{S^j}{r(r-1)\cdots(r-j+1)}\ll e^{-\mathcal I(a)S},
$$
because the logarithm of the reciprocal ratio is $S\int_1^a\log v\,dv+O(1)$ by Riemann summation. The rounding error is negligible relative to $y e^{-\delta S}$. Thus the removed points account for $O(y e^{-\delta S})$.

For the remaining integers, sum over every possible $d\in(n,2n)$ dividing $m$, writing $m=dk$. Define $\omega_{\neg d}(k)=\#\{p\in\mathcal P:p\nmid d,\ p\mid k\}$ and $s_d=\sum_{p\in\mathcal P,\ p\mid d}1/p$. The identity $\omega(dk)=\omega(d)+\omega_{\neg d}(k)$ gives, pointwise,
$$
1_{\omega(dk)\le aS}\le t^{-aS}t^{\omega(d)}t^{\omega_{\neg d}(k)}.
$$
Apply (4) to $k\in(x/d,(x+y)/d)$, omitting primes dividing $d$ and using weight $1-t$ at all other primes. The resulting bound on the inner sum of $t^{\omega_{\neg d}(k)}$ is
$$
\frac{y}{d}\big(e^{-(1-t)(S-s_d)}+e^{-5S}\big)+O(h^{1/5}).
$$
The factors depending on $d$ in the main term must be averaged jointly, not counted in separate large-deviation cases. Specifically
$$
t^{\omega(d)}e^{(1-t)s_d}
=\prod_{p\in\mathcal P,\ p\mid d} t e^{(1-t)/p}.
$$
All factors lie in $(0,1)$, so (4) applies again on $(n,2n)$ with weights $1-t e^{(1-t)/p}$. Their main product is at most $O(e^{-(1-t)S})$, since $\sum_p1/p^2$ converges. The other terms of (4), after division by $n$, are negligible since $h\le n$. As $1/d\le1/n$, this bounds the weighted average of $d$ in the main term.

Putting these bounds together, the remaining points account for
$$
O\!\left(y\,t^{-aS}e^{-2(1-t)S}\right)+
O\!\left(e^{O(S)} n h^{1/5}\right)+O\!\left(y\,t^{-aS}e^{-5S}\right).
$$
The rounding term is negligible because $h\le y/n$ and $S=O(\log\log h)$. Our choices of $a,t$ satisfy $2(1-t)+a\log t=2-a+a\log(a/2)=\delta$, so the first term is $O(y e^{-\delta S})$. Combining with the removed points and (3) proves the upper bound in (1).

## 2. Uniform lower bound by complementary divisors

Write $C=y/n$. First suppose $C\le n$ and $C$ is sufficiently large. Put $L_n=\operatorname{lcm}(n+1,\dots,2n-1)$ and choose $x=L_n+n$. If an integer $m$ satisfies $3y/4<m\le y$ and has a divisor $k$ with $C/2<k\le3C/4$, then $n<m/k<2n$. Consequently $L_n+m$ is counted in $(x,x+y)$. We use [Ford, Theorem 2 and Corollary 2](https://arxiv.org/abs/math/0401223) for this short-interval count with endpoint $y$, interval length $y/4$, and divisor range $(C/2,3C/4]$. Its lower endpoint $C/2$ is at most $\sqrt y$, and the lower bound on interval length in that theorem holds for all sufficiently large $C$. Here its Corollary 2 parameter $Y$ is comparable to $C$, since $y/(C/2)=2n$. This gives
$$
B(n,x,y)\gg \frac{y}{(\log C)^\delta(\log\log C)^{3/2}}.
$$
This step is an enlargement of the factorial/lcm dense-block argument in Snyder's report; the complementary divisor is now in a band set by the length ratio, not by $n$.

If $C\ge n$, average $B(n,x,y)$ over a full period of starting residues $x\bmod L_n$. Each of the $y-1$ positions in an open window has the exact global periodic density of having a divisor in $(n,2n)$. By Ford's Corollary 2 this density is $\asymp (\log n)^{-\delta}(\log\log n)^{-3/2}$. Replacing its right-closed divisor band by an open one changes the density by at most $1/(2n)$. The maximum of the translates is at least the average. This finishes (1).

## 3. Inverting the uniform bounds

Write $E=\log(1/\epsilon)$. For $\epsilon$ sufficiently small, apply the lower bound at $y=\lfloor Cn\rfloor$, first with fixed $\epsilon,C$ and then $n\to\infty$, taking $\log C=c\epsilon^{-1/\delta}E^{-3/(2\delta)}$ for a sufficiently small absolute $c>0$. Its lower bound exceeds $\epsilon$, so $Y_\epsilon(n)>\lfloor Cn\rfloor$ eventually. The upper bound applies to every integer $y\ge Cn$ if $n$ is sufficiently large and $\log C=C_0\epsilon^{-1/\delta}E$ for a sufficiently large absolute $C_0$: the upper function of $h$ is eventually decreasing and $h\ge C$. We obtain
$$
c\,\epsilon^{-1/\delta}E^{-3/(2\delta)}
\le \log K_-(\epsilon)
\le \log K_+(\epsilon)
\le C_0\,\epsilon^{-1/\delta}E.
$$
Taking one more logarithm proves (2).

The [finite verifier](verify_factor_erdos450_tolerance_dependence.js) makes 144,503 exact assertions, checking the weighted Bonferroni truncation, exact overlap identity for the divisor and quotient, the translated complementary-divisor implication, and the open-window periodic average. The asymptotic parts depend on the arguments above, not finite experiments.
