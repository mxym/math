# A prime-scale bound for composite divisors of shifted factorials

Let $A(X)$ count distinct composite integers $u<X$ that divide $n!+1$ for at least one positive integer $n$. Let $A_k(X)$ restrict to $\Omega(u)=k$, with prime factors counted with multiplicity. This is the counting function in [Erdős #1073](https://www.erdosproblems.com/1073), originally [Hardy and Subbarao, question F*](https://www.math.ualberta.ca/~subbarao/documents/2002_Pillai.pdf).

**Theorem.** Unconditionally,
$$
\limsup_{X\to\infty}\frac{\log X}{X}A(X)\le
\log(5/3)+\sum_{k=3}^\infty
\frac{(k+2/3)(2/3)^{k-1}}{(k-1)!k!}
=0.6566292970\ldots<0.657.
\tag{1}
$$
In fact the semiprime layer alone has upper coefficient $\log(5/3)$, and for some absolute $C$ and all sufficiently large integers $K$,
$$
\limsup_{X\to\infty}\frac{\log X}{X}\sum_{k\ge K} A_k(X)\ll (C/K)^K.
\tag{2}
$$
In particular $A(X)\ll X/\log X$. This improves the $O(X/\log\log X)$ global bound in the [July 2026 working report](https://erdosproblemaday.com/report/1073). It does not imply the conjectural $X^{o(1)}$.

## Small least prime factors

If $u\mid n!+1$, every prime divisor of $u$ exceeds $n$. In particular $\Omega(n!+1)\le n$, since $(n+1)^{\Omega(n!+1)}\le n!+1\le(n+1)^n$. Thus $\Omega(u)=k$ forces $n\ge k$, $P^-(u)\ge k+1$ and $k\log(k+1)\le\log X$.

For each prime $p$, the number of possible indices $1\le n<p$ with $p\mid n!+1$ is $O(p^{2/3})$. This is the constant-polynomial case of [Luca–Shparlinski, Lemma 4, as stated in Lai's Lemma 2.2](https://doi.org/10.1017/S0004972725100543). It also has a short proof: if two such indices differ by $h$, the smaller one is a root of the nonzero monic polynomial $\prod_{1\le j\le h}(t+j)-1$ modulo $p$. There are at most $h$ such pairs with difference $h$. If there are $t$ indices in increasing order, at least $(t-1)/2$ neighboring pairs have difference at most $2p/(t-1)$, since the sum of all neighboring differences is less than $p$. Summing the polynomial root bound over these differences proves $t-1\ll(p/(t-1))^2$ for $t\ge2$.

Write $L=\log X$, fix $2/3<c\le1$, and in layer $k$ put $Y_k=X^{1/(k+c)}$. If a counted $u$ has least prime $p\le Y_k$, then $u/p$ is a divisor with exactly $k-1$ prime factors of some $n!+1$ with $n<p$ from the list above. Its choices for a given $n$ are at most $\binom{n}{k-1}\le p^{k-1}/(k-1)!$: label the prime-factor occurrences of $n!+1$ and allow every subset of $k-1$ labels, which also bounds the number of different divisors when primes repeat. Consequently the small-least-prime part of layer $k$ is at most
$$
\ll \frac{Y_k^{k+2/3}}{(k-1)!}
=\frac{X}{(k-1)!}\exp\!\left(-\frac{(c-2/3)L}{k+c}\right).
\tag{3}
$$
Here even counting the primes $p\le Y_k$ as unrestricted integers suffices. The sum of (3) is $o(X/L)$ for each fixed $c>2/3$: up to $k=\sqrt L$ the exponential factor is at most $e^{-(c-2/3)\sqrt L/2}$, while above $\sqrt L$ the factorial tail alone is smaller than any power of $1/L$.

## Large least prime factors and the uniform tail

For the rest of the layer it suffices to count all integers below $X$ with exactly $k$ prime factors, each exceeding $Y=Y_k$. Take an ordered list $p_1,\ldots,p_{k-1}$ of all but the last prime factor, with product $d$. We only need lists with $d\le X/Y$. The choice of the last prime is bounded by $\pi(X/d)\ll X/(d\log Y)$. The constraint on the other factors is
$$
\sum_{i=1}^{k-1}\frac{\log(p_i/Y)}{\log Y}\le c.
$$
For $s>0$ the sum of $1/d$ over such lists is thus at most
$$
e^{sc}\left(\sum_{p\ge Y}\frac1p(p/Y)^{-s/\log Y}\right)^{k-1}.
\tag{4}
$$
Writing $\delta=s/\log Y$, partial summation and $\pi(v)\ll v/\log v$ give
$$
\sum_{p\ge Y}\frac1p(p/Y)^{-\delta}
\ll (1+\delta)\int_Y^\infty\frac{(Y/v)^\delta}{v\log v}\,dv
\ll 1/s+1/\log Y.
$$
Only $k\log(k+1)\le L$ can contribute to $A(X)$, so $k\le 2L/\log L$ for large $X$; in particular $\log Y_k\ge(\log L)/3$ uniformly in these layers. Choose $s=K$ in (4). For each fixed $K$ and sufficiently large $X$ the weight sum is $O(1/K)$ uniformly. After multiplying by $X/\log Y=(k+c)X/L$, summing over $k\ge K$, and including (3), we obtain (2); the factor $e^{Kc}$ and the leading factor polynomial in $K$ are absorbed by increasing the absolute constant $C$ in $(C/K)^K$. The same argument with a sufficiently large fixed $s$ gives $A(X)=O(X/L)$ directly.

## A constant from the fixed layers

For fixed $k$, squared prime factors exceeding $Y_k$ cost at most $X\sum_{p>Y_k}p^{-2}=O(X/Y_k)=o(X/L)$ integers. In the squarefree case choose the largest prime last and count all orders of the other $m=k-1$ primes. Each represented integer is counted exactly $m!$ times when the prime choices are all present. For an upper bound there are at most $\pi(X/d)$ choices of largest prime, and $d\max_i p_i\le X$ is necessary. By the prime number theorem, with $a=1/(k+c)$ and $t_i=\log p_i/L$, the normalized upper coefficient of this layer is at most
$$
\frac1{m!}\int_{\substack{t_i\ge a\\\sum_i t_i+\max_i t_i\le1}}
\frac{dt_1\cdots dt_m}{(1-\sum_i t_i)t_1\cdots t_m}.
\tag{5}
$$
Precisely, $\pi(X/d)=(1+o(1))X/(dL(1-\sum_i t_i))$ uniformly on this region since $X/d\ge Y_k$. The prime measures $\sum_{X^a\le p\le X}p^{-1}\delta_{\log p/L}$ converge weakly to $dt/t$ on $[a,1]$ by partial summation and the prime number theorem. Their fixed products converge as well, by rectangular approximation; the region boundary has zero limiting measure and the integrand apart from the measure is bounded by $1/a$. Thus (5) is an upper bound on the limsup. The small-least-prime part contributes zero to it by (3).

For $k=2$ expression (5) is $\int_{1/(2+c)}^{1/2}dt/(t(1-t))=\log(1+c)$. For $k\ge3$ change variables $t_i=(1+u_i)/(k+c)$. The transformed domain $\sum_i u_i+\max_i u_i\le c$, $u_i\ge0$, has volume $c^m/(m+1)!$. Indeed order the $u_i$ increasingly, replace them by successive nonnegative differences $z_i$, and obtain the simplex $\sum_{i=1}^m(m+2-i)z_i\le c$; multiply its volume by $m!$ for the permutations. The transformed integrand in (5) before the outside $1/m!$ is
$$
\frac{k+c}{(1+c-\sum_i u_i)\prod_i(1+u_i)}\le k+c.
$$
This gives coefficient at most $(k+c)c^{k-1}/((k-1)!k!)$. Use (2) to sum the fixed-layer bounds, first letting the number of layers tend to infinity at fixed $c$ and then taking $c\downarrow2/3$. The series converges uniformly for $2/3\le c\le1$. This proves (1).

## A reusable counting criterion

The same argument applies to any sequence of positive integers $a_n$ whose prime factors exceed $n$, with $\Omega(a_n)\le Bn$ for fixed $B$, and for which $\#\{n<p:p\mid a_n\}\ll p^\theta$ for primes $p$ and $0\le\theta\le1$. In (3) the factor $B^{k-1}$ does not affect the factorial-tail argument, and $k\log(k/B)\le L$ for $k>B$ still gives the uniform growing lower bound on $\log Y_k$. Taking $\theta<c\le2$ and then $c\downarrow\theta$, the upper coefficient becomes $\log(1+\theta)+\sum_{k\ge3}(k+\theta)\theta^{k-1}/((k-1)!k!)$. In particular bounded single-prime witness counts would imply $o(X/\log X)$, without any joint-prime input. This criterion does not assert that factorials have bounded witness counts.

The [fixed verifier](verify_factor_erdos1073_composite_divisor_bound.js) makes 506 exact assertions, checking small factorial witnesses and multiplicities, the polynomial pair counts, and a rational enclosure for the numerical upper coefficient in (1). The unresolved issue is simultaneous occurrence of the same factorial index modulo different large primes or prime powers; (3) and (4) do not use such correlation.
