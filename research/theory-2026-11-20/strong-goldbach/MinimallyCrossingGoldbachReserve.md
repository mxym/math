# A signed reserve on all minimally crossing rows, and the range of least-prime debits it pays

Take the [full rough-divisor inversion](https://github.com/mxym/math/commit/6f877f72) at a **prescribed** large even target $P$. Write $I=[P/3,2P/3]$, $L=\log P$, $X_P=|I|\mathfrak S(P)$, $q=P-p$ with $p\in I$ prime, and $dM(p)=(\log p)W(q-1)$, using weight $1$ or the same fixed-$K$ nonnegative neutral predecessor-tag weight as in that proof. In the latter case $W(q-1)=\mathcal V^{-1}\sum_a1_{a|q-1}$, the prime factors of $a$ come from disjoint subpower banks and are prime to $P(P-1)$, $a=P^{o(1)}$, and $\sum_a1/\phi(a)=(1+o(1))\mathcal V\asymp_K 1$.

Let $0<g<.04$, $0<\epsilon<1/2$, $y=P^g$, $z=y^\epsilon$. Define the **whole upper residual on a physical row** by
$$
 R(q)=\sum_{\substack{t|q,\ t>y\\ P^-(t)>z}}\mu(t)B_t(q),
$$
where $B_t(q)$ equals $\log(q/t)$ if $q$ has no prime divisor $\le z$, $\log r$ if $r$ is its single distinct prime divisor $\le z$, and zero otherwise. Complete inversion over all $t$, including the small ones, equals $\Lambda(q)$. Every sign below is for the **entire** $R(q)$ summed over a stated class of actual rows, not for individually selected terms of that divisor sum.

* The minimally crossing class $\mathcal C$ consists of $z$-rough $q$ such that the product $m$ of **all distinct** primes $\le y$ dividing $q$ satisfies $m>y$ but $m/r\le y$ for every prime $r|m$.
* The adverse class $\mathcal D_h$, for a fixed $h>1$, consists of **all** $q$ with $y<P^-(q)\le y^h$. It permits any number of factors and any valuations. We take $hg<.1$; in the explicit result $h=3/2$.

They are disjoint, and every row in either class is composite for large $P$. Neither class is selected by a parity sign.

**Explicit pointwise reserve.** At $g=\epsilon=1/100$, $h=3/2$, for every sufficiently large even $P$,
$$
 \sum_{p\in I,\ q\in\mathcal C\cup\mathcal D_{3/2}}dM(p)R(q)>2.3 X_P.\tag{1}
$$
The positive minimally crossing aggregate pays the full negative population $y<P^-(q)\le y^{3/2}$ and still leaves the displayed margin. This is not a lower bound on the whole residual or on the number of Goldbach pairs.

**Sharp leading balance for these two classes.** Write $\rho$ for Dickman's function. Under $P\to\infty$ first, then $g\downarrow0$ with $\epsilon=g$, the signed total on the left for any fixed $h>1$, divided by $X_P e^{-\gamma_E}/g$, tends to
$$ \frac1h-\int_1^\infty \frac{\rho(v)}v\,dv. \tag{2} $$
In particular the largest range paid at the leading scale has transition $h_*=(\int_1^\infty\rho(v)dv/v)^{-1}$, with $3/2<h_*<2$; no assertion about the sign at equality is needed. Thus even the whole crossing class does not pay the full range $y<P^-(q)\le y^2$ in this limit. These limits concern one fixed target at a time, with no target averaging. More precisely the limits are valid with either limsup or liminf in the first variable.

## 1. Values of the entire high residual

On $\mathcal C$, $m$ has at least two distinct factors, and $m\le y^2$ (use any $r|m$). The low terms $t\le y$ are precisely the proper divisors of the squarefree $m$. The sum of $\mu(t)\log(q/t)$ over **all** $t|m$ vanishes since $m$ has at least two prime labels. As $q$ is not a prime power, $R(q)=\mu(m)\log(q/m)$. In particular the signs of odd-rank and even-rank profiles both enter the calculation. Repeated prime factors of $q$ do not invalidate this identity. On $\mathcal D_h$ the only low divisor is 1, so $R(q)=\Lambda(q)-\log q$. The sum of the $\Lambda(q)$ correction over these composite rows is $P^{1/2+o(1)}$, using the number of proper powers and $W\ll_K L^K$. No discarded prime rows contribute to this correction.

## 2. The genuine fixed-target progression sieve

For fixed $m$ of the specified shape, impose $m|q$ and sieve $q$ against all primes $r\le y$ except those dividing $aPm$, in progression $p\equiv P\bmod m$, $p\equiv P-1\bmod a$. We take $(m,P)=1$; any exceptional source $p|P$ costs $P^{o(1)}$ even after absolute divisor counting. All tag primes are $<z$ for large $P$, hence disjoint from $m$; at such primes $q=1$ already. The conditional density at a sieving prime is $1/(r-1)$ (2 is excluded since $P$ is even). The main for the logarithmically weighted prime source in this progression, including the sieve product, is
$$
 \frac{|I|}{\phi(a)}V_{aP}(y)\prod_{r|m}\frac1{r-2},\qquad
 V_{aP}(Y)=\prod_{r\le Y,r\nmid aP}(1-1/(r-1))
  =(1+o_g(1))\frac{e^{-\gamma_E}\mathfrak S(P)}{\log Y}\quad(Y=y,y^h).
 \tag{3}
$$
Indeed $1/\phi(m)$ is the base density multiplier and each label in $m$ removes one factor from $V$. This counts *all* valuations at those primes; sieving $q/m$ at them without correction would be different. Source primes dividing $P$ and forbidden target labels have negligible cost; for the harmonic model $\sum_{r|P,r>z}1/r\ll L/z$. The elementary Euler product comparison in (3) is uniform in $a,P$; excluded tag factors cost $O_K(\exp(-L^{.1}))$. Average over $a$ with the stated normalization.

Use linear upper/lower sieves at level $D=P^{.30}$. The relative discrepancy of either model bound from 1 is at most $\Delta(s)+o_{g,h,\epsilon}(1)$, where $s=\log D/\log Y$ and
$$
 \Delta(s)=F(s)-f(s)=\frac{2e^{\gamma_E}}s\rho(s-1)\quad(s\ge2).
$$
Here $f,F$ denote the classical dimension-one limiting sieves. This follows by subtracting the differential-delay equations $(sF)'=f(s-1)$, $(sf)'=F(s-1)$ beyond the respective initial intervals, with $s(F-f)=2e^{\gamma_E}$ on $1\le s\le2$; $f\le1\le F$. See [Friedlander–Iwaniec's linear/beta-sieve theorem as stated in Kurlberg–Lester–Rosenzweig, §2.1](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136), or *Opera de Cribro*, Ch. 11. The required dimension bound is uniform: the product over any subset of the full odd primes in $[v,w)$ is no larger than the full product, itself at most $(\log w/\log v)(1+O(1/\log v))$ by Mertens, uniformly for $w\ge v\ge2$. The case of the finitely many small sieving primes is absorbed in the absolute dimension constant.

The total progression remainders are $O_A(PL^{-A})$ for every fixed $A$, **even under the absolute sum** over $a,m$ and sieve moduli $j$. The combined unit modulus $amj\le P^{2g+.30+o(1)}$ has fixed slack below the ordinary Bombieri–Vinogradov level and at most $\tau(amj)^{O(1)}$ reconstructions; bounded sieve coefficients suffice. Cauchy using the trivial discrepancy $O(L(P/k+1)+P/\phi(k))$ pays these divisor powers against the arbitrary-log BV bound with maximal residues/prefixes. Replacing $\Lambda(p)$ by true primes costs a power saving after summing these moduli using their slack. Endpoint logs $\log(q/m)=L(1-\log m/L)+O(1)$ on the central range; the $O(1)$ uses the positive upper sieve and is $o_{g,\epsilon}(X_P)$ even after the sum over $m$. The same applies to $\log q=L+O(1)$ in the two rough counts for $\mathcal D_h$.

Consequently on $\mathcal C$ the signed normalized main (in units $X_Pe^{-\gamma_E}/g$) is the limiting signed harmonic sum of $1-\log m/L$ with sign $\mu(m)$. Its absolute error is at most $\epsilon^{-1}\Delta(.30/g)+o_{g,\epsilon}(1)$: every $m$ uses only labels $z<r\le y$, so its unsigned model mass is bounded by $\prod_{z<r\le y}(1+1/(r-2))=\epsilon^{-1}(1+o_{g,\epsilon}(1))$. The $O(1)$ physical log shift and $\phi(a)$ normalizer contribute only vanishing error at fixed cuts. For $\mathcal D_h$ the two true rough counts at $y$ and $y^h$ give signed normalized main $-(1-1/h)$ and absolute error at most $\Delta(.30/g)+h^{-1}\Delta(.30/(gh))+o_{g,h}(1)$. This subtraction does not assume asymptotic prime-pair abundance.

## 3. All signed crossing ranks in one integral

Write $x_i=\log(r_i)/\log y\in(\epsilon,1]$ for the distinct labels of $m$. Fixed-cut reciprocal prime measures converge to $dx/x$ there. Replacing $1/(r-2)$ by $1/r$ in the product, removing repetitions in product integrals, or restoring labels dividing $P$ changes the compact-range harmonic model by $o_{g,\epsilon}(1)$ from $\sum_{r>z}r^{-2}$ and $L/z$. Only finitely many labels ($\le2/\epsilon$) occur for fixed cuts; boundaries of the log polytopes have measure zero. Choose the unique least label, with exponent $a$ (in this paragraph $a$ is a real variable, not a tag integer). Write $s$ for the sum of the **other** exponents divided by $a$, and $v=1/a$. The crossing condition is exactly $v-1<s\le v$, with other scaled coordinates at least 1. Their upper limit $v$ is automatic since their sum is $\le v$. The other labels are unordered, so the $j$-fold integrals have factor $1/j!$.

The signed measure of those other exponents is $d\mathcal D(s)=\delta_0+\rho'(s)ds$, the convolution exponential of $-\mathbf1_{s\ge1}ds/s$. Indeed its cumulative equals 1 up to 1 and satisfies $s\rho'(s)=-\rho(s-1)$ by distinguishing a boundary coordinate, as in the pooled inversion. The marked least label contributes a minus sign. Since $v>1$ except at a measure-zero endpoint, the zero atom lies outside the interval. Thus the crossing main is $C_0(\epsilon)-g C_1(\epsilon)$, with
$$
 C_0(\epsilon)=\int_\epsilon^1[\rho(1/a-1)-\rho(1/a)]\,\frac{da}a,
 \quad
 C_1(\epsilon)=\int_\epsilon^1\frac{da}a\int_{1/a-1}^{1/a}a(1+s)[-\rho'(s)]ds.\tag{4}
$$
In particular $C_0\le C_1\le2C_0$ since $1<a(1+s)\le1+a\le2$ there. The positivity of this final measure results from summing the genuine alternating ranks, not from dropping odd ones.

Changing variables and using $v\rho'(v)=-\rho(v-1)$ gives
$$
 C_0(\epsilon)=1-\rho(1/\epsilon)-\int_1^{1/\epsilon}\rho(v)\,dv/v .
$$
The usual factorial decay follows from $v\rho(v)=\int_{v-1}^v\rho(s)ds$, monotonicity and positivity. Thus if $\epsilon=g\downarrow0$, the linear-sieve gaps times $1/\epsilon$ vanish, $gC_1\to0$, and (2) follows. For the strict upper $h_*<2$, $\rho(v)=1-\log v$ on $[1,2]$ and $\rho'(v)=-\rho(v-1)/v>-1/v$ on $(2,e)$, so the integral exceeds $\int_1^e(1-\log v)dv/v=1/2$.

## 4. A rational check for the concrete surplus and its limitation

On $1\le v\le2$ the integral for $C_0$ contributes $(\log 2)^2/2$. On $2\le v\le3$ use
$$
 \rho(v-1)-\rho(v)=\int_{v-1}^v\rho(s-1)ds/s
 \ge \log(2/(v-1))+(1-\log(v-1))\log(v/2).
$$
For the eight subintervals $[l,r]=[2+(i-1)/8,2+i/8]$, replace $v-1$ on the right by $r-1$ and $v/2$ by $l/2$ for a lower bound, multiply by $\log(r/l)$ and sum. The companion **check.py** uses rational lower/upper atanh-series bounds for each logarithm and verifies $C_0>.389$ whenever $\epsilon\le1/3$. (The computations are unaffected by Python optimization.) This also gives $h_*>3/2$.

For $g=\epsilon=.01$, $h=1.5$ the two sieve parameters are 30 and 20. At integral $j$, $\rho(j)\le1/j!$ by the integral identity. Hence $\Delta(s)\le4/[s(s-1)!]$, using $e^{\gamma_E}<2$ (for instance $\gamma_E<H_5-\log5<\log2$). In units $X_P$ the sum of model errors has limsup less than $10^{-6}$. With $e^{-\gamma_E}>1/2$ the certified net lower is at least
$$
 \frac{(1-2g)\cdot .389-(1-1/h)}{2g}-10^{-6}>2.3.
$$
This proves (1). The non-minimal crossings, small-factor profiles that do not cross, rows with exactly one factor $\le z$, and rows with $P^-(q)>y^h$ have **not** been paid by this comparison; some of these can be adverse. If there are no prime pairs, the total high residual equals the negative of the complete small-$t$ sum up to negligible powers, by the exact inversion. Thus this positive reserve would force a still larger net debit on the remaining rows; it is not a contradiction. No claim on Goldbach or on a sign of the omitted part follows.
