# A signed small-prime model for both neighbors of a prime

Small prime powers dividing $p-1$ and $p+1$ can be modeled jointly, but treating the two complete small-prime records as independent makes a persistent error. For primes up to a subpower cutoff, a correct model uses independence **across the local primes**, not between the two signs at the same prime. We prove total-variation approximation for this signed record and evaluate exactly the distance from the product of its marginals. This is a statement about distributions of shifted integers. It says nothing about factor recovery or the largest prime factors of $p\pm1$.

## Results

Let $p$ be uniform among primes in $(x,2x]$, $3\le y\le x$, and $u=\log x/\log y$. Define the signed record
$$
X_{x,y}=\big((v_\ell(p-1),v_\ell(p+1))\big)_{\ell\le y},
$$
where all cutoff indices $\ell$ are primes. For each $\ell$ choose a uniform $\ell$-adic unit $U_\ell$, independently across $\ell$, and put
$$
Z_y=\big((v_\ell(U_\ell-1),v_\ell(U_\ell+1))\big)_{\ell\le y}.
$$
Uniform unit means that for every $k\ge1$, reduction modulo $\ell^k$ is uniform among the $\varphi(\ell^k)$ units there. Infinite valuations under this distribution have probability zero.

**Signed approximation.** For every fixed $B>0$ and some absolute $c>0$, for sufficiently large $u$,
$$
d_{\rm TV}(X_{x,y},Z_y)
\ll_B \exp\!\big(-c u\min(\log u,\log y)\big)+(\log x)^{-B}.
\tag{1}
$$
In particular, the signed model holds when $y=x^{o(1)}$, with no need to recover the signs from the scalar valuations of $p^2-1$.

**Exact dependence.** Use $\mathsf I(Z_y)$ for the law obtained by drawing the minus record and the plus record independently, with their correct marginal laws. Then
$$
 d_{\rm TV}(Z_y,\mathsf I(Z_y))
 =1-\frac14\prod_{5\le\ell\le y}\left(1-\frac1{(\ell-1)^2}\right).
\tag{2}
$$
For $X_{x,y}$ the same formula holds with additive error at most $3d_{\rm TV}(X_{x,y},Z_y)$. When $y\to\infty$ with $y=x^{o(1)}$, the right side tends to a constant about $0.780$. Removing all $\ell\le L$, by contrast, gives the sharp model-scale estimate
$$
 d_{\rm TV}(Z_{(L,y]},\mathsf I(Z_{(L,y]}))
 =(2+o(1))\sum_{L<\ell\le y}\frac1{(\ell-1)^2}
 =\Theta\!\left(\frac1{L\log L}\right)
 \qquad (L\to\infty,\ y\ge 2L).
\tag{3}
$$
Here the notation $(L,y]$ projects to those local primes. For the actual prime records the same approximation has the additive error supplied by (1); the relative asymptotic requires that error to be smaller than the displayed scale.

## Proof of (1): sieve a fixed signed record

A model-supported record assigns, at each $\ell\ge3$, either $(0,0)$ or a positive power on just one side. At $2$ it assigns one side exactly $1$ and the other some exponent at least $2$. A record at $3$ has exactly one positive side, as any unit is $1$ or $-1$ modulo $3$. For each record $v$ let
$$
d(v)=\prod_{\ell\le y}\ell^{h_\ell},\qquad h_\ell=\max(v^-_\ell,v^+_\ell).
$$
Each active prime $\ell$, meaning $h_\ell>0$, has a specified sign and demands the corresponding residue $p\equiv1$ or $-1\bmod\ell^{h_\ell}$. These demands form a single reduced residue class $a\bmod d$, where $d=d(v)$. To impose the **exact** record, exclude the following bad local events in that class:

- At an active $\ell$, exclude a lift to the same sign modulo $\ell^{h_\ell+1}$; its conditional fraction for model units is $1/\ell$. Given the base congruence, the other sign's valuation is already fixed.
- At an inactive $\ell$, exclude both residues $1,-1\bmod\ell$, of conditional total fraction $2/(\ell-1)$. Inactive primes are at least $5$.

Write these fractions $g_v(\ell)$ and extend them multiplicatively to squarefree products. By the Chinese remainder theorem, for any squarefree $e$ on primes up to $y$, the base congruence together with all bad events at primes dividing $e$ is a union of reduced residue classes modulo $de$. Its model mass is $g_v(e)/\varphi(d)$. In particular the model mass of the exact record is
$$
q_v=\varphi(d)^{-1}\prod_{\ell\le y}(1-g_v(\ell)).
\tag{4}
$$

Put $T=D=\lfloor x^{1/8}\rfloor$ and initially restrict to $d\le T$. Let $M=\pi(2x)-\pi(x)$ and
$$
E(m)=\max_{(a,m)=1}\left|\pi(2x;m,a)-\pi(x;m,a)-M/\varphi(m)\right|.
$$
Apply the lower fundamental-lemma sieve of Brun–Hooley with level $D$ to these bad events for the fixed record $v$. Indeed, uniformly in $v$, $g_v(\ell)\le 2/(\ell-1)$ for $\ell\ge5$, and the $2,3$ factors are bounded. Comparison to $(1-1/\ell)^{-2}$ gives the needed sieve-dimension-two bound
$$
\prod_{w\le\ell\le z}(1-g_v(\ell))^{-1}
 \le \left(\frac{\log z}{\log w}\right)^2 \exp(O(1/\log w))
 \qquad (2\le w\le z\le y).
$$
For $\ell\ge5$ each local ratio to $(1-1/\ell)^{-2}$ is at most $1+O(\ell^{-2})$, and Mertens' product estimate gives the main factor. The fundamental lemma thus supplies squarefree weights of absolute value at most one supported on $e\le D$, with relative model error $O(\exp(-c_1 u\log u))$ since $\log D/\log y\asymp u$. The sequence being sieved is the uniform prime measure restricted to the base residue class; for each prime in the sequence, use the product of the local primes at which its bad event occurs. This realizes the events of divisibility by $e$ required by the sieve. As a result,
$$
(q_v-\Pr(X_{x,y}=v))_+
 \ll q_v\exp(-c_1 u\log u)
       +M^{-1}\sum_{\substack{e\le D\\e\text{ supported}}}
          \sum_{\text{classes for }(v,e)} E(de).
\tag{5}
$$
No equidistribution is presumed after restricting to the base residue class; its error is still included through $E(de)$, also for $e=1$.

We can sum error (5) over **all** signed records with $d\le T$. For fixed $m=de$, at each prime power in $m$ there are at most two choices for whether the prime appears in the squarefree $e$. This fixes the exponent in $d$. If this exponent is positive there are at most two signs, and the imposed lift, if present, is unique. If this exponent is zero, there are at most two choices for the bad residue. Thus the number of contributions to $E(m)$ is at most $4^{\omega(m)}$. The quantitative use of both signs ends here; forgetting the signs before counting would not prove (5).

By Bombieri–Vinogradov, $\sum_{m\le x^{1/4}}E(m)\ll_A x/(\log x)^A$ for every fixed $A$, in the centered interval form shown above. Indeed one subtracts the estimates at $2x$ and $x$, replaces the logarithmic integral main term by $M$ using the prime number theorem with logarithmic savings, and sums $1/\varphi(m)$, whose sum up to $x$ is $O(\log x)$. The elementary bound $E(m)\ll x/\varphi(m)$ and an Euler product give
$$
 \sum_{m\le x^{1/4}}16^{\omega(m)}E(m)
 \ll x\prod_{\ell\le x^{1/4}}
       \left(1+\frac{16\ell}{(\ell-1)^2}\right)
 \ll x(\log x)^{16}.
$$
Cauchy–Schwarz and $M\asymp x/\log x$ then yield
$$
 M^{-1}\sum_{m\le x^{1/4}}4^{\omega(m)}E(m)
 \ll_B (\log x)^{-B}.
\tag{6}
$$

It remains to bound only the **model** mass of $d>T$, since $d_{\rm TV}=\sum_v(q_v-\Pr(X_{x,y}=v))_+$. Under the model the exponents $h_\ell$ are independent and $\Pr(h_\ell\ge k)\le 2/\varphi(\ell^k)\le4\ell^{-k}$ for $k\ge1$. For $0<t\le1/4$, summing the geometric tail yields $\log\mathbb E[\ell^{t h_\ell}]\ll(\ell^t-1)/\ell$. Consequently, by $\sum_{\ell\le y}(\log\ell)/\ell\ll\log y$,
$$
\log\mathbb E[d^t]\ll t(\log y)\exp(t\log y).
$$
Choose $t=\min\{1/4,\,(\log u)/(2\log y)\}$. Now $\exp(t\log y)\le\sqrt u$, whereas $t\log T\asymp u(t\log y)$. Markov's inequality bounds the tail by $O(\exp(-c_2 u\min(\log u,\log y)))$ for sufficiently large $u$. Together with (5)–(6), this proves (1).

## Proof of (2): the maximizing event is the forbidden support

Write $\mathsf Q$ for the law of $Z_y$ and $\mathsf J=\mathsf I(Z_y)$. Both are independent across the local primes. At $2$ the two model marginals each give valuation $1$ with probability $1/2$, and $\mathsf Q$ requires that exactly one side have valuation $1$. The $\mathsf J$-mass of this support is $1/2$; on each allowed atom, the $\mathsf Q/\mathsf J$ likelihood ratio is $2$, since the probability of a given exponent $k\ge2$ on its specified side is already its marginal probability. At $3$ the same ratio $2$ holds, now with exactly one positive side, each marginal positive with probability $1/2$.

For $\ell\ge5$, put $s_\ell=1/(\ell-1)$. Both marginal active probabilities equal $s_\ell$; the model never has both active. At the atom $(0,0)$ the likelihood ratio is
$$
\frac{1-2s_\ell}{(1-s_\ell)^2}=1-\frac1{(\ell-2)^2},
$$
and at any allowed atom with one positive side it is $1/(1-s_\ell)>1$. Over the full allowed support the ratio is therefore at least
$$
4\prod_{\ell\ge5}\left(1-\frac1{(\ell-2)^2}\right)
 \ge 4\prod_{k\ge3}(1-k^{-2})=\frac83>1.
$$
Thus all deficits of model mass relative to the independent marginals occur outside its support. The $\mathsf J$-probability of that complement is the right side of (2), proving exactness. For any two laws of pairs, the distance between their products of marginals is at most the sum of the distances between corresponding marginals, and projection cannot increase distance. This gives the stated $3d_{\rm TV}(X,Z)$ error.

## Proof of (3): the tail has two leading contributions

For $\ell\ge5$ each single-prime distance from its independent marginals is $2s_\ell^2$: the independent law has an excess $s_\ell^2$ on $(0,0)$ and another $s_\ell^2$ on the events with both sides positive. At one-positive atoms the model is larger. The product inequality bounds the full tail distance by $2\sum s_\ell^2$.

For the matching lower bound keep just $L<\ell\le Y=\min(y,L(\log L)^2)$. The sum of the $s_\ell$'s in this subwindow is $o(1)$, by the prime harmonic-sum bound. Define two disjoint events: every prime in that subwindow is inactive on both sides, or some prime there is active on both sides. For the first event the excess of the independent law is
$$
\prod_{L<\ell\le Y}(1-s_\ell)^2
 -\prod_{L<\ell\le Y}(1-2s_\ell)
 =(1+o(1))\sum_{L<\ell\le Y}s_\ell^2 .
$$
This follows by expanding the ratio of the products, whose local differences are $s_\ell^2$, with both products $1-o(1)$. The second event is forbidden by the model and has independent mass $1-\prod(1-s_\ell^2)=(1+o(1))\sum_{L<\ell\le Y}s_\ell^2$. Their union gives the lower bound. The discarded square sum is $o(1/(L\log L))$ by the prime number theorem or Chebyshev and partial summation, while $L<\ell\le2L$ provides a lower bound of this order by the prime number theorem. This proves the relative claim uniformly in $y\ge2L$.

## Sources and scope

- [Ford, *Poisson approximation of prime divisors of shifted primes*](https://arxiv.org/abs/2408.03803) proves a sharp scalar approximation for one shift. [Gorodetsky, *A Kubilius model for sieve-theoretic sequences*](https://arxiv.org/abs/2608.14190), §§3–4, supplies the version of the Brun–Hooley lemma used here (Proposition 3.1 / Corollary 3.2) and the one-sided total-variation proof template. Applying the scalar result to $p^2-1$ does not retain the signs; the residue classes and the summed signed error are the added steps.
- [Bombieri, *On the large sieve*](https://doi.org/10.1112/S0025579300005313) is the classical source of the mean distribution estimate used in (6).
- The local independence across distinct primes comes from CRT and mean equidistribution of primes in residue classes; it does not justify replacing $p-1$ or $p+1$ by an unrestricted random integer, or extrapolating to fixed power cutoffs. Equations (2) and (3) compare to the correct separate marginals.
- The companion [exact finite audit](verify_signed_prime_neighbors.js) checks local and joint support, the exact product formula, and the residue-class multiplicity inequality on small CRT moduli. These tests do not prove the analytic equidistribution or sieve lemma.
