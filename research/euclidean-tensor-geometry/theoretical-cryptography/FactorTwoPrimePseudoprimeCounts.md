# Counting two-prime Fermat pseudoprimes by the exact common divisor

Let $A\ge2$ be an integer base. Count only products $N=pq$ of **distinct** primes with $A^{N-1}\equiv1\pmod N$. This note improves two explicit upper bounds for the base-2 counts in Luca, Ralaivaosaona and Jiménez Urroz (2025). The proof groups pairs by the exact value of $\gcd(p-1,q-1)$, rather than squaring the size of the pool of all primes with small order. For the unrestricted count, a two-form upper-bound sieve controls the large-divisor tail.

**Theorem.** For every fixed $C>0$, uniformly for $2\le A\le x^C$,
$$
\#\{pq\le x:p<q,\ A^{pq-1}\equiv1\bmod pq\}
 \ll_C \frac{\sqrt{\log A}\,x^{3/4}}{(\log x)^{5/4}}.
\tag{1}
$$
For every fixed $C>0$ and $0<\eta\le1$, uniformly for $z^\eta\le H\le z$ and $2\le A\le z^C$,
$$
\#\{z<p<q\le z+H:A^{pq-1}\equiv1\bmod pq\}
 \ll_{C,\eta}\frac{\sqrt{\log A}\,H^{3/2}}{(\log z)^2}.
\tag{2}
$$
In particular, for $H=z$ and $A=2$, the prior upper bound $O(z^{8/5}/(\log z)^2)$ becomes $O(z^{3/2}/(\log z)^2)$. In (1), the prior base-2 bound was $O(x^{4/5}/(\log x)^{2/5})$. For base 2, the congruence $2^{N}\equiv2\bmod N$ is equivalent to the one used here when $N$ is odd. An even product $2q$, with $q$ an odd prime, does not satisfy the former congruence: modulo $q$ the exponent $2q-1$ is $1$ modulo $q-1$, so $2^{2q-1}\equiv2\not\equiv1\bmod q$. Thus the base-2 comparison counts the same distinct-prime products. If the unrestricted comparison also includes squares of primes, their trivial $O(\sqrt x)$ count is absorbed by (1).

These are upper bounds on a number-theoretic family, not asymptotic formulas, algorithms for recovering prime factors, or worst-case primality-test guarantees. All logarithms are natural.

## Small common divisor: the shared integer for each bin

Put $d=\gcd(p-1,q-1)$. The exact relation is
$$
A^{pq-1}\equiv1\bmod pq\quad\Longleftrightarrow\quad pq\mid A^d-1.
\tag{3}
$$
Indeed, either condition gives $\gcd(A,pq)=1$. Modulo $p$, the order of $A$ divides $p-1$ and must divide $pq-1$ if the left side holds. The greatest common divisor of these two exponents is $\gcd(p-1,q-1)=d$. Do the same at $q$. Conversely, $d\mid pq-1$, since both primes are $1$ modulo $d$.

For **each fixed** $d$, both primes must divide a single integer $A^d-1$. The number of its distinct prime divisors that are at least $U>1$ is at most $d\log A/\log U$, by multiplying them. Each admissible prime is at least $d+1$; in (2) it is also at least $z$. Hence the contribution of $d\le T$, respectively in (1) and (2), is at most
$$
\ll (\log A)^2\,T^3/(\log(T+1))^2,\qquad
\ll (\log A)^2\,T^3/(\log z)^2.
\tag{4}
$$
For the first bound, sum $d^2/\log^2(d+1)$, splitting at $\sqrt T$. This is the step yielding a power saving over a union of all small-order primes: pairs from different bins are not multiplied together.

## Large common divisor inside a window

Write $W(k)=\prod_{\ell\mid k}(1-1/\ell)^{-2}$ for $k\ge1$, with products over primes. For any fixed $j>0$ the mean $\sum_{k\le V}W(k)^j\ll_j V$ is bounded. In fact, expand $W(k)^j=\sum_{b\mid k}w_j(b)$, where $w_j$ is supported on squarefree integers with prime factors $w_j(\ell)=(1-1/\ell)^{-2j}-1=O_j(1/\ell)$. Summing first over $b$ bounds the mean by $V\prod_\ell(1+w_j(\ell)/\ell)$. In particular $\sum_{d>T}\varphi(d)^{-2}\ll T^{-1}$, by dyadic summation.

In (2), $d\le q-p\le H$. For $T<d\le H^{3/4}$, Brun–Titchmarsh for an interval of length $H$ gives $\ll H/(\varphi(d)\log H)$ candidates for each prime in the class $1\bmod d$. Summing the squared bound gives $O(H^2/(T\log^2 H))$. For $d>H^{3/4}$, there are at most $1+H/d\le2H/d$ candidates, giving $O(H^{5/4})$. Take
$$
T=\sqrt{H/\log A}.
$$
For $A\le z^C$, this lies between $2$ and $H^{3/4}$ for large $z$. The logs of $H$ and $z$ are comparable, and $H^{5/4}$ is lower order because $H\ge z^\eta$. Together with (4) this proves (2). There is also a small-width exclusion: if $H\log A\le2\log z$, no such pair exists, since $pq>z^2$ would have to divide $A^d-1<\exp(d\log A)\le z^2$.

## Large common divisor without a balance constraint

Drop condition (3) for $d>T$ and write $p=rd+1,\ q=sd+1$ with $1\le r<s$. In a block $D<d\le2D$, the condition $pq\le x$ implies $rs\le x/D^2$. We need the following two bounds:
$$
\begin{aligned}
\#\{D<d\le2D:rd+1,\ sd+1\text{ prime}\}
 &\ll \frac{D}{(\log D)^2}W(2rs(s-r)),\\
\sum_{\substack{rs\le V\\1\le r<s}} W(2rs(s-r))
 &\ll V\log(2V).
\end{aligned}
\tag{5}
$$
The first inequality is the elementary two-form Selberg sieve; a proof with uniform constants is given below. To see the second, use $W(2rs(s-r))\le W(2)W(r)W(s)W(s-r)$ and Hölder. Each of the three sums of cubes is $O(V\log(2V))$. For the $r$ and $s$ sums, enlarge to the full hyperbola, then use $\sum_{t\le V}W(t)^3/t\ll\log(2V)$ by the bounded mean. For the $s-r$ sum, fix $r\le\sqrt V$ and apply the bounded mean to the $s-r$ values, which are at most $V/r$; then sum over $r$.

If $T\ge x^{1/5}$, (5) shows that the number for one block is
$$
\ll \frac{D}{\log^2 D}\,\frac{x}{D^2}\log(2x/D^2)
 \ll \frac{x}{D\log x}
$$
whenever $D\le\sqrt x$. No other blocks contribute. Sum over $D=T,2T,\ldots$ to get $O(x/(T\log x))$. Now take
$$
 T=x^{1/4}(\log x)^{1/4}/\sqrt{\log A}.
$$
The assumed range of $A$ ensures $T\ge x^{1/5}$ for all sufficiently large $x$ and $\log T\asymp\log x$. The small-divisor bound (4) and the dyadic tail are both $O(\sqrt{\log A}\,x^{3/4}/(\log x)^{5/4})$, as required.

### Uniform sieve detail for (5)

Put $B=2rs(s-r)$. For every prime $\ell\nmid B$, the product $(rd+1)(sd+1)$ has exactly two distinct roots modulo $\ell$. Let $L=D^{1/8}$, and use only primes $\ell\le L$ coprime to $B$. For squarefree $k$ composed of these primes let $g(k)=2^{\omega(k)}/k$ and $h(k)=\prod_{\ell\mid k}g(\ell)/(1-g(\ell))$. The number of $d$ in the interval where $k$ divides the product is $Dg(k)+O(2^{\omega(k)})$, by the Chinese remainder theorem.

For sieve weights $\rho_k$ supported on those $k\le L$ with $\rho_1=1$, the square of the sum of the weights over divisors majorizes the indicator of surviving the sieve. The main term is $D$ times
$$
\sum_{k,j}\rho_k\rho_j g([k,j])
 =\sum_m h(m)^{-1}\left(\sum_{m\mid k}g(k)\rho_k\right)^2.
$$
Here $[k,j]$ is the least common multiple; the identity follows by expanding $1/g(\gcd(k,j))=\sum_{m\mid\gcd(k,j)}1/h(m)$. Write $G=\sum_{m\le L}h(m)$ on the supported integers. Choose the inner sums to be $\mu(m)h(m)/G$ for $m\le L$ and zero above $L$, using Möbius inversion; the main term is then $D/G$. Inverting also yields
$$
 \rho_k=\frac{\mu(k)}{G}\frac{h(k)}{g(k)}
  \sum_{\substack{j\le L/k\\(j,k)=1}} h(j),\qquad |\rho_k|\le1.
$$
For the last inequality, $h(k)/g(k)=\prod_{\ell\mid k}(1+h(\ell))=\sum_{v\mid k}h(v)$; each product $vj$ is a distinct term in $G$. The errors therefore sum to $O(\sum_{k,j\le L}2^{\omega([k,j])})=O(L^4)$, since $2^{\omega([k,j])}\le kj$. The two prime values being counted are larger than $L$, so they survive the sieve.

For an absolute small $\kappa>0$, put $w=L^\kappa$. Consider only squarefree products $m$ of primes $\ell\le w$ coprime to $B$, weighted by $\prod_{\ell\mid m}2/\ell$, which is bounded by $h(m)$. The total weight is $Z=\prod_{\ell\le w,\ell\nmid B}(1+2/\ell)$. As a probability distribution after normalization, the mean of $\log m$ is at most $2\sum_{\ell\le w}(\log\ell)/\ell=O(\log w)$ by Chebyshev's bound and partial summation. Choose $\kappa$ so this is at most $\tfrac12\log L$. Markov's inequality gives at least $Z/2$ weight on $m\le L$. The product over all primes up to $w$ satisfies $\prod_{\ell\le w}(1+2/\ell)\gg(\log w)^2$, by comparison with $\prod_{\ell\le w}(1-1/\ell)^{-2}$ and the harmonic sum; the comparison factors differ from one by $O(\ell^{-2})$. Removing primes dividing $B$ costs at most $W(B)$. Thus $G\gg(\log D)^2/W(B)$. The error $O(L^4)=O(\sqrt D)$ is absorbed, proving (5) uniformly in $r,s$.

## Relationship to prior work and finite checks

- [Luca, Ralaivaosaona and Jiménez Urroz, *On pseudoprime RSA moduli*, Afrika Matematika 36, 118 (2025)](https://doi.org/10.1007/s13370-025-01338-1), Theorems 2.1 and 3.1, is the direct comparison. Their common-divisor and small-order conditions appear in the proof; retaining the exact bin for both primes is the refinement here. There is no claim of an optimal exponent.
- [Li and Pomerance, *Fermat pseudoprimes*](https://math.dartmouth.edu/~carlp/evenpsps041025.pdf) addresses general composites with a different uniform-base question. The distinct-two-prime promise is essential to (3).
- [Montgomery and Vaughan, *The large sieve*](https://doi.org/10.1112/S0025579300004708) is the source for the short-interval Brun–Titchmarsh inequality. For the standard Selberg identity used in (5), compare [Kedlaya, *Notes on analytic number theory*, Theorem 13.1](https://kskedlaya.org/ant/chap-selberg.html); the weighting and bounds in the specialization are given above.
- The companion [exact finite checks](verify_two_prime_pseudoprime_counts.js) test the arithmetic equivalence, the small-bin counting inequality without floating-point logarithms, and the local root counts. The checks are restricted to small preselected ranges and emit only aggregate counts. None are used as a premise of the asymptotic proof.
