# Almost-injectivity of Carmichael's exponent on balanced semiprimes

For $X\ge 3$ let
$$
\mathcal S_X=\{pq:X<p<q\le2X,\ p,q\ \text{prime}\},
\qquad
F_X(m)=\#\{N\in\mathcal S_X:\lambda(N)=m\},
$$
where $\lambda$ is the Carmichael function. In this set $\lambda(pq)=\operatorname{lcm}(p-1,q-1)$.

**Theorem.** Unconditionally,
$$
\sum_m F_X(m)\big(F_X(m)-1\big)
 \ll \frac{X^2}{(\log X)^3}. \tag{1}
$$
In particular, for sufficiently large $X$ and $N$ uniform on $\mathcal S_X$, the expected number of **other** elements of $\mathcal S_X$ with the same exponent is $O(1/\log X)$. The probability that an exponent fails to distinguish its input within $\mathcal S_X$ is at most this, and
$$
\#\lambda(\mathcal S_X)
 = \#\mathcal S_X-O\big(X^2/(\log X)^3\big)
 \sim \frac{X^2}{2(\log X)^2}.
$$
More precisely the deficit is at most half the left side of (1). The conditional entropy in nats is
$H(N\mid\lambda(N))=\mathbb E\log F_X(\lambda(N))=O(1/\log X)$, since $\log t\le t-1$ for $t\ge1$.

This is a statement about the restricted image and fibers, not about uniqueness among all positive integers, and not an exponent-computation, inversion, or factor-recovery algorithm.

## Uniform estimates used in the proof

Write $V(n)=n/\varphi(n)$ for positive $n$. We use the following standard two-form consequence of the Selberg upper-bound sieve. If $\alpha,\beta$ are distinct positive integers, $X^\eta\le T\ll X$ for a fixed $\eta>0$, and $J$ is any interval of length $O(T)$, then
$$
\#\{t\in J\cap\mathbb Z:
\alpha t+1,\ \beta t+1\text{ are both prime and }>X\}
 \ll_\eta \frac{T}{(\log X)^2} V(\alpha\beta|\alpha-\beta|)^2. \tag{2}
$$
Indeed, at an odd prime $\ell\nmid\alpha\beta(\alpha-\beta)$ there are exactly two excluded residues. Drop all restrictions at the other primes, including $2$. For a squarefree divisor $d$ supported on the retained primes, the count in the excluded classes is the interval length times $2^{\omega(d)}/d$, with error $O(2^{\omega(d)})$. The Selberg upper bound at a sufficiently small fixed power of $T$ gives the corresponding local product times $O(T)$; all the counted primes exceed the sieve cutoff. Relative to the product over all odd primes below the cutoff, the loss is at most $\prod_{\ell\mid\alpha\beta(\alpha-\beta),\,\ell>2}(1-2/\ell)^{-1}\ll V(\alpha\beta|\alpha-\beta|)^2$. Mertens' estimate supplies the two logarithms. One may use the same two-form sieve as in [Soundararajan–Xu, Section 6](https://arxiv.org/abs/2212.06098); the residue counts and their errors are independent of the interval's location and of the coefficient sizes.

We also record an elementary estimate to average the factors in (2). For a fixed integer $j\ge1$, write
$$
V(n)^j=\sum_{d\mid n} c_j(d),\qquad
c_j(\ell)=(1-1/\ell)^{-j}-1=j/\ell+O_j(\ell^{-2}),
$$
where $c_j$ is multiplicative and supported on the squarefree integers. As a result,
$$
\sum_{d\ge1}\frac{c_j(d)}{d}\ll_j 1,\qquad
\sum_{d\le Z}c_j(d)\ll_j (\log(2Z))^j,\qquad
\sum_{n\le T}V(n)^j\ll_j T. \tag{3}
$$
The first two follow by Euler products; the third follows by counting multiples of $d$ and using the first. For integers $a\ne0,b$ and an interval of length $O(T)$,
$$
\sum_{\substack{t\text{ in the interval}\\0<|at+b|\le Z}}V(|at+b|)^j
 \ll_j T V(\gcd(|a|,|b|))^j+(\log(2Z))^j. \tag{4}
$$
For a squarefree $d$ with $\gcd(a,d)\mid b$, the divisibility constraint restricts $t$ to one residue class modulo $d/\gcd(a,d)$, giving at most $O(T\gcd(a,d)/d+1)$ possibilities; otherwise it gives zero. The Euler product of the main-term divisor sum has a factor $1+c_j(\ell)$ for $\ell\mid\gcd(a,b)$, a factor $1+c_j(\ell)/\ell$ for $\ell\nmid a$, and $1$ otherwise. The error follows from (3). Inputs with $at+b=0$ are excluded.

For later use, let $u,v$ be positive and comparable with ratio bounded by $16$, $U=\max(u,v)$, and $i\ge1$. For every fixed $0<\sigma<1$,
$$
\sum_{\substack{i,u,v\ge1\\u,v\text{ comparable}}}
 (iU)^\sigma \frac{\tau(u)\tau(v)}{i^2U^3}<\infty. \tag{5}
$$
The $i$ sum converges; the part with $U\asymp 2^k$ is bounded by $O((1+k)^2 2^{-k(1-\sigma)})$ using $\sum_{n\le T}\tau(n)\ll T\log(2T)$. Also $V(n)\ll\log(2n)$ by Mertens' bound, hence any fixed powers of $V(iuv)$ and $V(|u-v|)$ (if $u\ne v$) can be absorbed into $(iU)^\sigma$. The portion without those powers and with $iU>K$ is $O_\sigma(K^{-\sigma})$.

## Collisions involving four different primes

Take two different pairs $(p,q)$ and $(r,s)$ in the defining interval, and write
$$
g=\gcd(p-1,q-1),\quad h=\gcd(r-1,s-1),\quad
g=iu,\quad h=iv,\quad (u,v)=1.
$$
Equality of exponents gives $(p-1)(q-1)/g=(r-1)(s-1)/h$. Since all four shifted primes are between $X/2$ and $2X$, $u$ and $v$ are comparable as in (5).

Put $a=(p-1)/g$, $b=(q-1)/g$, $c=(r-1)/h$, $d=(s-1)/h$. Then $u ab=v cd$ and both $(a,b)$ and $(c,d)$ are $1$. Thus the entire $v$ factors uniquely as $v=v_1v_2$ with $v_1\mid a$, $v_2\mid b$, and $u=u_1u_2$ similarly with $u_1\mid c$, $u_2\mid d$. There are at most $\tau(u)\tau(v)$ choices. After division we have an exact product equality between coprime pairs:
$$
(a/v_1)(b/v_2)=(c/u_1)(d/u_2).
$$
The gcd of $a/v_1$ and $c/u_1$ is a coordinate $A$ of a four-parameter rectangle, and the four reduced entries are $AB, CD, AC, BD$, respectively. This follows by assigning each prime power in the common product to the one entry carrying it on each side. Thus the four primes have the forms
$$
k_1 AB+1,\quad k_2 CD+1,\quad k_3 AC+1,\quad k_4 BD+1,\qquad
(k_1,k_2,k_3,k_4)=(gv_1,gv_2,hu_1,hu_2). \tag{6}
$$
For an upper bound we can discard the residual coprimality conditions on $A,B,C,D$.

Fix $i,u,v,u_1,u_2,v_1,v_2$. In a dyadic block $A_0\le A<2A_0$ the other three coordinates have scales
$$
B_0=\frac{X}{k_1A_0},\qquad
C_0=\frac{X}{k_3A_0},\qquad
D_0=\frac{X}{k_4B_0}.
$$
That is, each is between fixed positive multiples of its scale, by (6) and the ranges of the shifted primes. If any scale is smaller than a fixed positive constant the block is empty; otherwise there are $O(1)$ times the scale many integer choices in each coordinate. The product of the scales is
$$
A_0B_0C_0D_0=\frac{X^2}{h^2u}\ll \frac{X^2}{i^2U^3}. \tag{7}
$$
There are $O(\log X)$ possible values of $A_0$. For $iU>X^{1/20}$, the trivial volume bound times (5) with, say, $\sigma=1/2$ gives a total $O(X^{2-1/40}\log X)$.

For the rest, $1\le k_j\le X^{1/10}$. Since $A_0B_0=X/k_1$, one of $A_0,B_0$ is at least $X^{9/20}$. The ratios $D_0/A_0=k_1/k_4$ and $C_0/B_0=k_1/k_3$ lie between $X^{-1/10}$ and $X^{1/10}$. Consequently either $A,D$ have scales at least $X^{7/20}$ or $B,C$ do. Fix the other two coordinates and apply (2) in each of the two large-scale variables. For example, if $B,C$ are large and $A,D$ are fixed, the coefficient pairs are $(k_1 A,k_4 D)$ and $(k_3 A,k_2 D)$. An equality between coefficients in either pair would give two equal primes, so such choices can be discarded in this four-distinct-prime case.

Here are the details of the averaging of the two sieve losses. Call the fixed variables $R,S$ with scales $R_0,S_0$. They play the roles of $A,D$ or $B,C$. In both orientations the two coefficient pairs can be written as $(k_e R,k_f S)$ and $(k_j R,k_l S)$ for a permutation of the four $k$'s. For each of the admissible $R,S$, by $V(mn)\le V(m)V(n)$, the product of the factors $V(\alpha\beta|\alpha-\beta|)^2$ in (2) is at most
$$
 V(iuv)^8 V(R)^4V(S)^4
 V(|k_eR-k_fS|)^2 V(|k_jR-k_lS|)^2 .
$$
We used that every prime factor of every $k$ divides $iuv$. The arithmetic-geometric mean inequality bounds the last four factors by the average of their fourth powers. Each term $V(R)^{16},V(S)^{16}$ has sum $O(R_0S_0)$ by (3). If $\max(R_0,S_0)\ge(\log X)^{10}$, sum each difference term $V(|kR-k'S|)^8$ along the variable of larger scale by (4), and then sum over the other variable. The linear expression is bounded by $X^{O(1)}$; its progression gcd divides the coefficient of the summed variable, whose prime support is contained in $iuv$. The error per such progression is $O((\log X)^8)$, which is absorbed by its length scale. The sum is thus $O(R_0S_0 V(iuv)^8)$. Including the coefficient factor, the weighted count for a dyadic block is at most
$$
\frac{A_0B_0C_0D_0}{(\log X)^4} V(iuv)^{16}
$$
up to an absolute constant.

It remains to justify not losing anything substantial when both fixed scales are below $(\log X)^{10}$. At most $O(\log\log X)$ blocks have $A,D$ both that small, since $A_0$ runs over powers of $2$. At most $O(\log\log X)$ have $B,C$ both that small: $B_0=X/(k_1 A_0)$ is in a geometric progression and at least an absolute positive constant on a nonempty block. In these blocks use the pointwise $V(n)\ll\log\log(3n)$ for integers $n=X^{O(1)}$, so the two sieve losses are $O((\log\log X)^4)$. The pointwise bound follows, for instance, by splitting the prime divisors at $\log(3n)$, using Mertens below it and $\sum_{\ell\mid n,\ \ell>\log(3n)}1/\ell=O(1)$ above it. The contribution of these blocks, by (5) and (7), is at most $O(X^2(\log\log X)^5/(\log X)^4)$.

Summing the other blocks, absorb $V(iuv)^{16}$ into a fixed positive moment $(iU)^\sigma$ in (5). There are $O(\log X)$ blocks and $\tau(u)\tau(v)$ coefficient splits. This proves the desired $O(X^2/(\log X)^3)$ bound for four distinct primes.

## Collisions sharing one prime

Relabel so that the two pairs are $(p,q)$ and $(p,s)$, with $q\ne s$. Keep $g,h,i,u,v$ as above. Equality of exponents makes
$$
(q-1)/g=(s-1)/h=t\in\mathbb Z_{>0},
\quad q=iu t+1,\quad s=iv t+1,\quad
p\equiv1\pmod {iuv}.
$$
Here $u\ne v$ since $q\ne s$. Ignoring the primality conditions, the count for fixed $i,u,v$ is at most $O(X^2/(i^2uvU))$: count $p-1$ as a positive multiple of $iuv$ up to $2X$ and $t$ up to $2X/(iU)$. For $iU>X^{1/20}$, sum this by (5) with $\sigma=1/2$. For $iU\le X^{1/20}$, the modulus $iuv\le X^{1/10}$, so Brun–Titchmarsh bounds the count of $p$ by $O(X/(\varphi(iuv)\log X))$. Apply (2) to $t$ with scale $X/(iU)\ge X^{19/20}$. This gives an overall coefficient weight bounded by $V(iuv)^3V(|u-v|)^2$ times $O(X^2/(i^2uvU(\log X)^3))$. Sum again by (5). Sharing both primes would give the same unordered pair and is exactly the excluded diagonal. This completes the proof of (1).

## Relation to earlier work and checks

- [Soundararajan and Xu, *Central limit theorems for random multiplicative functions*, Lemma 3.4 and Section 6](https://doi.org/10.1007/s11854-023-0331-y) give an upper bound of order $X^2/(\log X)^3$ for collisions of the **product** of fixed-shift primes. Their parametrization and two-form sieve provide the starting point. Equality of the **least common multiples** requires allowing unequal pairwise gcds, with a summable coefficient cost in (5)–(7); it also allows a shared prime, which the product equation excludes for distinct pairs.
- [Ford–Luca, *The Number of Solutions of* $\lambda(x)=n$](https://arxiv.org/abs/1010.5442) and [Ford–Luca–Pomerance, *The image of Carmichael's* $\lambda$-*function*](https://arxiv.org/abs/1408.6506) concern the unrestricted fibers and range. In contrast, (1) counts collisions only within $\mathcal S_X$. It strengthens the balanced-set bounds in [FactorCarmichaelFibers.md](FactorCarmichaelFibers.md) from a polynomial upper bound on the size-biased mean to a mean tending to one with a quantified rate.
- The analytic prime counting inputs are the Selberg upper sieve, as in the first reference, and [Montgomery–Vaughan, *The large sieve*](https://doi.org/10.1112/S0025579300004708) for Brun–Titchmarsh. No prime-tuple lower bound is used, and no asymptotic for the off-diagonal term itself is claimed.
- [The small checker](verify_factor_carmichael_collision_energy.js) uses only predetermined integer and prime ranges to verify the rectangle parametrization, the exceptional shared-prime relation, and the exact combinatorial count identities. It does not verify the analytic estimates.
