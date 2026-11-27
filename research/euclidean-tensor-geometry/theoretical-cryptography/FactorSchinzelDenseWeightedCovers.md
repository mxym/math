# A positive proportion of lengths admit growing-weight Schinzel covers

In the restricted covering problem of [Bui, Naprienko, Pratt and Zaharescu (BNPZ), Definition 5.3](https://arxiv.org/html/2605.21221#S5.SS1), use a nonzero class $a_p$ for each moved prime $p\le k$, with $a_p>k\bmod p$. Unmoved primes keep their ordinary divisibility contribution. If $R$ is the set of moved primes, the weight of an index $j\in[1,k]$ is
$$
\frac{j}{\prod_{p\in R}p^{v_p(j)}}\prod_{\substack{p\in R\\j\equiv a_p\bmod p}}p.
$$
A cover of weight $B$ means this is at least $B$ at every index.

**Theorem.** There are absolute constants $b,c>0$ such that for all sufficiently large $K$, at least $cK$ different integers $k\in[K,2K]$ have a cover of weight
$$
 B=\left\lfloor b\sqrt{\frac{\log K}{\log\log K}}\right\rfloor.
\tag{1}
$$
Consequently, each of these lengths has a residue class of upper indices $n>k$ in which every term $n-i$ ($0\le i<k$) has a divisor at least $B$ supported on primes not dividing $\binom nk$. In particular none of the $n-i$ divides $\binom nk$ for any $n$ in that class.

BNPZ Proposition 5.5 proves the existence of $K^{1-o(1)}$ lengths at the larger weight $\asymp\log K/\log\log K$. The new conclusion here is **positive proportion** at a smaller but still growing weight. It neither gives that density at the BNPZ weight nor excludes a sparse infinite set of non-prime-power lengths satisfying Schinzel's universal divisibility property.

## 1. Prime reserves for a positive fraction of one progression

Write $L=\log K$, $V=10\sqrt{L\log L}$, $Y=\lfloor e^V\rfloor$ and $H=\lfloor Y/2\rfloor$. Fix a prime $Q\in[B,B^2]$. We will produce covers for at least a fixed positive fraction of the multiples of $Q$ between $K$ and $2K$, with bounds uniform in $Q$. Put
$$
R_Q(k)=\#\{k-H<p<k:\ p\text{ prime},\ p\equiv1\bmod Q\}.
$$
Among uniform multiples $k$ of $Q$ in $[K,2K]$, the first and second moment estimates
$$
\mathbf E R_Q\asymp \frac{H}{QL},
\qquad
\mathbf E R_Q^2\ll \left(\frac{H}{QL}\right)^2
\tag{2}
$$
have absolute implied constants. For the first, write $p=k-h$ and sum each $1\le h<H$ with $h\equiv-1\bmod Q$. The prime number theorem in progressions in the [Siegel–Walfisz range](https://annals.math.princeton.edu/wp-content/uploads/annals-v161-n3-p11.pdf) applies uniformly to $Q\le B^2\ll L$; the intervals are $[K-h,2K-h]$ with $h=o(K)$.

For distinct $h_1,h_2$ in this residue class, an upper-bound sieve for the two linear forms $Qm-h_1,Qm-h_2$, $k=Qm$, bounds the number where both are prime by
$$
\ll \frac{K}{QL^2}\,J(h_1-h_2),\qquad
J(t)=\prod_{\substack{\ell\mid t\\\ell>2}}\frac{\ell-1}{\ell-2}.
\tag{3}
$$
We give the uniformity details in the appendix below. The standard elementary divisor expansion of $J$ gives $\sum_{1\le t\le D}J(t)\ll D$: after expanding over squarefree odd divisors, the required majorant is $\prod_{\ell>2}(1+1/(\ell(\ell-2)))<\infty$. Since $h_1-h_2=Qd$ and $J(Qd)\le 2J(d)$, summing (3) over the two offsets proves the second moment bound; the diagonal costs only the first moment, which tends to infinity. Thus by Cauchy–Schwarz or Paley–Zygmund, for some absolute $c_0,c_1>0$, at least $c_0K/Q$ multiples $k$ satisfy
$$
R_Q(k)\ge c_1 H/(QL).
\tag{4}
$$
This requires no asymptotic prime count in an individual subpolynomial short interval.

## 2. Removing exceptional lengths

We move $Q$ to the admissible class $a_Q=1$, which covers all indices $j\equiv1\bmod Q$ with weight at least $B$. Let $z_Q(j)=j/Q^{v_Q(j)}$ and define the deficient small indices by
$$
D_Q=\{1\le d\le Y: z_Q(d)<B,\ d\not\equiv 1\bmod Q\}.
$$
These are of the form $uQ^a$ with $u<B$, so $|D_Q|\ll B(1+V/\log Q)$. For every $d\in D_Q$ we seek a prime $q_d>2Y$ dividing $m_d=k-d+1$ with
$$
m_d/q_d^{v_{q_d}(m_d)}\ge B.
\tag{5}
$$
The following exclusions remove fewer than $c_0 K/(2Q)$ multiples when $b$ in (1) is sufficiently small.

1. Exclude lengths where any $m_d$ lacks a prime factor greater than $2Y$. Put $u_0=\log(2K)/\log(2Y)\asymp L/V$. Rankin's bound with $\sigma=1-\log u_0/(2\log(2Y))$ gives
   $$
   \Psi(2K,2Y)\le(2K)^\sigma\prod_{p\le 2Y}(1-p^{-\sigma})^{-1}
   \ll K e^{-c_2 u_0\log u_0}.
   $$
   Indeed the log of the product is $O(\sqrt{u_0}\log\log(2Y))=o(u_0\log u_0)$. The union bound over $d$ is $o(K/Q)$ since $|D_Q|,Q$ are polylogarithmic.

2. Exclude any $m_d=u q^e$ with $u<B$, a prime $q>2Y$, and $e\ge1$. Terms with $e\ge2$ cost $O(B\sqrt K L)$ per $d$, even without a progression condition, and so are negligible. For $e=1$, because $m_d\equiv 1-d\not\equiv0\bmod Q$ and $u<B\le Q$, the prime is in a reduced class modulo $Q$. The upper estimate from Siegel–Walfisz is $O(K/(u QL))$ per $u$. Summing over $u$ and $d$ costs
   $$
   \ll \frac KQ\frac{B(1+V/\log Q)\log B}{L}
   \ll \frac KQ\left(b+\frac{B\log B}{L}\right),
   $$
   with the factor $10$ from $V$ absorbed in the absolute constant. This is small relative to $c_0K/Q$ for sufficiently small absolute $b$.

3. Exclude lengths for which some $k-Y<j\le k$ has $z_Q(j)<B$. The number of candidates $j=uQ^a\le2K$, $u<B$, is $O(B(1+L/\log Q))$. Each costs at most $O(Y/Q+1)$ multiples of $Q$, so their union costs $o(K/Q)$.

We use (5) only for lengths surviving these exclusions. The primes $q_d$ are distinct, since a common prime $>2Y$ cannot divide two numbers $k-d+1$ differing by at most $Y$. They are also at most $k/B$ by (5).

## 3. Building the cover and averaging the auxiliary prime

Set $a_{q_d}=d$ for each $d\in D_Q$. Because $q_d\mid k-d+1$ and $d<q_d$ we have $k\bmod q_d=d-1$. Thus these moves are admissible. Together with $a_Q=1$, their moved-prime set is $S=\{Q\}\cup\{q_d:d\in D_Q\}$.

All indices through $Y$ now have weight at least $B$, since none is divisible by any $q_d$, and the remaining deficiencies were precisely $D_Q$. All indices $k-Y<j\le k$ are also covered. If no $q_d$ divides $j$, this follows from exclusion 3. Otherwise $j=k-d+1$ for the unique $q_d$ dividing it: both numbers lie in an interval of length $Y<q_d$, and no other $q_{d'}$ can divide $j$. Moreover $Q\nmid j$, since $d\not\equiv1\bmod Q$. Now (5) gives the required ordinary weight after removing moved primes.

Every deficient index still remaining must satisfy
$$
j=uQ^a\prod_{d\in D_Q}q_d^{e_d},\qquad
u<B,\qquad \sum_{d\in D_Q}e_d\le U=\frac{\log(2K)}{\log(2Y)}.
$$
The number of candidates is at most $B(1+\log(2K)/\log Q)(|D_Q|+\lceil U\rceil+1)^{\lceil U\rceil+1}$. Its logarithm is $O(\log L)+(\lceil U\rceil+1)\log(|D_Q|+\lceil U\rceil+1)$, which is at most $V/10$ for large $K$, since $|D_Q|=O(L)$ and $U=(1+o(1))\sqrt{L/\log L}/10$. In particular the number is $o(H/(QL))$.

For a surviving length satisfying (4), assign distinct reserve primes $p\in(k-H,k)$ with $p\equiv1\bmod Q$ to these deficient indices $Y<j\le k-Y$. Move each to $a_p=j$, which is admissible since $p>k/2$, $k\bmod p=k-p<H<j$ and $j<p$. Reserve primes are distinct from the earlier moved primes (which are at most $k/B$, apart from $Q$ which is smaller still). When a reserve is moved, the only index losing an ordinary factor $p$ is $j=p$, already covered by $Q$. Hence all positions have the required weight. This proves that at least $c_0K/(2Q)$ multiples of each $Q\in[B,B^2]$ have covers.

Crucially, do not keep just one auxiliary prime. By Mertens, $\sum_{B\le Q\le B^2}Q^{-1}=\log 2+o(1)$, so the number of good pairs $(k,Q)$ is $\gg K$. If $M(k)$ counts all prime divisors $Q$ of $k$ in $[B,B^2]$, then
$$
\sum_{K\le k\le2K}M(k)^2\ll K,
$$
by counting multiples of $Q$ and $Q_1Q_2$ and using the same reciprocal sum; the rounding errors from the polylogarithmic number of $Q$'s are $o(K)$. Cauchy–Schwarz gives $\gg K$ distinct good $k$. This proves the asserted positive proportion.

For completeness, the implication for binomial coefficients uses the [BNPZ lifting argument](https://arxiv.org/html/2605.21221#S5.SS1). For $p\le k$, let $e$ be the first exponent with $p^e>k$. Set $n-k\equiv0\bmod p^e$ for an unmoved prime, and $n-k\equiv-(p^e-p+a_p)\bmod p^e$ for a moved prime. In the latter case the congruence class $p^r-p+a_p$ exceeds $k\bmod p^r$ at every level $1\le r\le e$, so it meets $[1,k]$ in exactly $\lfloor k/p^r\rfloor$ positions. Thus the total valuation contributed at each $p\le k$ is exactly $v_p(k!)$ and cancels in $\binom nk$. At each index the cover weight divides the small-prime part of $n-k+j$. The CRT combines the local choices, proving the claimed residue-class conclusion.

## Appendix: uniform upper bound (3)

Let $N$ be the number of consecutive values of $m$ under consideration, so $N\asymp K/Q$. If the forms cannot both be odd, the count of pairs is zero for large $K$. Otherwise exclude primes $\ell\le w$ for which either form vanishes modulo $\ell$, with $Z=K^{1/20}$ and $w=Z^{1/10}$. For each such prime let $\nu_\ell$ count the excluded residues and let $g_\ell=\nu_\ell/\ell$. Here $\nu_\ell=2$ unless $\ell$ divides $Q(h_1-h_2)$, with $\nu_Q=0$. There are no other local obstructions. Omit primes with $g_\ell=0$. With binary exclusion indicators $X_\ell$, take the positive-square upper sieve obtained from the polynomial
$$
P(X)=\frac1{\mathcal K}\sum_{\substack{d\le Z\\ d\text{ squarefree},\ p\mid d\Rightarrow p\le w}}
 \prod_{\ell\mid d}\frac{g_\ell-X_\ell}{1-g_\ell},
\qquad
\mathcal K=\sum_{d\le Z}\ \prod_{\ell\mid d}\frac{g_\ell}{1-g_\ell}
$$
with the same squarefree support in both sums. Then $P(0)=1$ and the product-model expectation of $P^2$ is $\mathcal K^{-1}$ by orthogonality. In the product distribution randomizing $d$ with weights $\prod_{\ell\mid d}g_\ell/(1-g_\ell)$ on the full primorial, the mean of $\log d$ is $\sum_{\ell\le w}g_\ell\log\ell\le 2\log w+O(1)$. Markov gives $\mathcal K\gg\prod_{\ell\le w}(1-g_\ell)^{-1}$. Each term of the polynomial has coefficient absolute sum $(\log K)^{O(1)}$, and $\mathcal K\ge1$. For a pair of terms indexed by $d,d'\le Z$, every monomial after expansion depends only on primes dividing $[d,d']$; its actual count differs from the product-model count by at most $2^{\omega([d,d'])}=Z^{o(1)}$ by CRT rounding. Summing over at most $Z^2$ pairs gives an error $O(Z^{2+o(1)})$. Finally
$$
\prod_{\ell\le w}(1-g_\ell)\ll L^{-2}J(h_1-h_2)
$$
by comparison with $\prod_{\ell\le w}(1-1/\ell)^2$, absorbing the factors at $2$ and $Q$ into an absolute constant. Two true primes exceed $w$ and therefore survive the sieve. This proves (3), with a rounding error negligible relative to $K/(QL^2)$.

## Scope and finite checks

- The cover architecture and its conversion to valuations come from [BNPZ, Section 5](https://arxiv.org/html/2605.21221#S5). The changes are the positive-fraction reserve estimate, the small auxiliary prime and its scale choices, and the simultaneous use of auxiliary primes across a band with bounded second overlap moment.
- See [Schinzel's 1958 paper](https://matwbn.icm.edu.pl/ksiazki/cm/cm5/cm5128.pdf) and [the formally stated open variant of #387](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB387%C2%BB/) for the distinction between failure at given $k$ and eventual failure for all non-prime-power $k$.
- The [fixed finite verifier](verify_factor_schinzel_dense_weighted_covers.js) runs 668 exact assertions over eight fixed small covers (including two reserve repairs), their residue-to-valuation lift, and twelve finite first/second-moment count identities. It does not test the implicit constants or claim any result about the least $k$ at growing weight.
