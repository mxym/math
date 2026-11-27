# Near-full deterministic streaming width for primes and semiprimes

Fix a base $b\ge2$. Inputs are canonical $B$-digit words, so their values satisfy $Y/b\le N<Y$ for $Y=b^B$. A deterministic machine reads each digit once in a natural order, either least significant first or most significant first, and decides a predicate exactly. Transitions may depend on the position, with arbitrary computation between reads. The theorem is a lower bound on the number of states at one fixed cut, not on the time complexity of primality or factoring.

**Theorem.** Write $\Lambda=\log\log Y$. For either natural order, the following minimum widths hold:
 
- **Primality:** $Y\exp(-O_b(\Lambda^2))$.
- **Balanced distinct-prime products**, for instance $N=pq$ with $p<q\le2p$: $Y\exp(-O_b(\Lambda^2))$.
- **General products of two primes**, either with or without allowing a repeated prime: $Y\exp(-O_b(\Lambda^2\log(2+\Lambda)))$.

For primality, this improves the $Y\exp(-O_b(\Lambda^2\log(2+\Lambda)))$ automaticity lower bound proved by [Dubbe, *The automaticity of the set of primes*, Theorem 1](https://doi.org/10.1016/j.tcs.2025.115480) in the least-significant-first convention. The exact same-width result in the other direction follows directly, not by reversal of an automaton.

The proof has a reusable form: it applies to **any** accepted subset of the canonical interval of size at least $cY/(\log Y)^\nu$, if all its elements have at most $d$ distinct prime divisors below a suitable cutoff $\exp(C\Lambda(\log(2+\Lambda))^d)$. The constants depend on the fixed $c,\nu,d,b$; the resulting width is
$$
Y\exp\!\big(-O_{c,\nu,d,b}(\Lambda^2(\log(2+\Lambda))^d)\big). \tag{1}
$$
The condition does not require a uniform count of accepted words in short intervals.

## A uniform sieve for a common continuation

We give the sieve details because its dimension grows with $Y$. Let $W\le Y$ be a continuation range. Suppose a continuation $t$ is accepted for $K$ distinct prefixes, so the corresponding values are $F_i(t)=a t+c_i$, where $1\le a\le Y$ and $0\le c_i<Y$ are integers with $c_i$ distinct. Here $K$ will be of order $\Lambda$, and $\log W$ of order $\Lambda^2(\log(2+\Lambda))^d$. Let $A_0$ be a large constant, and put
$$
z=W^{1/(A_0 K)},\quad Z=\lfloor W^{1/12}\rfloor,\qquad
\Delta=a\prod_{i<j}|c_i-c_j|\prod_{p\le2K}p.
$$
We use only primes $p\le z$ not dividing $\Delta$. Each forbids exactly $K$ residues modulo $p$, and $K/p<1/2$.

Here is the upper bound on avoiding all the forbidden residues for any subset $\mathcal Q$ of these primes, on an interval of length $T$ (including an arithmetic progression parameter after changes below):
$$
\#\{\text{avoiding integers in the interval}\}
\le 2T\prod_{p\in\mathcal Q}(1-K/p)+O(W^{1/2}). \tag{2}
$$
The constant is uniform in $K$. Write $g(p)=K/p$ and $h(p)=g(p)/(1-g(p))$ on $\mathcal Q$, and extend these multiplicatively on squarefree products of its primes, with $g(1)=h(1)=1$. The Selberg quadratic majorant uses weights $\lambda_j$ supported on such $j\le Z$ with $\lambda_1=1$. The square of the sum of weights for those $j$ whose prime constraints the input falls into supports the avoiding count: it is $1$ there and nonnegative elsewhere. By CRT the count falling into the simultaneous forbidden classes modulo $[i,j]$ is $Tg([i,j])+O(\omega_*([i,j]))$, where $\omega_*(m)=\prod_{p\mid m}K\le m$ is the number of those classes.

For completeness, the main quadratic form is
$$
\sum_{i,j}\lambda_i\lambda_j g([i,j])
=\sum_{r\le Z}\frac{1}{h(r)}
       \left(\sum_{\substack{j\le Z\\r\mid j}}\lambda_j g(j)\right)^2,
$$
where all summation variables are squarefree and supported on $\mathcal Q$. This follows from $g([i,j])=g(i)g(j)/g((i,j))$ and $1/g(c)=\sum_{r\mid c}1/h(r)$. Set $G=\sum_{r\le Z}h(r)$ and choose the inner sum $(\mu(r)h(r))/G$ for each $r$. Möbius inversion then gives $\lambda_1=1$, the quadratic form $1/G$, and
$$
|\lambda_j|=\frac{h(j)}{g(j)G}\sum_{\substack{m\le Z/j\\(m,j)=1}}h(m)
\le \prod_{p\mid j}(1-g(p))^{-1}\le j.
$$
The error in the majorant is thus $O(\sum_{i,j\le Z}i^2j^2)=O(Z^6)=O(W^{1/2})$.

To bound $G$ below, choose a random squarefree product of primes from $\mathcal Q$ by independently including each $p$ with probability $g(p)$. Its distribution is proportional to the weights $h(r)$ on all squarefree products. The expected logarithm is at most
$$
K\sum_{p\le z}\frac{\log p}{p}\ll K\log z=\frac{\log W}{A_0}.
$$
For $A_0$ sufficiently large this is at most $\tfrac12\log Z$. Markov's inequality gives probability at least $1/2$ that the product is at most $Z$. This shows $G\ge \tfrac12\prod_{p\in\mathcal Q}(1-K/p)^{-1}$ and proves (2). In particular it does not require the continuation length to accommodate every product of the sifting primes.

### Allowing a fixed number of small prime divisors

Suppose each accepted value has at most $d$ distinct prime factors up to $z$. For a shared accepting $t$ the set $S$ of sifting primes that divide any of the $F_i(t)$ then has size at most $dK$. For each possible $S$, the value of $t$ falls in at most $K^{|S|}$ classes modulo $D_S=\prod_{p\in S}p$. In each such class write $t=t_0+D_S u$. For the remaining sifting primes the forbidden classes in $u$ still have count $K$ by invertibility of $D_S$. Apply (2) with interval length at most $W/D_S$. The sieve product for that class is bounded by
$$
\prod_{\substack{p\le z\\p\nmid\Delta D_S}}(1-K/p)
\le \left(\prod_{p\le z}(1-1/p)\right)^K
         \left(\frac{\Delta D_S}{\varphi(\Delta D_S)}\right)^K
\le (C\Lambda/\log z)^K . \tag{3}
$$
The first step uses $1-K/p\le(1-1/p)^K$ and removes all exceptional primes. The second uses Mertens' estimate and $n/\varphi(n)\ll\log\log(3n)$, with $\log(2\Delta D_S)\ll K^2\log Y+dK\log z$. For example the totient bound follows by splitting prime divisors at $\log(3n)$, applying Mertens below it, and noting that the sum of their reciprocals above it is $O(1)$.

After summing the main terms over choices of $S$ and their residues, the additional factor is bounded by
$$
\sum_{|S|\le dK}\frac{K^{|S|}}{D_S}
 \le \sum_{j\le dK}\frac{(K H_z)^j}{j!}
 \le [C_d(1+H_z)^d]^K,\qquad H_z=\sum_{p\le z}\frac1p\ll\log\log(3z).
$$
For $H_z\le d$ use the exponential series; otherwise the terms through $dK$ increase and the last is bounded by $(eH_z/d)^{dK}$. When $d=0$ the exact factor is one. The number of classes for the error terms is at most
$$
\sum_{j\le dK}(Kz)^j\le W^{d/A_0+o(1)}
$$
since $K\log K=o(\log W)$. Taking $A_0$ sufficiently large (also depending on $d$), the number of shared accepted continuations is at most
$$
W\!\left(\frac{C_d\Lambda(1+\log\log(3z))^d}{\log z}\right)^K
 + O(W^{2/3}). \tag{4}
$$
Here the growth conditions on $K,W$ are those stated above. The looser $W^{2/3}$ absorbs the sum of the Selberg error terms. No prime-tuple asymptotic or lower bound is assumed.

## Counting distinct rows

Take $K=\lceil 4(\nu+1)\Lambda\rceil$ and let $W=b^L$ be the least power of $b$ such that
$$
\log W\ \ge\ A_0 C_2 K \Lambda (\log(2+\Lambda))^d,
$$
with $C_2$ a sufficiently large constant. Set $R=Y/W$. This gives $\log z\asymp C_2\Lambda(\log(2+\Lambda))^d$ and $1+\log\log(3z)=O_d(\log(2+\Lambda))$. For large $Y$, the base of the power in (4) is at most $1/4$ and the error there is negligible compared with $W/(\log Y)^{\nu+1}$. Thus the shared acceptance count of any $K$ distinct rows is $O(W/(\log Y)^{\nu+1})$.

For most-significant-first, a row has fixed high prefix $v$ and values $vW+t$ for $0\le t<W$. For least-significant-first, a row has fixed low prefix $v$ and values $Rt+v$ for $W/b\le t<W$. These give the specified common-slope forms with distinct intercepts. In both cases all words have canonical length, there are at most $R$ rows, and each canonical word appears once.

Group the rows by their Boolean continuation patterns. A group with at least $K$ prefixes has pattern support of size only $O(W/(\log Y)^{\nu+1})$, by selecting any $K$ of the prefixes and using (4). Thus all these groups together account for only $O(Y/(\log Y)^{\nu+1})$ accepted words. Of the at least $cY/(\log Y)^\nu$ accepted words, a positive fraction therefore lies in groups of fewer than $K$ prefixes. Each such pattern accounts for at most $KW$ words, so there are $\Omega(Y/(KW(\log Y)^\nu))$ distinct patterns, giving (1). Two distinct patterns cannot share the same streaming state at the cut, since the same continuation would demand different decisions.

## Applying the criterion

For primes take $\nu=1,d=0$ by the prime number theorem and $z=Y^{o(1)}$. For balanced semiprimes take $\nu=2,d=0$. Indeed both factors are $\gg_b\sqrt Y$, and choosing the two primes in a common fixed interval $(c_3\sqrt Y,c_4\sqrt Y)$ with $b^{-1/2}<c_3<c_4<1$ and $c_4/c_3<2$ yields $\gg_b Y/(\log Y)^2$ distinct canonical products. For all semiprimes the same density lower bound applies, and at most one prime factor can be $\le z$ since $z^2<Y/b$; use $d=1$. The bounds transfer from complete digit-length ranges to arbitrary cutoffs up to a constant factor, as in standard automaticity.

The shared-continuation strategy comes from [Dubbe](https://arxiv.org/abs/2409.04314). The quantitative change in the rough case is the direct lower bound on the Selberg denominator by a Bernoulli product with controlled logarithm, together with retaining only the dense low-multiplicity groups. This allows $\log W=O(\Lambda^2)$ rather than $O(\Lambda^2\log(2+\Lambda))$ for prime recognition. The bounded-exception count is additionally needed to apply the method to unrestricted semiprime recognition. This is distinct from the [power-free predicate](FactorPowerFreeStreaming.md), where there is no positive-density roughness at small primes and the proof counts large square divisors globally instead.

[Exact finite checks](verify_factor_rough_automaticity.js) cover the Selberg quadratic identity and normalization, the CRT grouping of small-prime exceptions, and finite prefix multiplicity identities on predetermined toy ranges. They do not prove the estimates or accept arbitrary integers. We make no claim about randomized error, arbitrary orders, or a general factoring algorithm.
