# An exact obstruction to finite modular covers of the eight balanced families

This does **not** exhibit simultaneous primes. It shows why two tempting universal elimination strategies for [the eight remaining h=2 families](EACBalancedCores.md) cannot work, even if combined. Take any $P=P_0\cup V$ with $P_0=\{3,5,7,11,13,19,23,47\}$, $V\subseteq\{17,31,37\}$, and put $F=\prod_{p\in P}p$, $v_p=2p+1$.

**For every finite set of primes Q**, infinitely many admissible support/size candidates $W=25F^n$ simultaneously satisfy
- $W\equiv1\pmod4$, $\mathrm{rad}(W)=F$, $v_p\mid W$ for all p;
- none of the distinct integers $R_p=(W/v_p-1)/2$ has any prime divisor in Q, and all $R_p>53$;
- none of the integers $W/v_p$ is any proper integer power.

In fact each polynomial $25X^m-v_p$ is irreducible over the rationals for every $m\ge1$. Thus passing to fixed multiples of an exponent cannot supply a polynomial factorization into positive-degree factors either. These are conclusions about finite trial-divisor and algebraic-power tests, not an obstruction to other arithmetic approaches or a claim that $R_p$ itself is prime.

**Proof.** Take n any sufficiently large even multiple of every order of F modulo odd $\ell\in Q\setminus P$. Then $W\equiv25\pmod\ell$. The following nonzero differences $25-v_p$ have no prime divisor outside $\{2\}\cup P_0$:

|p|3|5|7|11|13|19|23|47|17|31|37|
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|$25-v_p$|18|14|10|2|−2|−14|−22|−70|−10|−38|−50|

Every $v_p$ is P-smooth. Thus $R_p$ is not divisible by any of the indicated odd primes outside P. For large n, every member of P divides $W/v_p$, so none divides $R_p$ either. Finally $F^n\equiv1\pmod4$ and $v_p\equiv3\pmod4$ give $R_p$ odd. Integrality, support, distinctness and eventual size are immediate.

For $q\in P$, put $d_q=2\mathbf 1_{q=5}-\nu_q(v_p)$. The valuation vector of $W/v_p$ is $(n+d_q)_{q\in P}$. The gcd of **all pairwise differences** among the offsets $d_q$ is 1 for each allowed p. This already holds on the $P_0$ coordinates; it follows directly from $v_p=7,11,15,23,27,39,47,95,35,63,75$. For instance $v_{13}=27$ has offsets −3,2,0, whose differences generate 1, and $v_{37}=75$ (optional) has offsets −1 at 3 and 0 elsewhere. Therefore the full valuation vector always has gcd 1, ruling out *every* power exponent >1.

For irreducibility take a real root $\alpha=(v_p/25)^{1/m}$ of $25X^m-v_p$ and let $d=[\mathbb Q(\alpha):\mathbb Q]\le m$. Taking the field norm gives $N(\alpha)^m=(v_p/25)^d$. At each rational prime $q\in P$, this implies $m\mid d\,d_q$. Since the offsets have gcd 1, $m\mid d$, hence $d=m$ and the polynomial is irreducible. The argument ignores any integer content as it works over $\mathbb Q$. It applies also to arbitrarily long multiples of an exponent needed for a given finite menu Q.
