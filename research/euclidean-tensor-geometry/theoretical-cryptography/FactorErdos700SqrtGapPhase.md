# Erdős–Szekeres binomial gcds: three phases at square-root prime gaps

Let $f(n)=\min_{2\le k\le \lfloor n/2\rfloor}\gcd(n,\binom nk)$, as in Erdős problem [#700](https://www.erdosproblems.com/700). We classify $f(pqr)$ for all prime triples $p<q<r$ with $r-p<\sqrt p$. The exact answer can be the **middle** prime $q$, not just the smallest prime or the product of the two smallest primes. All three possibilities have positive limiting proportions in this family.

## 1. Exact classification

Write $a=q-p$, $d=r-q$, and $b=a+d=r-p$. Assume $p>b^2$. Then
$$
f(pqr)=
\begin{cases}
p, & d\le a\ \text{or}\ r\le d(2d-1),\\
q, & d>a,\ r>d(2d-1),\ p\le b(a+b-1),\\
pq, & \text{otherwise}.
\end{cases}
\tag{1}
$$
For example, $(p,q,r)=(41,43,47)$ is in the middle-prime case. The triple $(197,199,211)$ has increasing gaps but is in the smallest-prime case. For $p>2b^2$, the formula reduces to the previously posted two-way rule: $f(pqr)=pq$ for $d>a$, and $f(pqr)=p$ otherwise.

### Proof

Use $n=pqr$. Say a prime $\ell\mid n$ escapes at $k$ if $\ell\nmid\binom nk$. By Lucas's theorem, escape requires $\ell\mid k$; subject to this, it occurs exactly when each base-$\ell$ digit of $k/\ell$ is no larger than the corresponding digit of $n/\ell$. All three cannot escape together, since that would give $n\mid k$. If two escape, the gcd equals the remaining prime. If no pair can escape, the gcd is at least $pq$; equality is attained at $k=r$, since the units digit of $pq$ in base $r$ is $bd>0$ and $k/r=1$.

All three primes are odd: $a,d\ge 2$ and $b\ge 4$. In particular $2b-2\le b^2/2<p/2$. We use the following expansions, in their respective bases (all displayed coefficients are valid digits under $p>b^2$):
$$
\begin{aligned}
qr&=p^2+(a+b)p+ab,\\
pr&=
  \begin{cases}
  q^2+(d-a-1)q+(q-ad),&d>a,\\
  (p+d-1)q+(q-ad),&d\le a,
  \end{cases}\\
pq&=(p-d)r+bd.
\end{aligned}
\tag{2}
$$

**Nonincreasing gaps.** If $d\le a$, choose the unique integer $s\in[(a+1)d,(a+2)d)$ congruent to $r$ modulo $d$, and put $j=(r-s)/d$. Then $b\le s\le bd$, and $1\le j\le p/d\le p/2$. At $k=qrj$ the two relevant expansions are
$$
k/q=jq+(q+d-s),\qquad k/r=(j-1)r+s.
$$
The units digits satisfy $0<q+d-s\le q-ad$ and $0<s\le bd$. The higher digits satisfy $j\le p+d-1$ and $j-1\le p-d$ because $p>b^2$ and $j\le p/2$. Both $q,r$ escape, so $f(n)=p$.

Now suppose $d>a$. If a pair of primes escapes, write $k$ as their product times $j$. The $p$-test uses only the two lowest digits of $k/p$, since $k/p\le qr/2<p^2$. Similarly $k/q\le pr/2<q^2$. These inequalities follow by (2) and $p>b^2$.

**The pair $p,q$ cannot both escape.** Here $k/p=jq\ge jp$, so the $p$-test gives $j\le a+b$. Because $a<b/2$, we have $ja\le a(a+b)<p$. Thus $k/p=jp+ja$ and $k/q=(j-1)q+(q-ja)$. The $q$-test requires both $j\le d-a$ and $ja\ge ad$, or $j\ge d$. This is impossible.

**The pair $q,r$ escapes exactly when $r\le d(2d-1)$.** With $k/q=jr\ge jq$, the $q$-test gives $j\le J:=d-a-1$. Conversely every integer $1\le j\le J$ passes the $q$-test: its digit pair is $(j,jd)$, with $jd+ad\le(d-1)d<q$. In base $r$, $k/r=jq=(j-1)r+(r-jd)$; the upper digit passes, since $j-1\le J<p-d$. The units digit passes precisely if $(j+b)d\ge r$. This is feasible if and only if $(J+b)d=d(2d-1)\ge r$. The witness $j=J$ is allowed since $J<p/2$.

**The pair $p,r$ escapes exactly when $p\le b(a+b-1)$.** The $p$-test applied to $k/p=jr$ first gives $j\le a+b$. Then $jb<2p$, because $a<b/2$ and $p>b^2$. Neither $p$ nor $r$ can equal $jb$ since each is prime and greater than $b$. If $jb<p$, the $p$-test gives $jb\le ab$, so the units digit $r-jb$ of $k/r=jp$ is bigger than $bd$: indeed $r>ab+bd=b^2$. If $r<jb<2p$, the $p$-test gives $jb-p\le ab$; the units digit $2r-jb$ of $k/r$ is again bigger than $bd$. The only possibility is $p<jb<r=p+b$, which selects the unique $j=\lceil p/b\rceil$. For that $j$ the units digits $jb-p$ and $r-jb$ are positive and less than $b$, so both pass. The higher digit $j-1$ in base $r$ passes whenever $j+1\le a+b$ because $a+b<p/2$ and $d<p/2$. The remaining condition is the higher base-$p$ digit $j+1\le a+b$, exactly $p\le b(a+b-1)$. This witness has $j<q/2$, so $k=prj$ is allowed.

Since $p<q<pq$, these cases prove (1), including overlaps of the $q,r$ and $p,r$ escape conditions.

## 2. Unconditional counts and proportions

For $N\ge 1$, count triples of distinct primes $p<q<r$ with $pqr\le N$ and $r-p<\sqrt p$. Unique factorization identifies these triples with distinct integers $n$. The total is asymptotic to
$$
\frac{27}{4}\frac{N^{2/3}}{(\log N)^3}.
\tag{3}
$$
For the three respective rows of (1), the counts are asymptotic to
$$
\frac{27}{2}\,A_i\,\frac{N^{2/3}}{(\log N)^3}, \qquad i\in\{p,q,pq\}.
\tag{4}
$$
The constants are the areas of explicit regions in $T=\{(u,v):0<u<v<1\}$, with $u=(q-p)/\sqrt p$ and $v=(r-p)/\sqrt p$. Ignoring boundaries of area zero, these regions are
$$
\begin{aligned}
R_p&=\{u\ge v/2\}\cup\{v-u>1/\sqrt2\},\\
R_q&=\{u<v/2,\ v-u<1/\sqrt2,\ v(u+v)>1\},\\
R_{pq}&=\{u<v/2,\ v-u<1/\sqrt2,\ v(u+v)<1\}.
\end{aligned}
\tag{5}
$$
All three regions are understood to lie in $T$. The limiting proportions within the family are $2A_i$, respectively about **58.58%, 6.66%, and 34.76%**.

For closed forms put $s_0=1/\sqrt 2$, $v_0=\sqrt{2/3}$ and $v_*=(1+\sqrt{17})/(4\sqrt2)$. The first region consists of the decreasing-gap half and a disjoint triangle of side $1-s_0$, giving $A_p=1/4+(1-s_0)^2/2$. The middle region is between $u=v/2$ and $u=\max(1/v-v,v-s_0)$ for $v_0<v<1$. Consequently
$$
A_q=\int_{v_0}^{v_*}(3v/2-1/v)\,dv+
     \int_{v_*}^1(s_0-v/2)\,dv,\qquad
A_{pq}=1/2-A_p-A_q.
$$

### Prime distribution argument

Use Guth–Maynard [Corollary 1.4](https://arxiv.org/html/2405.20552#S1) on primes in almost all short intervals. On $x\in[X,2X]$, apply it to the $O(\log X)$ positive lengths on a grid of spacing $\sqrt X/\log X$ up to $2\sqrt X$ (round lengths to integers). All nonzero lengths exceed $X^{2/15+\epsilon}$, say $\epsilon=1/10$, for large $X$. Outside $O(X\log X\exp(-c(\log X)^{1/4}))$ integer starts, all the interval counts on this grid equal length divided by $\log x$ with errors $o(\sqrt X/\log X)$, uniformly. Monotonicity fills in the grid: for a good prime $p\in[X,2X]$ the measures
$$
\mu_p=\frac{\log p}{\sqrt p}
          \sum_{\substack{\ell\ \mathrm{prime}\\ p<\ell<p+\sqrt p}}
          \delta_{(\ell-p)/\sqrt p}
$$
have interval masses on $(0,1)$ equal to interval length plus $o(1)$, uniformly in the good primes and the endpoints. For any Jordan-measurable $R\subset T$, approximate $R$ from inside and outside by finite unions of grid rectangles. Product measures $\mu_p\otimes\mu_p$ give its area plus $o(1)$, uniformly over good primes. This uses almost-all estimates over short intervals, not a fixed-gap prime-tuple conjecture. The ordering is already enforced by $R\subset T$, so there is no additional combinatorial factor.

At a given good $p$, the exact tests for the curves in (5) are $u\ge v/2$, $2(v-u)^2\ge 1+(2v-u)/\sqrt p$, and $v(u+v)\ge 1+v/\sqrt p$. They differ from (5) only in shrinking neighborhoods of the two non-linear boundaries. Each such neighborhood can be covered by finitely many rectangles of arbitrarily small total area, so the same product-measure argument applies. Hence the pair counts at good $p$ are $(A_i+o(1))p/(\log p)^2$. The bad starts contribute at most $O(X)$ pairs each, making their total $o(X^2/(\log X)^3)$. Their missing main weights are negligible as well.

Sum over dyadic blocks, then use the ordinary prime number theorem and partial summation:
$$
\sum_{p\le Y}\frac{p}{(\log p)^2}\sim \frac{Y^2}{2(\log Y)^3}.
$$
For the dyadic summation, blocks below $\sqrt Y$ contain only $O(Y)$ pairs by the crude bound $O(p)$ per start; on the higher blocks the normalized $o(1)$ errors tend uniformly to zero. Finally, set $Y=N^{1/3}$. For $p\le Y-\sqrt Y$, every counted product is at most $N$; the boundary $Y-\sqrt Y<p\le Y$ contributes just $O(Y^{3/2})$ pairs, again using $O(Y)$ per start. This proves (3) and (4).

In this family $f(pqr)>\sqrt{pqr}$ holds exactly in the $pq$ phase. Thus the square-root strict inequality in #700(ii) holds for at least $(2.34656\ldots+o(1))N^{2/3}/(\log N)^3$ composites up to $N$; (4) is an asymptotic only within the specified close-prime family. Here $f(n)=n/P(n)$ also holds exactly in the $pq$ phase, with $P(n)=r$.

## 3. Relation to prior work and checks

- [Erdős and Szekeres, *Some number theoretic problems on binomial coefficients* (1978), pp. 98–99](https://static.renyi.hu/~p_erdos/1978-46.pdf) is the primary statement. Its $P(n)$ is the largest **prime power** dividing $n$, which agrees with the largest prime on our squarefree family.
- [Erdős Problem a Day, #700](https://www.erdosproblemaday.com/day/700-gcd-binomial) had already publicly described the two-way close-triple formula for $p>10(r-p)^2$ and its Maynard-based infinitude proof for part (ii). We do not claim priority for that formula or the yes answer. The extension here is the third phase in the whole range $r-p<\sqrt p$, the two transition curves, and the unconditional counting laws. Parts (i) and (iii) are not resolved in general.
- The accompanying [fixed finite verifier](verify_factor_erdos700_sqrt_gap_phase.js) uses Legendre factorial valuations, separately from the digit proof. It checks all 2,063 qualifying triples with $p\le 2100$ and all 4,216,932 allowed pair-multiple trials for them. It reaches all three phases, gap ties, cases with the minimal final gap $d=2$, and 46 overlaps of the two increasing-gap escape conditions. It takes no input modulus and makes no general factorization claim.
