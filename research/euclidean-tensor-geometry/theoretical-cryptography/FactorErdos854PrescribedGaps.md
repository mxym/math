# Every even primorial gap up to the modern long-cover scale

Write $p_k$ for the $k$-th prime and $P_k=\prod_{p\le p_k}p$. Let $F(k)$ be the least positive even integer not occurring as a difference between consecutive members of the **finite** list
$
             \{1\le a<P_k:\gcd(a,P_k)=1\},
$
and let $Q(k)$ be the number of different differences in that list. This is the first-missing-gap question and the related abundance question in [Erdős #854](https://www.erdosproblems.com/854). The first question already appears on p. 80 of [Erdős's 1985 paper](https://old.renyi.hu/~p_erdos/1985-17.pdf).

**Theorem.** There is an absolute constant $c>0$ such that, for all sufficiently large $k$, **every** even $g$ with
$$
          2\le g\le c\,p_k\log p_k
                       \frac{\log_3 p_k}{\log_2 p_k}                 \tag{1}
$$
occurs in the finite list. Here $\log_j$ is the $j$-fold iterated natural logarithm. In particular
$$
 F(k),\ Q(k)\gg p_k\log p_k\frac{\log_3 p_k}{\log_2 p_k}
                 \asymp k(\log k)^2
                       \frac{\log\log\log k}{\log\log k}.
 \tag{2}
$$

More generally, for every fixed $r\ge2$ and all sufficiently large $k$ depending on $r$, every admissible tuple $0=h_1<\cdots<h_r$ of span $h_r$ at most the right side of (1) occurs as a block of exactly $r$ consecutive members of the finite list. Admissibility means $\#\{h_j\bmod p:1\le j\le r\}<p$ for each prime $p$, a necessary condition for any such translate. The tuple, not just its span, may vary with $k$.

### Comparison and scope

[Ziller, Propositions 2.6–2.7 and Corollary 2.8](https://arxiv.org/abs/2007.01808) prove that the first $k$ even values occur (and compute gap sets at many stages). The [July 2026 working report](https://www.erdosproblemaday.com/report/854) gives $F(k)\ge(e^\gamma-o(1))k\log\log k$, not a bound at the scale of (2). [Holt–Rudd](https://arxiv.org/abs/1510.00743) prove eventual occurrence for a fixed even gap and certain fixed repeated-gap constellations. Here both the size and the positions of the offsets are uniform over a range growing at the modern long-gap scale.

[Ford–Green–Konyagin–Maynard–Tao](https://www.ams.org/journals/jams/2018-31-01/S0894-0347-2017-00876-2/S0894-0347-2017-00876-2.pdf) give a lower bound of this order for the length of **some** full covering interval. The input is their residue-covering conclusion (1.1), not a conjecture about gaps between actual primes. The new step below transforms a single full covering into occurrences with every prescribed admissible set of surviving offsets, leaving no intervening survivors. No lower bound proportional to the actual maximal primorial gap is claimed; (2) neither gives a matching upper bound for $F(k)$ nor proves all of #854.

## 1. A cover-to-constellation transfer

The following statement isolates the step independent of the source of a long cover. Let $D>0$, $r\ge2$ be fixed, $x$ be sufficiently large, and $Y$ be an integer with $x\le Y\le x(\log x)^D$. Suppose that $[1,Y]\cap\mathbb Z$ is covered by a family $b_p\bmod p$ with one residue class for each prime $p\le x/2$. Put $P(x)=\prod_{p\le x}p$. If $h_1=0<h_2<\cdots<h_r$ is admissible and
$$
                         h_r\le Y-\lfloor Y/(\log x)^2\rfloor,     \tag{3}
$$
then its translate occurs as exactly the coprimes to $P(x)$ in a subinterval of $[1,P(x)-1]$. We will retain the core of the original cover and reserve primes in $(x/2,x]$.

### 1.1. Find shifts safe at the small primes

Let $L=\log x$, $w=L^{D+4}$, $M=\lfloor Y/L^2\rfloor$. In $[1,M]$ consider the shifts $m$ for which the $r$ points $m+h_j$ avoid the original class at every prime $p\le w$. For each small prime the forbidden classes of $m$ are
$$
               b_p-h_j\bmod p,\qquad 1\le j\le r.
$$
Their number $\nu(p)$ is at most $r$ and strictly below $p$. Uniformly in the original residue choices and the admissible tuple, the set $\mathcal A$ of these shifts has
$$
                  |\mathcal A|\gg_r M/(\log w)^r.                   \tag{4}
$$

Here is a short inclusion–exclusion proof in this polylogarithmic range. Write $g_p=\nu(p)/p$, $S=\sum_{p\le w}g_p$. For any set of at most $J$ small primes, the intersection of the forbidden events has size $M\prod g_p+O(\prod\nu(p))$ by CRT. Take $J$ to be the largest odd integer not exceeding $\log M/(4\log(2rw))$. The odd Bonferroni truncation is a lower bound for the avoiders. Its total counting error is at most $O((J+1)(rw)^J)=O(M^{1/3})$. The discrepancy of its main term from the full product $M\prod(1-g_p)$ is at most $M\sum_{\ell>J}S^\ell/\ell!$. By Mertens $S\ll_r\log\log w$, whereas $J\asymp_D L/\log L$, so this tail is $O_{r,D}(M x^{-c_{r,D}})$ for some positive constant: the first omitted term is bounded by $(eS/(J+1))^{J+1}$, and the following terms decrease geometrically. Finally $\prod(1-g_p)\gg_r(\log w)^{-r}$. Indeed for the finitely many $p\le2r$ the factors are at least $1/p$, and for $p>2r$ the ratios $(1-r/p)/(1-1/p)^r$ have a positive convergent product; apply Mertens to $\prod(1-1/p)^r$. This proves (4).

### 1.2. Delete conflicting classes at small average cost

Take $m$ uniformly from $\mathcal A$. Call an original class at a prime $w<p\le x/2$ conflicting if it contains at least one of the $m+h_j$. The probability of this is at most
$$
     \frac{r(M/p+1)}{|\mathcal A|}
           \ll_r(\log w)^r(1/p+1/M).                              \tag{5}
$$
This only uses the trivial count of a single residue class in $[1,M]$. No independence across large primes is assumed.

Delete all conflicting classes. Each deletion can uncover at most $Y/p+1$ points of the entire original interval. By (5) the expected total number of points left uncovered, including the $m+h_j$, is at most
$$
 \begin{split}
   &O_r\left((\log w)^r
         \sum_{w<p\le x/2}(1/p+1/M)(Y/p+1)\right)\\
   &\qquad=O_r\left((\log w)^r
              \bigl(Y/w+(1+Y/M)\log x+x/M\bigr)\right)
       =o_{r,D}(x/\log x).                                         \tag{6}
 \end{split}
$$
For the middle expression one may bound the prime sums by the integer harmonic and reciprocal-square sums. The last equality uses $Y/w\le x/L^4$, $Y/M=O(L^2)$, and $x/M=O(L^2)$. Small primes delete nothing because $m\in\mathcal A$. Choose a shift $m$ meeting the average bound. By (3) the interval $[m,m+h_r]$ lies inside the full original cover.

### 1.3. Repair the cover without hitting the prescribed points

There are $(1/2+o(1))x/\log x$ unused primes $q\in(x/2,x]$. If $n\in[m,m+h_r]$ is uncovered and is not one of the prescribed points, assigning $n\bmod q$ to such $q$ is forbidden only if $q\mid n-m-h_j$ for some $j$. Each of these is a nonzero integer of absolute value at most $Y<(x/2)^2$, so at most one $q$ in the reserve divides it. Thus each uncovered nonprescribed point forbids at most $r$ reserve primes. Assign a distinct permissible $q$ to each such point greedily; (6) leaves more than $r+2$ reserve primes after all assignments. None of the repaired classes hits the prescribed points.

Complete the deleted classes and the unused reserve classes with arbitrary choices avoiding all prescribed points. This is possible at every prime by admissibility. Choose two unused reserve primes last. Varying their allowed residues gives at least $(x/2-r)^2$ different CRT translations modulo $P(x)$. Indeed choose $t\bmod P(x)$ to satisfy $t\equiv-b_p\bmod p$ at every prime, where $b_p$ is the final assigned class. Then $t+n$ is divisible by $p$ exactly when $n\equiv b_p\bmod p$, so the coprimality pattern on $[m,m+h_r]$ translates to the intended pattern modulo $P(x)$. At most $h_r+1\le Y+1$ start residues $t+m\bmod P(x)$ fail to put the whole block inside the literal interval $[1,P(x)-1]$. Since $Y=o(x^2)$, at least one completion gives an internal block. This proves the transfer.

## 2. Applying the transfer at the Ford–Green–Konyagin–Maynard–Tao scale

In the cited paper, let $Y_0(s)$ be the maximum integer $y$ such that a single chosen residue modulo each prime $p\le s$ covers $[1,y]$. Their displayed bound (1.1) is
$$
              Y_0(s)\gg s\log s\,\frac{\log_3 s}{\log_2 s}.
$$
This is the covering statement obtained explicitly in their §3 by assigning the remaining uncovered elements to additional primes and translating the interval. Apply it at $s=x/2$; then there is a full cover of $[1,Y]$ with
$$
           Y=\left\lfloor c_0 x\log x
                        \frac{\log_3 x}{\log_2 x}\right\rfloor
$$
for a suitable absolute $c_0>0$. Here $x\le Y\le xL^2$ for large $x$. The transfer applies with $D=2$, and (3) contains all admissible spans at most $(c_0/2)x\log x\log_3 x/\log_2 x$ for sufficiently large $x$. Take $x=p_k$. Every pair of offsets $\{0,g\}$ with $g$ even is admissible: modulo $2$ it occupies one residue, and every odd prime has more than two residues. This proves (1), including finite-list internal occurrence, hence the claimed bounds for $F(k)$ and $Q(k)$.

The companion verifier checks ordinary CRT constructions, uniform finite inclusion–exclusion bookkeeping, the collision accounting, and the repair on small fixed overlaps. It does not independently prove the long-cover input or test its asymptotic constants.
