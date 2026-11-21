# Prime-neutral predecessor tags on the literal Goldbach pairs

Let $P$ be a sufficiently large even integer, $L=\log P$, $H=\log L$, $I=[P/3,2P/3]$. Write $\Sigma_P=\mathfrak S(P)|I|/L^2$ with the usual binary singular series. No zero-free hypothesis and no bilinear estimate are required in this note.

Fix $K$ and $J\asymp_K H$. For $1\le i\le K,1\le j\le J$ take pairwise disjoint prime sets $\mathcal P_{ij}$ in $[\exp(L^{.1}),\exp(2L^{.2})]$, each having reciprocal mass $V_{ij}\in[1/4,1/2]$, with **all** divisors of $P(P-1)$ excluded. The separated full intervals of [Jiang–Lau–Lü, (2.1)–(2.5)](https://arxiv.org/html/2611.12467v2#S2) give such choices after removing those primes: the lost mass is $O(L\exp(-L^{.1}))$ from any interval, whose initial mass for split primes tends to $\frac12\log 2$. Put
$$ W_j(t)=\prod_{i=1}^K\frac{\sum_{\ell\in\mathcal P_{ij}}{\bf1}_{\ell|t}}{V_{ij}},
 \qquad \bar W(t)=J^{-1}\sum_j W_j(t).$$
For every even $P$ as above there is **absolute comparison on the expected scale**, namely
$$
 \sum_{\substack{p+q=P\\p,q\ {\rm prime}\\p\in I}}
       |\bar W(q-1)-1|\ll_K\Sigma_P/\sqrt H.                         \tag{1}
$$
This uses the genuine prime pairs without presupposing their existence or abundance. It does not bound an error relative to their *actual* count if that count is tiny. In particular a uniform strict lower $\ge c\Sigma_P$, for any absolute $c>0$, for the genuine prime-pair count weighted by $\bar W(q-1)$ would imply binary Goldbach for all sufficiently large even $P$. On any sequence with a true pair count $\gg\Sigma_P$, the relative loss in the weighted comparison tends to zero. The previous projected mean-square control that put tags on $q$ itself did **not** preserve a prime $q$.

## A common nonnegative upper bound with an evaluable variance

Use the usual two-dimensional upper beta sieve. More explicitly take $z_0=P^{1/100}$ and level $D=P^{1/10}$; increasing the fixed ratio 10 if desired by reducing $1/100$ is immaterial. There are real coefficients $|\lambda_d^+|\le1$ supported on squarefree $d\le D$ with primes $\le z_0$, with
$$ B(n)=\sum_{d|n(P-n)}\lambda_d^+\ \ge {\bf1}_{(n(P-n),\,\prod_{r\le z_0}r)=1}\ge0. $$
For squarefree $d$ write $\nu(d)=\prod_{r|d}\nu(r)$ where $\nu(r)=1$ at $r|P$ and $2$ otherwise. Standard dimension-two upper sieve gives
$$ 0\le M_0=\sum_{d\le D}\lambda_d^+\nu(d)/d
       \ll \prod_{r\le z_0}(1-\nu(r)/r)
       \ll\mathfrak S(P)/L^2.                                        \tag{2}$$
Here the beta-sieve hypothesis follows uniformly from the usual Mertens product, using $\nu(r)\le2$ and $\nu(2)=1$. This is only an upper bound with an absolute constant, not the fundamental lemma with vanishing error at fixed level ratio. Nonnegativity of $M_0$ also follows by averaging $B$ over a common period. On the central interval actual primes $n,P-n$ exceed $z_0$, so $B(n)\ge1$ there. One source is Friedlander–Iwaniec, *Opera de Cribro*, upper beta sieve.

For every squarefree union $a$ of at most $2K$ prime tags (including $a=1$),
$$
 \sum_{\substack{n\in I\\n\equiv1\bmod a}}B(n)
 =\frac{|I|}{a}\left(M_0+O_K(e^{-L^{.1}}L^{2})\right)
     +O(D(1+\log D)).                                                 \tag{3}
$$
If $r|a$ then $n=1\bmod r$ and $P-n=P-1\ne0\bmod r$. Thus terms with $(d,a)>1$ are genuinely absent. For all other terms CRT gives exactly $\nu(d)$ classes modulo $ad$, so the count is $|I|\nu(d)/(ad)+O(\nu(d))$. The cost to replace $\sum_{(d,a)=1}$ by the same $d$-main as for $a=1$ is bounded, inside the parentheses, by
$$ \sum_{r|a}\frac{2}{r}\prod_{\ell\le z_0}(1+2/\ell)\ll_K e^{-L^{.1}}L^2 .$$
Finally $\sum_{d\le D}\nu(d)\le \sum_{d\le D}\tau(d)\ll D(1+\log D)$. These bounds do not use monotonicity of the signed sieve coefficients, just their absolute bounds. They use one and the same positive majorant throughout the squared test.

Expand $(\bar W(n-1)-1)^2$ and use (3) termwise. Repeated equal primes in $W_j^2$ are counted once in the squarefree lcm $a$. For each component the reciprocal sum over ordered pairs in the same set is $V+V^2-\sum_{\ell}1/\ell^2\le V+V^2$, so that the normalized coefficient of $W_j^2$ in the ordinary harmonic model is $O_K(1)$. For $i\ne j$ disjointness gives exact harmonic coefficient $1$ for $W_iW_j$. Each linear coefficient also has harmonic value $1$. The absolute harmonic coefficients of the expansion have total $O_K(1)$. Thus the total coefficient of $|I|M_0$ is $O_K(1/J)$, while the errors from the coprimality replacement total $O_K(Pe^{-L^{.1}}L^2)$. There are at most $\exp(O_K(L^{.2}))H^2=P^{o(1)}$ individual label tuples with their bounded normalized weights, so even the total of all rounding errors is $P^{.1+o(1)}$. We conclude, by (2) and nonnegativity,
$$
 \sum_{\substack{n\in I\\n,P-n\ {\rm prime}}}
       (\bar W(n-1)-1)^2 \le \sum_{n\in I}B(n)(\bar W(n-1)-1)^2
 \ll_K \Sigma_P/H .
$$
Also $\#\{n\in I:n,P-n\ {\rm prime}\}\le\sum_{n\in I}B(n)\ll\Sigma_P$ by (3). Cauchy gives (1). In particular at most $O_K(\Sigma_P/H)$ genuine pairs have **no full family** of predecessor tags at all. This last statement remains compatible with zero genuine pairs.

## The precise new quadratic test, and why an old bound does not settle it

The normalized quantity whose positive lower would suffice is
$$
 T(P)=\frac1J\sum_{j=1}^J\frac1{\prod_i V_{ij}}
 \sum_{a\in\mathcal A_j}
 \sum_{\substack{h\ge1\\P-1-ah\in I}}
       \Lambda(P-1-ah)\Lambda(1+ah),
 \qquad \mathcal A_j=\{\prod_i p_i:p_i\in\mathcal P_{ij}\}.             \tag{4}
$$
Indeed it is the tagged, log-weighted actual count up to $P^{1/2+o(1)}$ from proper prime powers in the two forms, bounding the tags by the divisor bound for fixed $K$. The two prime logarithms are uniformly $(1+O(1/L))L$. Hence $T(P)\ge c\mathfrak S(P)|I|$ for every sufficiently large even $P$ would suffice. We do not have that inequality.

For example, after a Vaughan Type II expansion in the first factor, put $R=P-1$. The inner equation is $mn=R-ah$. A divisor term $d|1+ah$ in the second factor forces $(ah,d)=1$ and $h\equiv-\bar a\bmod d$. Its exact insertion is
$$
 \frac1{\phi(d)}\sum_{\chi\bmod d}\overline{\chi}(-1)
                 \sum_h\chi(h)\!\!\sum_{\substack{a,m,n\\mn=R-ah}}
                         \chi(a)\,\eta(a/Y)\alpha_m\beta_n .           \tag{5}
$$
Endpoint cuts are understood. In particular both the tag and the residual receive the **same** character. Testing a mean square only against a bounded function of $h$ cannot discard $\Lambda(1+ah)$. Even a uniform saving $O_A(PL^{-A})$ for (5) separately for each $d$ would not control polynomially many Möbius divisor coefficients in (4). The two-prime marginal upper sieve proving (1) supplies neither a lower for (4) nor a signed estimate for that correlated collection of moduli.
