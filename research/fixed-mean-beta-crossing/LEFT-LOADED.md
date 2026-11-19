# The binomial left-loaded conjecture

Yongxian Zhang (张永贤). AI-assisted companion note; internally checked, not externally peer reviewed, November 19, 2026.

Let $n,m$ be positive integers with $n\ge2m$, and let $X$ have the $\operatorname{Bin}(n,m/n)$ distribution. Put $\alpha_i=\Pr(X\le m-i)-\Pr(X\ge m+i)$ for $1\le i\le m$. [Fokkink, Papavassiliou and Pelekis (2022), Definition 1.2 and Conjecture 4.1](https://www.math.uni.wroc.pl/~pms/files_doi/g00050/g00050.pdf) ask whether every such $X$ is left-loaded. Condition (L1) means that for some $1\le\ell\le m$, $\alpha_i\ge0$ for $i\le\ell$ and $\alpha_i\le0$ for $i>\ell$; condition (L2) means that all the partial sums of $\alpha_i$ are nonnegative. They require only one condition. We show both. No assertion about noninteger means or negative binomials is needed.

**Proof.** If $n=2m$, symmetry makes every $\alpha_i$ zero. Otherwise put $u=n-m>m$ and write $b_j=\Pr(X=j)$, extended by zero outside the support. For $0\le j\le m$, set $R_j=b_{m-j}/b_{m+j}$. Then $R_0=1$, and whenever $0\le j<m$ the consecutive binomial-mass ratios give
$$
 \frac{R_{j+1}}{R_j} = \frac{u^2[m(m+1)-j(j+1)]}{m^2[u(u+1)-j(j+1)]}.
$$
All denominators are positive. The numerator minus denominator on the right is
$$
 (u-m)[mu-(m+u)j(j+1)].
$$
It is positive for $j=0$ and decreases strictly with $j$. Thus $R_j$ first increases and then is nonincreasing (it may only increase on the range considered). It starts at 1, so $d_j=b_{m-j}-b_{m+j}$ is nonnegative on an initial segment of $j=1,\ldots,m$ and nonpositive thereafter. For $m<j\le u$ we have $d_j<0$ automatically.

For $1\le i\le u$, define $A_i=\sum_{j=i}^u d_j$, extending the same tail differences to $i>m$, with $A_{u+1}=0$. On the terminal segment where $d_j\le0$ the $A_i$ are nonpositive. On the initial segment the $A_i$ are nonincreasing as $i$ increases because $A_{i+1}=A_i-d_i$. Thus their signs can change only from positive to negative. Moreover $\sum_{i=1}^u A_i=\sum_{j=1}^u j d_j=\mathbb E(m-X)=0$, whereas $A_u=-b_n<0$. Some initial $A_i$ must consequently be positive, and $A_1>0$. Restriction to $1\le i\le m$ gives (L1). Every prefix sum of the full sequence is nonnegative because it has a nonnegative initial segment and a nonpositive final segment with total zero. Restriction proves (L2). $\square$

**Prior boundary.** This is an application of a classical proof of Simmons' inequality, not a new mirror-mass ratio. [Feldheim (1941), §2, pp. 4–6, Eqs. (5)–(9)](https://www.numdam.org/item/JMPA_1941_9_20__1_0.pdf) uses the reflected masses, their first crossing, the extension by zeros and the centered first moment for the first-tail comparison. [Rényi, *Probability Theory* (1970), Ch. III §18, Exercise 35, p. 167](https://real-eod.mtak.hu/12669/) gives the same consecutive-ratio computation and sign threshold $j(j+1)=np(1-p)$ and credits Feldheim. The passage to all tail differences and all their initial sums is the short deduction above; in the terminology of 2022 this gives both conditions, although their conjecture only asks for one. Fokkink–Papavassiliou–Pelekis themselves prove the Poisson statement, some binomial parameter ranges, and the corresponding zero-sum identity in Lemma 2.1. See [SOURCES.md](SOURCES.md) for further comparisons.
