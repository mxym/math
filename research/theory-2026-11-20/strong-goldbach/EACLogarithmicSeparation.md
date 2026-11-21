# A logarithmic separation between the two smaller primes

Let $N=p+q^d=q+p^er=r+p^b$, with the prime and exponent hypotheses of the [first-power theorem](EACThreeExponentGaps.md). The largest prime occurs just once. **Uniformly**
$$ \log q\gg \frac{(\log p)^2}{\log\log(3p)}. \tag{1} $$
Consequently the middle prime in an arbitrary three-label exceptional autonomous component (including a repeated largest factor) satisfies, for $L=\log N$,
$$ \log(\operatorname{mid} C)\gg L^{2/5}/[\log(2L)]^{3/5}. \tag{2} $$
Here the component is taken in [Bożek’s actual factorization graph](https://arxiv.org/abs/1909.09900v1), not an arbitrary three-vertex directed graph. The constants are absolute. Neither bound excludes all three-label components. This proof uses divisibility, a short formal expansion at $p=1$, and bounded-order derivatives, not a uniform-in-exponents claim from fixed-signature Siegel.

Put $P=p^e$, $B=P-1$, $x=p-1$, and $k=\lceil\log q/\log x\rceil$. The elementary theorem gives $P<q$, so $e\le k$. Also $b\ll kd$ and $d\ll(\log p)(\log P)\log(2d)$ from the weighted rational Matveev estimate in [EACCoprimePurePowers.md, §1](EACCoprimePurePowers.md). Constants in the argument below never depend on the integers $k,d,e,b$.

### A bounded-digit polynomial for the actual q

Use a formal variable T and write $H=(1+T)^e-1$, $V=(1+T)^{e+b}$. The exact numeric equation is
$$ q+H(x)(q^d+1+x)=V(x). \tag{3} $$
There is a unique formal solution $Y\in\mathbb Z[[T]]$ of $Y+H(Y^d+1+T)=V$ with $Y(0)=1$: the coefficient of order $j$ is determined from lower ones since $H(0)=0$. We need a uniform coefficient bound. There exists an absolute $C$ such that with $A=Cd(e+b+1)$ one has $|[T^j]Y|\le2A^j$. Indeed, for $|T|\le1/A$ the map $y\mapsto V-H(y^d+1+T)$ sends $|y-1|\le1/d$ into itself and has derivative of modulus $\le1/2$ there. Use $|(1+T)^l-1|\le2l|T|$ for $l|T|\le1/2$ and $|y|^d\le\exp(1)$. Iteration from $1$ converges uniformly on the disk to the holomorphic branch with $|Y|\le2$, and Cauchy's estimate proves the bound.

Let $Q_{<k}$ be the truncation of $Y$ through order $k-1$. Then $q\equiv Q_{<k}(x)\pmod{x^k}$. Indeed substituting the truncation solves the equation modulo $T^k$; at $T=x$ the difference of the two sides with $Q_{<k}(x)$ and $q$ factors as their difference times $1+H(x)\sum q^iQ_{<k}(x)^{d-1-i}$, coprime to $x$ since $x\mid H(x)$. Therefore
$$ Q(T)=Q_{<k}(T)+wT^k\in\mathbb Z[T],\qquad Q(x)=q,\quad Q(0)=1. $$
From $q\le x^k$ and $x\ge2$, $|w|\le1+2\sum_{j<k}A^j x^{j-k}\le (4A)^k$. After an absolute enlargement of $A$, we thus have $|[T^j]Q|\le A^j$ for $1\le j\le k$.

Put $W=Q+H(1+T)$ and define the polynomial $F=H Q^d+W-V$. Then $F(x)=0$. For $|T|\le1/(C' d A)$, the coefficient bound gives $|Q(T)-1|\le1/d$ by summing a geometric series. On this disk $|Q|^d,|H|,|V|,|W|,|F|$ are absolutely bounded. Thus for all $j\ge0$,
$$ |[T^j]F|\le C_0(C'dA)^j.$$
With $J=4k+10$, all coefficients of order at most $J$ are bounded by $(C''kd)^{C''k}$ because $e\le k,b\ll kd$. If $x$ exceeds this bound, all of these coefficients must vanish: evaluate $F(x)$ modulo $x$ to get $[T^0]F=0$ as its magnitude is $<x$, divide by $x$ and repeat. Thus $\operatorname{ord}_0(F)>J$.

### A zero estimate independent of d and b

We show such a zero forces $F\equiv0$. Write $D=d/dT$ and
$$ E=(1+T)DF-(e+b)F=Q^{d-1}A_0+B_0,$$
$$ A_0=(1+T)(H'Q+dHQ')-(e+b)HQ,\qquad B_0=(1+T)W'-(e+b)W. $$
Here $A_0(0)=e\ne0$, $\deg A_0\le2k$, $\deg B_0\le k+1$. If the indicated polynomials vanish identically the following identities retain their meaning. Apply $Q A_0 D-[(d-1)Q'A_0+QA_0']$ to $E$. The $Q^{d-1}A_0$ term vanishes, and the result, involving $B_0$ alone, has degree at most $4k+1$. But it vanishes through order at least $J-2$ at $0$, hence is identically zero. The rational function $B_0/(Q^{d-1}A_0)$ therefore has derivative zero and is constant. Now $E$ is a constant multiple of $Q^{d-1}A_0$, a unit at zero, while $E(0)=0$. Thus $E=0$. Similarly $D(F/V)=0$, and $F(0)=0$ gives $F=0$.

### The impossible polynomial identity

Translate from $T$ to $X=1+T$ and denote $Q(X-1)$ by $R(X)$. The identity becomes
$$ (X^e-1)(R(X)^d+X)+R(X)=X^{e+b}. \tag{4} $$
Here $R\in\mathbb Z[X]$. If $R$ is constant, $Q(0)=1$ forces $R=1$, conflicting with $Q(x)=q$. Write $l=\deg R\ge1$. Degree comparison gives $dl=b$ and its leading coefficient $a$ satisfies $a^d=1$ ($dl\ge2$ dominates the isolated $X$). But $b>ed$ in the first-power orientation (or: if $b\le ed$, then $P^d\ge p^b$ and the identity $B(q^d-p^b)=p^b-pB-q$ contradicts $q\ge P+2$, since $(P+2)^d-P^d\ge2dP^{d-1}>P^d/B$). Hence $l>e$. From (4) at $+\infty$,
$$ R^d=X^{b}\,[1+X^{-e}+o(X^{-e})]. $$
Indeed $R/X^{e+b}=o(X^{-e})$ as $l<b$, and $X(X^e-1)/X^{e+b}=O(X^{1-b})=o(X^{-e})$ as $b=dl\ge2(e+1)$. The coefficient of $X^{l-e}$ in $R$ is $a/d$ (all intervening lower coefficients vanish), impossible for an integer polynomial. Thus (4) cannot hold.

This proves $\log(p-1)\ll k\log(2kd)$. If $k\ge\log p$ we already have (1). Otherwise $e\le k<\log p$ and $d\ll (\log p)^3\log(2d)$, whence $\log(2d)\ll\log\log(3p)$. Consequently $k\gg \log p/\log\log(3p)$, which yields (1) using $\log q>(k-1)\log(p-1)$ and absorbing small $p$ in the constant.

Finally put $Y=\log q$. Weighted Matveev and $P<q$ give $L\ll(\log p)Y^2\log(2L)$. By (1), $\log p\ll\sqrt{Y\log(2L)}$, so $L\ll Y^{5/2}[\log(2L)]^{3/2}$, yielding (2). If the largest prime instead occurs at least twice, [EACRepeatedFixedLabel.md](EACRepeatedFixedLabel.md) gives $L\ll(\log p)(\log q)$; the middle of the three labels is then at least $\exp(c\sqrt L)$.

For comparison, [Kelanemer's 2026 preprint record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) describes low-dimensional exponent matrices in a terminal-island framework with global Goldbach hypotheses. The full text could not be checked in this comparison. The inequalities here concern the local component without assuming the center is a Goldbach counterexample; they use only the exact displayed relations and the cited logarithmic estimates. No claim of priority over unread material is made.
