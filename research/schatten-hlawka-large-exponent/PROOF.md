# Large-exponent Hlawka constants: order for Schatten classes, exact diagonal asymptotics

**AI-assisted draft, independently checked within the same project; not externally peer reviewed.** This is a partial answer to Audenaert–Kittaneh's optimal-constant problem, not determination of the exact noncommutative constant. It uses two 2026 results of Ezzeri Esa as prior work; neither the finite-constant theorem nor the cyclic variational formula is new here.

For a norm $N$, write
$$
T_N=\sum_{i=1}^3N(X_i)-N(X_1+X_2+X_3),\quad
D_N=\sum_{i<j}\{N(X_i)+N(X_j)-N(X_i+X_j)\}.
$$
Let $C_p$ be the smallest number such that $T_N\le C_pD_N$ for all rectangular finite-dimensional complex matrices, with $N(X)=(\operatorname{Tr}|X|^p)^{1/p}$. Let $K_p$ be the corresponding constant for complex diagonal matrices, uniformly over finite dimensions.

Set $L=\log2$, $J=\log3$. Our conclusions are
1. For every $1<p<\infty$, $C_p\le2\max\{p,p/(p-1)\}$. In particular $C_p=\Theta(p)$ as $p\to\infty$, with
$$
\frac1{3L}\le\liminf_{p\to\infty}\frac{C_p}{p}\le
\limsup_{p\to\infty}\frac{C_p}{p}\le2.
$$
The lower slope is already implicit in Esa's displayed $t=p^{-1/p}$ test; the unrestricted upper order follows by making the scalar step of Esa's transfer quantitative. We do not establish a limit for $C_p/p$. The same upper bound controls the total deficit of **any finite number of matrices** by the sum of all pair deficits, with no dependence on that number. This is the quantitative corollary of the transfer for the multi-summand extension suggested just after Eq. (50) of the published problem list.
2. For the sharp diagonal constant the asymptotic expansion is
$$
K_p=\frac{p}{3L}-\frac{\log p}{6L}
       +\frac{\log L+2L-J-1}{6L}
       +O\!\left(\frac{(\log p)^2}{p}\right).
$$
For all sufficiently large $p$, Esa's one-variable cyclic maximum has exactly one maximizing parameter on $[1/2,2]$. It satisfies
$$
t_p=1-\frac{\log p-\log L}{p}
             +O\!\left(\frac{(\log p)^2}{p^2}\right),\qquad
  t_p^p=\frac Lp+O\!\left(\frac{\log p}{p^2}\right).
$$
This asserts uniqueness of a scalar parameter of the specified family, not of every maximizing matrix triple. It addresses $p\to\infty$, not the distinct trace-endpoint obstruction.

## 1. A uniform scalar bound and the transfer to all matrices

Put $a=1/p$, $b=1-a$, $\alpha=\min(a,b)$, $\beta=\max(a,b)$. The power Bregman divergence of $F(s)=|s|^p/p$ on the real line is $F(s)-F(t)-F'(t)(s-t)$. Under the scalar Mazur change $u=\operatorname{sgn}(s)|s|^{p/2},\ v=\operatorname{sgn}(t)|t|^{p/2}$ it is
$$
B(u,v)=a|u|^2+b|v|^2-\operatorname{sgn}(uv)|u|^{2a}|v|^{2b}.
$$
We claim
$$
ab|u-v|^2\le B(u,v)\le2\beta|u-v|^2. \tag{1}
$$
For equal signs write $r=|u|,\ s=|v|$ and assume $a\le1/2$, interchanging the variables and $a,b$ if necessary. The standard refined and reverse Young bounds imply (and the following short argument shows directly) that the centered Young difference lies between $a(r-s)^2$ and $b(r-s)^2$. For the first inequality, weighted AM–GM gives $r^{2a}s^{2b}\le2ars+(1-2a)s^2$. For the second, the tangent inequality for the convex power $x^{2b}$ at one gives $r^{2a}s^{2b}\ge2brs+(1-2b)r^2$; zero endpoints follow by continuity. For opposite signs, the weighted quadratic term alone bounds $ab(r+s)^2$ from below because their difference is $(ar-bs)^2$. Weighted AM–GM bounds $B$ above by $2(ar^2+bs^2)\le2\beta(r+s)^2$. This proves (1).

For completeness we reconstruct the previously used transfer. Hermitian dilations $\left(\begin{smallmatrix}0&X\\X^*&0\end{smallmatrix}\right)$ preserve real-linear combinations and multiply every Schatten $p$ norm by the same $2^{1/p}$, so it is enough to treat Hermitian matrices. Define $\psi_p(H)=\operatorname{sgn}(H)|H|^{p/2}$ by spectral calculus and $\Phi(H)=\operatorname{Tr}|H|^p/p$. For two Hermitians, the trace Bregman expression $\Phi(H)-\Phi(G)-\operatorname{Tr}[F'(G)(H-G)]$ and the squared Hilbert–Schmidt distance $\|\psi_p(H)-\psi_p(G)\|_2^2$ are respectively sums of their scalar versions over pairs of eigenvalues, weighted by squared overlaps of the two orthonormal eigenbases. Thus (1) remains valid with the same constants for those expressions.

For any finite list of matrices, let $w_i=\|X_i\|_p$, $U_i=X_i/w_i$, omitting zero terms. Minimizing the sum of $w_i$ times these Bregman expressions with $(H,G)=(U_i,G)$ over $\|G\|_p=1$ gives exactly
$$
\sum_i w_i-\|\textstyle\sum_iX_i\|_p.
$$
Indeed both power potentials agree on the sphere and $\operatorname{Tr}F'(G)G=1$. As $G$ ranges over the Hermitian $p$-sphere, $F'(G)$ ranges over the Hermitian conjugate exponent unit sphere; ordinary norm duality gives the minimization, also if $\sum X_i=0$. Likewise $\psi_p(G)$ ranges over the whole Hermitian Hilbert–Schmidt sphere; the minimum of $\sum_i w_i\|\psi_p(U_i)-\psi_p(G)\|_2^2$ equals $2(\sum_iw_i-\|\sum_iw_i\psi_p(U_i)\|_2)$. All-zero lists are immediate. Hence the Schatten deficit for any finite list lies between $2ab$ and $4\beta$ times the corresponding Hilbert deficit of the same vectors $w_i\psi_p(U_i)$. Apply the classical Hilbert-space Hlawka inequality to these vectors, with the upper bound for triples and lower bound for pairs, to obtain $C_p\le 2\beta/(ab)=2/\alpha$. This reasoning does not divide by a possibly zero pair-deficit sum.

More generally, if $k\ge2$, write $T_k=\sum_{i=1}^k N(X_i)-N(\sum_iX_i)$ and $D_k=\sum_{i<j}(N(X_i)+N(X_j)-N(X_i+X_j))$. The argument for finite lists gives $T_k\le2\max(p,p/(p-1))D_k$ by the Hilbert multi-vector Hlawka inequality of Adamović, recalled in the published problem list as Eq. (50). For a direct check of that last ingredient on the real line, the total deficit is twice the smaller of the total positive and total negative magnitudes, while the pair-deficit sum is twice the sum of the minima over opposite-sign pairs. If the positive total is the smaller, each positive magnitude $d$ contributes at least $d$, because $\sum_{j}\min(d,e_j)\ge\min(d,\sum_j e_j)=d$ for the negative magnitudes $e_j$. The other case is symmetric. Project onto a standard real Gaussian in the finite-dimensional real span of the Hilbert vectors and integrate this scalar inequality, using $\mathbb E|\langle g,v\rangle|=\sqrt{2/\pi}\|v\|_2$. The uniform upper order at infinity cannot be improved for any $k\ge3$, since zero-padding preserves both deficits of a triple.

## 2. The diagonal variational problem and localization

Use Esa's previous theorem for real $p\ge256$: $K_p=\max_{1/2\le t\le2} R_p(t)$ for
$$
A=(2+t^p)^{1/p},\quad B=(2^p+2|1-t|^p)^{1/p},\quad c=3^{1/p},\qquad
R_p(t)=\frac{3A-c(2-t)}{6A-3B}. \tag{2}
$$
These are the norms in the cyclic family $(-t,1,1),(1,-t,1),(1,1,-t)$. The denominator is positive by strict convexity. For $1/2\le t\le2$,
$$
B=2+O(2^{-p}/p),\qquad |B'|=O(2^{-p}),
$$
by the explicit formula (all asymptotic estimates below are for real $p\to\infty$). Since $A-1\ge e^{L/p}-1\ge L/p$, replacing $B$ by 2 in (2) is a uniform $O(p2^{-p})$ change in $R_p$. Set $H=3-2c+ct$. The simplified ratio is
$$
\widetilde R=\tfrac12+\frac{H}{6(A-1)}. \tag{3}
$$

Taking $t=p^{-1/p}$ in (3) gives $R_p(t)/p\to1/(3L)$. To locate all maximizers, extract any subsequence with $t_p\to t_0$ by compactness. If $t_0>1$, $A-1$ is bounded below and $R_p(t_p)/p\to0$. If $t_0<1$, $p(A-1)\to L$ and $R_p(t_p)/p\to(1+t_0)/(6L)<1/(3L)$. Hence $t_p\to1$. In that case $H\to2$, so $p(A-1)\ge\log(2+t_p^p)$ forces $t_p^p\to0$ at a maximizer: otherwise a subsequence has $t_p^p\ge d>0$ and its limsup slope is at most $1/[3\log(2+d)]$. Thus all maximizing points are eventually interior to $(1/2,1)$, and $K_p/p\to1/(3L)$. In combination with (1) and diagonal inclusion this proves the order claimed for unrestricted matrices. The argument up to this point needs no assumption that a maximizer is unique.

## 3. Uniqueness in the cyclic family

At any global maximizing parameter let $K=K_p$ and consider the level-set function
$$
F_K(t)=(3-6K)A+3KB-c(2-t).
$$
Its global maximum is zero. For $1/2<t<1$ and $p>2$,
$$
A''=2(p-1)t^{p-2}(2+t^p)^{1/p-2},\quad
B''=2(p-1)2^p(1-t)^{p-2}(2^p+2(1-t)^p)^{1/p-2}.
$$
The first is at least $(2/9)(p-1)t^{p-2}$, while the second is at most $4(p-1)2^{-p}(1-t)^{p-2}$. Thus $B''/A''\le18\cdot 2^{-p}$ throughout this interval. Because $K_p$ grows linearly, $F_K''=(3-6K)A''+3KB''<0$ there for large $p$. All maximizers lie there by Section 2; strict concavity gives uniqueness.

## 4. Stationarity and expansion

At the maximizing point set $s=t^p$. Differentiating (3) and comparing to (2) introduces an error exponentially small times a polynomial in $p$. More explicitly, let $\delta=(B-2)/2$, so $R_p=1/2+(H+3\delta)/[6(A-1-\delta)]$. The numerator of the derivative of its last fraction, up to a fixed factor, is
$$
(c+3\delta')(A-1-\delta)-(H+3\delta)(A'-\delta'),
$$
so stationarity gives $HA'=c(A-1)+O(2^{-p})$ (here $A,H,A'$ are bounded near this point). Since $A'=A t^{p-1}/(2+s)$,
$$
t^{p-1}=\frac{(2+s)c(A-1)}{HA}+O(2^{-p}). \tag{4}
$$
Using $t\to1,\ s\to0,\ p(A-1)\to L,\ H\to2$ gives $t^{p-1}\sim L/p$, hence $s\sim L/p$ and $t=1+O(\log p/p)$. Substituting these preliminary rates into (4) yields $t^{p-1}=(L/p)(1+O(\log p/p))$: indeed $A-1=L/p+O(p^{-2})$, $H=2+O(\log p/p)$, $s=O(1/p)$. Taking logs and dividing by $p-1$, or multiplying by $t$, respectively proves the two stated estimates on $t_p$ and $s$.

Let $u=\log p-\log L$. At this $t$ the estimates imply
$$
A=1+\frac Lp+\frac{L+L^2}{2p^2}
       +O\!\left(\frac{\log p}{p^3}\right),\qquad
3A-c(2-t)=2+\frac{3L-J-u}{p}
       +O\!\left(\frac{(\log p)^2}{p^2}\right).
$$
Indeed $\log(2+s)=L+s/2+O(s^2)$, and $c=1+J/p+O(p^{-2})$. Substitution into (2), using the exponentially small $B-2$, gives the claimed expansion, including its constant term. ∎

**Limits.** No uniqueness of matrix extremizers is asserted, and (1) does not say that the noncommutative worst case is diagonal or that the coefficient two is sharp. The interval below $p=2$ is not classified; the first bound near $1$ is only $O(1/(p-1))$, not an endpoint equivalent. See [SOURCES.md](SOURCES.md) for related earlier bounds and the extent of the novelty check.
