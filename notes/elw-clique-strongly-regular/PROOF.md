# Proof of the truncated clique inequality on strongly regular graphs

Let $G$ be a finite simple strongly regular graph on at least one vertex, and let $w=\omega(G)$. We prove [the inequality stated in the overview](README.md) for $\ell=\min\{w,n^+\}$. The graph need not be primitive.

## 1. Reduce to a concave function on an interval

An imprimitive strongly regular graph is a union of equal cliques or its complement: if the graph is disconnected, then $\mu=0$ and every component is complete. The same argument applies when the complement disconnects. For $c$ disjoint copies of $K_p$, $p\ge2$, the full positive-square sum is $c(p-1)^2=2m(1-1/p)$, which bounds the truncated sum. For a complete $c$-partite graph with equal parts of size $p$, $c\ge2$, the sole positive eigenvalue is $d=(c-1)p$ and $d^2=nd(1-1/c)$. If there are no edges, $w=1$ and the sum is empty.

Now assume both $G$ and its complement are connected. Write its parameters as $(n,d,\lambda,\mu)$ and its eigenvalues as $d,r,-t$ with multiplicities $1,f,g$. Thus $d>r>0$, $t>1$, $0<\mu<d$. These are standard primitive SRG facts; for instance, an induced three-vertex path forces the least eigenvalue below $-1$. Put $h=d-\lambda$ and $b=n-2d+\lambda$. The restricted-eigenvalue quadratic and the count $(n-d-1)\mu=d(d-\lambda-1)$ give
$$
\mu=d-rt,\quad \lambda=\mu+r-t,\quad h=(r+1)(t-1)+1,
\qquad n=d+h+b,\quad \mu b=rt(h-1).
$$
In particular $d=rt(1+(h-1)/b)$. The common-neighbor counts for nonadjacent and adjacent vertices of the complement are respectively $b\ge1$ and $b+t-r-2\ge0$. The order and multiplicities are
$$
n=\frac{(d-r)(d+t)}{\mu},\qquad
f=\frac{d(d+t)(t-1)}{\mu(r+t)},\qquad
g=\frac{d(d-r)(r+1)}{\mu(r+t)}.
$$
Here the multiplicities follow from $1+f+g=n$ and $d+fr-gt=0$. If $r<t$, then $t-r=\mu-\lambda$ is a positive integer even if the individual roots are irrational. If $r\ge t$, both roots are integral: irrational conjugate roots of their monic integer quadratic would have equal multiplicity, contradicting $d+f(r-t)=0$. Rational roots are algebraic integers. Thus $t\ge2$ in that branch.

Each neighborhood has $d$ vertices, is $\lambda$-regular, and has clique number at most $w-1$. Turán's theorem gives $\lambda\le d(1-1/(w-1))$. Hoffman's independent-set bound in the complement gives $w\le n(r+1)/(n-d+r)=1+d/t$. On coordinates of a clique the quadratic form $A+I$ is the positive-semidefinite all-ones form; it is negative definite on a $g$-dimensional subspace. Therefore $w\le n-g=f+1$ by dimension counting. Thus
$$
L:=1+d/h\ \le w\ \le\min\{D,1+f\},\qquad D:=1+d/t.
$$
There are $f+1$ positive eigenvalues, so $\ell=w$. This inertia reduction, which [Elphick–Linz–Wocjan, §4.2.3](https://arxiv.org/pdf/2101.05229#page=9) obtain from Cvetković's bound, gives the target $F(w)\ge0$, where
$$F(x)=nd(1-1/x)-d^2-(x-1)r^2.$$
Since $F''(x)=-2nd/x^3<0$ for $x>0$, it suffices to show $F(L)\ge0$ and at least one of $F(D)\ge0$ or $F(f+1)\ge0$.

## 2. The lower endpoint

Multiplying $F(L)$ by $h(h+d)/d$ gives $B(b)=dhb-(d+h)r^2$. Substituting $d=rt(1+(h-1)/b)$, the nonconstant terms in $B$ are $rthb-r^3t(h-1)/b$, so it is strictly increasing in $b>0$.

* If $r<t$, evaluate at $b=1$: $B(1)=rh[t(h-r^2)-r]\ge0$, since $h-r^2=(r+1)(t-r)$, $t-r\ge1$, and $t>1$.
* If $r\ge t\ge3$, set $u=r-t$. We have $b\ge u+2$ and
$$
t[h(u+2)-r^2]-rh=u^2(t^2-3t+1)+u(t^3-2t^2-t)\ge0.
$$
  Hence $hb-r^2\ge rh/t>0$. Using $d\ge rt$ gives $B(b)=d(hb-r^2)-hr^2\ge0$.
* If $r\ge t=2$, then $h=r+2$ and $b\ge r$. For $2\le r\le6$, $B(b)\ge B(r)=r(-r^2+6r+4)>0$. For $r\ge7$, [Neumaier's $\mu$-bound](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf), Theorem 1.3.15, gives $\mu\le t^3(2t-3)=8$. It applies because the graph is primitive and the least eigenvalue is integral. Thus $b=2r(r+1)/\mu\ge2r$, so $hb-r^2\ge r^2$; $d\ge h$ follows from $\lambda\ge0$. This proves $B(b)\ge0$.

## 3. The upper endpoint

The identity
$$F(D)=\frac{dr}{\mu t}[dt(t-1)-r\mu]$$
recovers the sign condition in [Elphick–Linz–Wocjan, Eq. (9)](https://arxiv.org/pdf/2101.05229#page=10). Their Type C proof uses that the clique attains $D$; we do not assume the endpoint always has the correct sign. It does if $r\le t(t-1)$ since $\mu\le d$. In particular, $r<t$ implies $r\le t-1<t(t-1)$.

Suppose $r>t(t-1)$, so $r,t$ are integers and $t\ge2$. From $nd=d^2+fr^2+gt^2$,
$$
F(f+1)\ge0\quad\Longleftrightarrow\quad
(f+1)gt^2\ge nd\quad\Longleftrightarrow\quad
f+1\ge\frac{(r+t)(d+t)}{(r+1)t^2}.\tag{1}
$$
Set $S=r-t^2+2t>0$. The [first Krein condition](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf#page=40),
$(r+1)(d+r-2rt)\le(d+r)(t-1)^2$, bounds the degree by
$$rt\le d\le K:=\frac{r[(2t-1)r+t^2]}{S}.$$

### 3a. $t\ge3$ and $r\le t^3$

Replacing $f+1$ by $f$ on the left of (1) is sufficient; after clearing positive factors this says
$$J(d):=d(t-1)(r+1)t^2-(d-rt)(r+t)^2\ge0.$$
The function $J$ is affine, $J(rt)>0$, and
$$
S J(K)=r^2(t-1)\{r(2t^3-2t^2-2t-r)+t^4-2t^2\}.
$$
This is nonnegative since $2t^3-2t^2-2t\ge t^3\ge r$ for $t\ge3$.

### 3b. $r\ge t^3$ and $t\ge2$

The [absolute bound](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf), Proposition 1.3.14, gives $2n\le f(f+3)$, so
$$
f+1\ge 2n/f-2=\frac{2(d-r)(r+t)}{d(t-1)}-2.
$$
Substituting this lower bound into (1) and clearing positive factors shows that it suffices to prove
$$
H(d):=2(d-r)(r+t)(r+1)t^2-2d(t-1)(r+1)t^2-d(t-1)(r+t)(d+t)\ge0.
$$
This is concave in $d$, and $H(rt)=rt^2(r+1)(r-t)(t-1)\ge0$. To check $H(K)$, put $u=r-t^3$. Direct expansion gives $S^2H(K)/(r(t-1))=\sum_{i=0}^4 c_i u^i$ with
$$
\begin{aligned}
c_4&=4t-1, \\
c_3&=2t^2(6t^2+5),\\
c_2&=t^2(12t^5+6t^4+26t^3+t^2+10t+5),\\
c_1&=2t^3(2t^7+4t^6+11t^5+t^4+9t^3+6t^2+3),\\
c_0&=t^5(t+1)(3t^6+3t^5-2t^4+10t^3-3t^2+3t+2).
\end{aligned}
$$
All coefficients are positive for $t\ge2$: in the last line group $3t^5-2t^4$ and $10t^3-3t^2$. Since $u\ge0$, this proves $H(K)\ge0$, and concavity gives (1).

### 3c. $t=2$ and $2<r<8$

It remains to show that the Delsarte endpoint works here. Its sign condition becomes $\mu(r-2)\le4r$. It holds for $r\le4$ since $\mu\le8$. For $r=5,6,7$, a violation would require $\mu$ in $\{7,8\},\{7,8\},\{6,7,8\}$ respectively. Since $b=2r(r+1)/\mu$ is integral, the only surviving $(r,\mu)$ are $(6,7),(7,7),(7,8)$. Their multiplicities
$$f=\frac{(\mu+2r)(\mu+2r+2)}{\mu(r+2)}$$
would be $57/8,23/3,22/3$, respectively; none is an integer. This exhausts all cases and proves the theorem. $\square$
