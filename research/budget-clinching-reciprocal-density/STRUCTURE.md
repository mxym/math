# Two distribution classes for two-agent middle-ironed clinching

**Yongxian Zhang.** We use the two-bidder, i.i.d., one-item public-budget welfare problem of Feng–Hartline, with the direct randomized-allocation, deterministic-payment, DSIC and normalized ex-post IR conventions in the companion [explicit counterexample](PROOF.md). The common positive budget is $B$. The value interval is $[0,h]$ with $h>0$; $f>0$ denotes a continuous, possibly unnormalized density there. A threshold pair has $a+b=2B$, $0\le a\le B$. For $B\ge h$, the ordinary efficient second-price auction fits the budget.

* If $1/f$ is strictly concave and nondecreasing, with $f\in C^1[0,h]$, then for **some** $0<B<h/2$ no middle-ironed clinching auction is expected-welfare optimal. The same four-band construction as in the explicit example suffices. This is not an assertion about every budget.
* If $1/f$ is affine and nondecreasing, then for **every** $B>0$ some middle-ironed clinching auction is expected-welfare optimal among all mechanisms in the stated DSIC class. This includes the known uniform case. The proof supplies a dual upper bound valid for allocations that need not exhaust the item.

These are sufficient conditions, not a classification for general reciprocal densities.

## 1. Strictly concave reciprocal: the family fails somewhere

Let $J(u)=\int_u^h(v-u)f(v)dv$ and for $0<b\le h$ put
$$
 K(b)=\frac{f(b)J(b)}b-\int_b^h\frac{f(u)J(u)}{u^2}du
     =-\int_b^h\frac{(fJ)'(u)}u du .
$$
Because $f$ is nonincreasing, $-(fJ)'\ge f(u)\int_u^h f(v)dv>0$ for $u<h$; in particular $K$ is strictly decreasing, with $K(h)=0$ and $K(0+)=+\infty$. Define
$$
 A(a,b)=\frac1{b-a}\int_a^b[(v-a)f(a)+(b-v)f(b)]f(v)dv.
$$
As $b\downarrow0$, $A(0,b)\to0$, while $A(0,h)>0$. By continuity there exists $b_0\in(0,h)$ satisfying $K(b_0)=A(0,b_0)$. Set $B=b_0/2$. The moving-boundary derivative proved in the companion note holds verbatim with $b=2B-a$: the unnormalized welfare gain has derivative
$$G'(a)=(b-a)[A(a,b)-K(b)].$$

To maximize over the whole family, fix $B$ and write $a=B-s$, $b=B+s$ ($0<s\le B$). Then $A(a,b)$ equals
$$2s\int_0^1 [t f(B-s)+(1-t) f(B+s)] f(B+(2t-1)s)\,dt.$$
If $g=1/f$, positivity and concavity give $xg'(x)\le g(x)-g(0)<g(x)$, hence $-xf'(x)/f(x)<1$ for $x>0$. We show that each weighted product in the last display increases with $s$. The logarithmic derivative with respect to $\log s$ of the factor $s$ is $1$. The factor $f(B-s)$ is nondecreasing; $f(B+s)$ loses at most $s/b$ in logarithmic derivative. For $v=B+(2t-1)s$, the other factor $f(v)$ is nondecreasing for $t\le1/2$; for $t>1/2$ it loses at most $(2t-1)s/v\le s/b$. Since $2s/b<1$ for $0<s<B$, the sum of the logarithmic derivatives is positive in the interior. Continuity gives strict increase also up to $s=B$. Thus $A(a,2B-a)<A(0,b_0)=K(b_0)<K(2B-a)$ for $0<a<B$. Continuity at the endpoints yields the unique best family parameter $a=0$.

For small $c,d>0$ use bands $[0,c),[c,b_0-d),[b_0-d,b_0),[b_0,h]$, the same allocation table as in the companion, with $\gamma=c/(2b_0)$ and high-pair advantage $cd/u^2$ for lower report $u$. For $c,d$ small the columns remain monotone. The three top payments in the first three columns are $(b_0-d)/2$, $b_0/2$, and $c/2+b_0(1/2-\gamma)=B$. In the high column, writing the upper payment as in the companion gives $b_0/2-\gamma d+cd/(2b_0)=B$; ties can only decrease it. This proves the same DSIC, ex-post IR and budget properties on every profile.

Relative to $a=0$, the gain increases by full advantage on the lowest versus upper-middle bands; it decreases by $2\gamma$ on the upper-middle versus high bands; on high pairs it increases by $cd/u^2$. Dividing the unnormalized change by $cd$ and letting $c,d\downarrow0$, continuity of $f$ gives, respectively,
$$ b_0 f(0)f(b_0),\qquad -f(b_0)J(b_0)/b_0,\qquad
 \int_{b_0}^h f(u)J(u)u^{-2}du.$$
The sum is $b_0 f(0)f(b_0)-K(b_0)>0$. Indeed, $A(0,b_0)/(b_0f(0)f(b_0))$ is the average over $[0,b_0]$ of $f(v)$ times the chord between $1/f(0)$ and $1/f(b_0)$ at $v$. Strict reciprocal concavity makes this average strictly below one. Hence some positive $c,d$ give a strict gain over the entire family.

For example $f(x)=(1+\epsilon x)^{-1/2}$ on any fixed $[0,h]$ meets the hypotheses for every $\epsilon>0$. These analytic densities converge (after normalization) to uniform as $\epsilon\downarrow0$, even in every fixed $C^k$ norm. When $\epsilon h<3$ the hazard is strictly increasing: with $S(x)=\int_x^h f$, the sign of $f^2+f'S$ is the sign of $2\sqrt{1+\epsilon x}-\sqrt{1+\epsilon h}>0$. We do not assert that all densities in the theorem are MHR.

## 2. Affine reciprocal: an exact welfare dual

Write $1/f(v)=\alpha+\beta v$ with $\alpha>0,\ \beta\ge0$ and set $g(v)=\int_0^v f(z)^2dz$. Direct integration (also for $\beta=0$) gives
$$g(v)-g(t)=(v-t)f(v)f(t). \tag{1}$$
Suppose $0<B<h$. For $0<t\le h$ put $U(t)=\int_t^h(h-z)g'(z)\,dz/z$. On $[\max(0,2B-h),B]$ seek $a$ with $b=2B-a$ and $g(b)-g(a)=U(b)$. The left side minus the right side decreases strictly with $a$, is negative at $a=B$, and is positive at the lower endpoint if that endpoint is positive (then $b=h$). If there is a root, take it and set $k=0$. Otherwise take $a=0,b=2B,k=U(b)-g(b)+g(0)>0$. In either case $0<b<h$, $g(b)-g(a)+k=U(b)>0$, and $k$ can be positive only when the low region is empty.

Let $L=[0,a)$, $M=[a,b)$, $H=[b,h]$, and define
$$ \lambda(t)=
\begin{cases}0&t\in L,\\g(t)-g(a)+k&t\in M,\\U(t)&t\in H.
\end{cases}
\qquad \psi(t)=g(t)-\lambda(t).$$
The price $\lambda$ is nonnegative, and $\psi$ nondecreasing: it equals $g$ on $L$, is constant on $M$, and has derivative $h g'(t)/t$ on $H$. The pieces of $\psi$ meet continuously (if $k>0$ there is no $L$). Moreover
$$\int_t^h[\psi(v)-\psi(t)]dv
=\int_t^h(h-z)\psi'(z)dz=hU(t) \qquad (t\in H). \tag{2}$$

For clarity, define a nonnegative function $m(v,t)$ as follows; omitted cases have value zero:
* If $v>t$ and $v,t\in H$, put $m(v,t)=\psi(v)-\psi(t)$.
* If $v\in H$ and $t\in M$, put $m(v,t)=[\lambda(t)/U(b)] [\psi(v)-\psi(t)]$.

The fraction in the second case belongs to $[0,1]$. From (2) and flatness of $\psi$ on $M$,
$$ \int_0^h m(v,t)dv=h\lambda(t) \quad \text{for all }t, \tag{3}$$
including $t\in L$, where both sides are zero.

To see why these prices certify welfare, we may symmetrize any rival mechanism by exchanging agent labels at random and averaging allocations and payments. The average still obeys the per-profile hard budget, DSIC and ex-post IR. Write $x(v,t)$ for an agent's allocation with report $v$ against $t$; thus $x(v,t)+x(t,v)\le1$. Let $X(t)=x(h,t)$. Monotonicity gives $x(v,t)\le X(t)$. The normalized single-parameter payment identity and budget imply $hX(t)-\int_0^h x(v,t)dv\le B$. (With no positive transfers, IR at type zero forces the normalization.) These are the only constraints needed for the upper bound.

Set $C(v,t)=vf(v)f(t)+\lambda(t)-m(v,t)$. Integrating the budget against $\lambda$ and the ceiling against $m$ and using (3) yields
$$ \iint vf(v)f(t)x(v,t)\,dvdt
 \le B\int\lambda(t)dt + \iint C(v,t)x(v,t)\,dvdt . \tag{4}$$
For $v>t$, (1) gives $C(v,t)-C(t,v)=\psi(v)-\psi(t)-m(v,t)\ge0$, while $C(t,v)=tf(t)f(v)+\lambda(v)\ge0$. The last integral in (4) is thus bounded above by $\int_{v>t}C(v,t)dvdt$, whether or not the original allocation sells the item on every profile.

The bound is attained by the proposed middle-ironed auction with the selected $a,b$. It allocates fully and favors the higher report on every weighted pair in the upper bound: more precisely, if the lower report has positive allocation in $M\times M$ or $H\times H$, then $C(v,t)=C(t,v)$, so full allocation alone suffices there. Outside those two regions the higher bidder obtains probability one. Wherever $m(v,t)>0$, the higher report is already on its upper plateau $x(v,t)=X(t)$. Finally, every middle or high opponent produces a top payment $B$, except for an immaterial endpoint tie at $h$. Against a middle opponent this payment is $(a+b)/2$ from the two jumps; against a high opponent $t<h$ it is
$$t(1/2+ab/(2t^2))-\int_b^t(1/2-ab/(2z^2))dz=(a+b)/2.$$
Against low opponents $\lambda=0$. All inequalities in (4) and the paired bound therefore agree in the integral. Multiplying by the common welfare normalization establishes optimality. For $B\ge h$ the efficient second-price mechanism is the no-active-ironing endpoint of the family and is feasible. No uniqueness of optimal rival mechanisms is asserted.
