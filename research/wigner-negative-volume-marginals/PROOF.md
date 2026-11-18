# A two-mode state with less Wigner negative volume than the sum of its marginals

**Claim.** There exists a two-mode state, diagonal in a finite product number basis and therefore separable, for which the Wigner negative volume satisfies
$$
N(W_{12})<N(W_1)+N(W_2).
$$
The target is the numerical suggestion for **general two-mode states** following Property 4 in [Cerf, Hertz and Van Herstraeten (2024), §4.2](https://doi.org/10.1007/s40509-024-00325-8). Their proved property for product states is unaffected. With their convention $\arg W=+\pi$ for $W<0$, Eqs. (29)–(33) give
$$
\operatorname{Im}\left(-\int W\log W\right)=\pi N(W),\qquad
N(W)=\int(-W)_+=\frac{\|W\|_1-1}{2}.
$$
Here $W_i$ is the reduced one-mode Wigner function on a full position–momentum plane. For products, $N(W_1W_2)=N(W_1)+N(W_2)+2N(W_1)N(W_2)$; for any state, marginalization gives $N(W_{12})\ge\max_iN(W_i)$. The example violates neither fact.

## 1. The state

Set $m=64$, $r=1/2$ and $a=r^m/m!$. Define the vacuum projector $V=|0\rangle\langle0|$ and the binomial mixture
$$
S=\sum_{j=0}^m 2^{-m}\binom mj|j\rangle\langle j|.
$$
Put $D=S-aV$, $X=V-S$ and take
$$
\rho_{12}=\frac{D\otimes D-4a^2X\otimes X}{(1-a)^2} .
$$
Both marginals equal $D/(1-a)$ because $\operatorname{Tr}X=0$ and $\operatorname{Tr}D=1-a$. Thus $\operatorname{Tr}\rho_{12}=1$. Each diagonal entry of its numerator on $\{0,\dots,m\}^2$ is at least $(2^{-m}-a)^2-4a^2>0$: indeed $a<2^{-m}/4$ and $|X_{jj}|\le1$. All other entries vanish. The state is a finite-energy mixture of product number states, and is nonproduct because $X\ne0$. Its matrix entries are rational.

Use the oscillator normalization with vacuum Wigner function $e^{-t}/\pi$, $t=x^2+p^2$. For number state $j$ the symbol is $e^{-t}(-1)^j L_j(2t)/\pi$. Consequently the symbol of $S$ is $e^{-t}A(t)/\pi$ with $A(t)=t^m/m!$. To check this, expand $L_j(z)=\sum_{k=0}^j\binom jk(-z)^k/k!$. The coefficient sum $\sum_{j=k}^m(-1)^j\binom mj\binom jk$ equals $(-1)^k\binom mk(1-1)^{m-k}$; only the top coefficient survives.

Integrating the angle in a single phase plane leaves area element $\pi\,dt$. Write $d\mu(t)=e^{-t}dt$ on $[0,\infty)$, so $\int A\,d\mu=1$. Let $t=x_1^2+p_1^2$, $u=x_2^2+p_2^2$, $A=A(t)$ and $B=A(u)$. The joint radial signed density relative to $\mu\otimes\mu$ is $G/(1-a)^2$, where
$$
G=(A-a)(B-a)-4a^2(1-A)(1-B).
$$
The one-mode radial density relative to $\mu$ is $(A-a)/(1-a)$; it is negative exactly on $t<r$. The Gaussian times polynomial Wigner functions also have finite complex entropies: for bounded $|z|$, $|z\log|z||$ is bounded by a constant times $\sqrt{|z|}$, an integrable envelope here.

## 2. Certifying the sign

Let $\Delta=N(W_{12})-N(W_1)-N(W_2)$. Integrating each marginal back against the joint measure gives
$$
(1-a)^2\Delta=\iint J\,d\mu(t)d\mu(u),\qquad
J=(-G)_++\big(\mathbf1_{t<r}+\mathbf1_{u<r}\big)G .
$$
Write $++$, $--$ and *mixed* for the signs of the two marginal densities, **not** the sign of $G$. The lines $t=r$ and $u=r$ are null sets. On $++$ we have $J=(-G)_+$; on mixed rectangles $J=G_+$; on $--$ we will have $G<0$ and hence $J=G$. The estimates below include the full unbounded domain.

**Both negative.** For $A,B<a$ one has $G\le a^2-4a^2(1-a)^2\le-2a^2$ since $a<1/16$. Also $\mu([0,r])\ge r/2$ because $r=1/2$ and $e^{-t}\ge1-t$. The integral over this rectangle is therefore at most $-a^2r^2/2$.

**Both positive.** Suppose $A,B\ge a$. If $1-A$ and $1-B$ have different signs then $G\ge0$. If $A,B\ge1$ then $(A-a)(B-a)\ge(A-1)(B-1)\ge4a^2(A-1)(B-1)$. Thus a positive value of $(-G)_+$ requires $A,B\le1$, where $(-G)_+\le4a^2$ and $(A-a)(B-a)<4a^2$. With $x=t/r$, $y=u/r$, the possible region in scaled variables satisfies $x,y>1$ and $(x^m-1)(y^m-1)<4$. Its area is at most $2I_m^2$, by bounding its indicator by $2/\sqrt{(x^m-1)(y^m-1)}$. Here
$$
I_m=\int_1^\infty\frac{dx}{\sqrt{x^m-1}}
\le\frac4m\int_1^\infty\frac{dz}{z\sqrt{z^2-1}}
=\frac{2\pi}{m}<\frac8m .
$$
Indeed put $x=z^{4/m}$ and use $z^{4/m-1}\le1$ and $z^4-1\ge z^2(z^2-1)$. Returning to $t,u$ contributes a Jacobian $r^2$. Dropping the factors $e^{-t-u}\le1$ only enlarges this nonnegative integral, which is at most $(512/m^2)a^2r^2=a^2r^2/8$.

**Mixed.** By symmetry take $A<a$, $B\ge a$. For $B\le1$, $G\le0$. For $B>1$, $G>0$ forces
$$
(a-A)(B-a)<4a^2(1-A)(B-1)\le4a^2(B-a).
$$
It follows that $a-A<4a^2$: the first coordinate belongs to a strip of width at most $r[1-(1-4a)^{1/m}]\le4ar$. Throughout that strip $G_+\le4a^2 B$. Integrate over all $u$ using $\int B\,d\mu=1$, and bound $e^{-t}\le1$ in the strip. The two mixed rectangles together give at most $32a^3r<a^2r^2/8$, since $a/r<1/256$.

Adding the contributions proves the explicit strict bound
$$
\boxed{\displaystyle \Delta<-\frac{a^2r^2}{4(1-a)^2}<0 .}
$$
No numerical integration, subtraction of floating-point approximations, or tail cutoff is used. For context and limitations see [SOURCES.md](SOURCES.md), and for an independent review of the sign estimates see [REVIEW.md](REVIEW.md).
