# The exact profile on the upper half of the density range

Use the notation of [the threshold proof](THRESHOLD.md). Write $M(p)$ for the supremum of the labelled RRRB density. For $p\in[p_*,1]$ we already have $M(p)=f(p)=p^3(1-p)$. The remaining part of $[1/2,1]$ has the following scalar formula.

**For $1/2\le p<p_*$.** Put $x=4p-1$, $a=(1-x^2)/4$ and $C(r)=a+xr-4r^2$. Let $r$ be the rightmost zero in $(0,x/8)$ of
$$
ax+(x^2-8a)r-12xr^2+16r^3=0.
$$
Then
$$
M(p)=f(p)+C(r)^2/8-r^4.
$$
The equal-part kernel (2) with $\lambda=-r$ and $q=C(r)/4$ attains the maximum. Only existence of such a maximizer is asserted; uniqueness of the block construction is not needed.

**Proof.** A positive excess exists by the threshold proof. As $a\le0$ and $x>0$, positive excess in (1) requires $\lambda=-r<0$ and $C(r)>0$. Optimizing over $q\ge0$ then sets $q=C(r)/4$, with upper envelope $E=C(r)^2/8-r^4$. Where $C\le0$ the envelope is instead $-r^4$, so those points cannot maximize. Any positive maximum is interior, and its stationarity equation $C(r)(x-8r)=16r^3$ implies $0<r<x/8$.

On this interval $D=4E'=ax+(x^2-8a)r-12xr^2+16r^3$ has $D''=-24x+96r<0$. We have $D(0)=ax\le0$ and $D(x/8)=-16(x/8)^3<0$. The polynomial $D$ is positive somewhere in $(0,x/8)$: the positive maximum of $E$ must be reached after a point with $C=0$ and $E\le0$ (the point is $r=0$ at $p=1/2$). Thus its rightmost root in this interval is the only positive-excess maximum.

It remains to meet the graphon constraints. Since $x\ge1$, $C\le a+x^2/16=(4-3x^2)/16\le1/16$, so $2\sqrt q\le1/4$. Also $r<x/8<5/32$. Every entry of the proposed kernel differs from $p$ by at most $13/32$; $1/2\le p<p_*<9/16$ places all of them strictly in $(0,1)$. The upper bound is therefore attained.

**Closed form at $p=1/2$.** Here $x=1$, $a=0$ and $C=r-4r^2$. The derivative is $E'=r(1-12r+16r^2)/4$, with the interior maximizing root $r=(3-\sqrt5)/8$. Substitution gives $q=(\sqrt5-2)/16$ and
$$
M(1/2)=\frac{21+5\sqrt5}{512}>\frac1{16}.
$$
The source's undirected count divided by $n^4$ is *half* this value. The general upper bound and the feasibility check, not just the explicit construction, are needed to prove exactness.
