# The asymmetric four-layer optimum for [3,1,3]

Let $p$ denote the limiting packing density of the permutation $3214765$, of layered type $[3,1,3]$. Hästö's 2002 Theorem 1.3 already implies the existence of an optimal partition with four positive layers; we optimize the resulting known polynomial exactly. In particular the optimal four-layer masses are asymmetric and unique up to reversal. This addresses the unresolved symmetry observation immediately before Proposition 4.4 of that paper, **within its four-layer optimization**. We do not classify arbitrary finite optimal permutations or all permutons. Qualitative boundedness also follows from Kabela–Král’–Noel–Pierron (2022), Theorems 4–5, so the overbroad older bounded-type assertion for general $[a,1,b]$ is not needed.

**Exact value.** Define $T(y)=\sum_{i=0}^{10}t_i y^i$ by the following coefficients in **ascending** order:
```
-432, 2565671328, 20668776552, 4575974416, -439508172703,
-1682183144550, -2635934939569, -1771652618180,
-506074249089, -40641373350, 3363968313.
```
Let $r$ be the unique root of $T(r^2)=0$ in $(0,1/7]$, and let $z\in(0,1/\sqrt3)$ be the unique solution of
\[
 r(3+r^2)(1-3z^2)=2z^3(1+3r^2). \tag{1}
\]
Define
\[
 V=(1-z^2)(r+z)(1+rz),\quad
 h=\big[r(1-r^2)^2/V\big]^{1/3},
\quad (a,b,c,d)=\frac{(1+r,h(1-z),h(1+z),1-r)}{2(1+h)}.
\]
Then $p=140[a^3d^3(b+c)+a^3bc^3+b^3cd^3]$. For orientation the layer masses approximate $(0.4277082,0.0663472,0.0785873,0.4273573)$; the density is approximately $0.12451626$.

**Reduction and nonsymmetry.** Denote the expression in brackets in the formula for $p$ by $F$. This is Hästö’s four-layer polynomial (Theorem 4.3); the factor $140=7!/(3!3!)$ is the multinomial sampling multiplicity. A maximizer exists, and must use four positive coordinates: fewer than three give zero, and splitting the middle layer of any positive three-layer partition adds copies without losing any. Reverse the partition so that $a\ge d$. Use the above parameters $r=(a-d)/(a+d), z=(c-b)/(c+b),h=(c+b)/(a+d)>0$. Write $P=(1-r^2)^3$ and $H=(1-z^2)[(1+3r^2)(1+z^2)+2r(3+r^2)z]$. Direct expansion gives
\[
 64F=\frac{h[P+h^3H]}{(1+h)^7}. \tag{2}
\]
If $r=0$ then $H=1-z^4$, forcing $z=0$. However, with $h>0$ held fixed, substituting $r=z^2$ and $z>0$ small increases the numerator factor $P+h^3H$ by $6h^3 z^3+O_h(z^4)$, contradicting maximality. Thus $r>0$. In (2), reversing the sign of $z$ strictly improves a negative $z$, and the derivative at zero is positive. Thus $z>0$. Differentiating in $z$ now gives precisely (1). On $(0,1/\sqrt3)$ the right-hand ratio $2z^3/(1-3z^2)$ increases strictly from zero to infinity, so any $r>0$ determines $z$ uniquely.

We also have the a priori restriction $r\le1/7$. The endpoint bounds $a,d\le3/7$ follow on scaling all the other masses: for the first endpoint the polynomial takes the form $a^3(1-a)^4A+(1-a)^7B$ with $A>0,B\ge0$, decreasing for $a>3/7$; the last endpoint is the reverse case. Hästö's Lemma 4.1 gives $a\ge3b,d\ge3c$. Consequently $a+d\ge3/4$, and $1+r=2a/(a+d)\le8/7$.

**Elimination.** The global four-layer maximizer is interior in $r,z,h$ relative to the original positive partition; even if an auxiliary numerical bound is attained, its original first derivatives vanish. Differentiating (2) in $r$ gives $h^3=U/V$, with $U=r(1-r^2)^2$. In fact $P_r=-6r(1-r^2)^2$ and $H_r=6(1-z^2)(r+z)(1+rz)$. Differentiating in $h$ gives $(1-6h)P+(4-3h)h^3H=0$. Put
\[
 A=r[(1+3r^2)(1+z^2)+2r(3+r^2)z],\qquad B=(1-r^2)(r+z)(1+rz).
\]
Then $h^3H/P=A/B$, so $h=(B+4A)/(6B+3A)$. In particular the optimizer satisfies the system $D=E=0$, where
\[
 D=r(3+r^2)(1-3z^2)-2z^3(1+3r^2),\qquad
 E=U(6B+3A)^3-V(B+4A)^3 .
\]
All denominators used are strictly positive. The resultant in $z$ is
\[
 \operatorname{Res}_z(D,E)=12r^4(r^2-1)^{22}T(r^2). \tag{3}
\]
The exact integer verification [verify3.py](verify3.py) computes the $13\times13$ Sylvester determinants by fraction-free elimination at 82 distinct integer values of $r$. Degrees in $z$ are at most 3 and 10, respectively, and degrees in $r$ at most 3 and 17. The determinant has $r$-degree at most $10\cdot3+3\cdot17=81$. Since the right side has degree only 68, these evaluations certify the identity. The common-root condition implies vanishing of the resultant; we do not use the converse.

On $0\le y\le1/49$, the estimate
\[
 T'(y)\ge t_1+\sum_{i=2}^{10}\min(0,it_i)49^{1-i}>2500000000
\]
and $T(0)<0<T(1/49)$ are checked by rational arithmetic. Hence $r$ is uniquely determined; (1) then determines $z$, and $h=(U/V)^{1/3}$ is unique. Existence of a four-layer maximizer from the cited theorem guarantees that this unique necessary tuple attains the maximum; no extraneous algebraic solution is declared feasible. Reversal gives the other ordering. For the original symmetry suggestion, the short $r=z^2$ variation alone suffices without (3).
