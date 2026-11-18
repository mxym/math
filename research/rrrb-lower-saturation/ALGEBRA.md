# Locating the physical root: two checks

Use the signed scalar maximizer $r(p)$, stationarity polynomial $K$ and diagonal test $D$ of [PROOF.md](PROOF.md). Put
$$
J(p)=65536p^4-86528p^3+39133p^2-5378p-139.
$$

## 1. Elimination, with the direction of implication explicit

The Sylvester determinant gives $\operatorname{Res}_r(K,D)=p^2J(p)$. Coefficients of the cubic $K$ in $r$ have degree at most three in $p$ and those of the quartic $D$ have degree at most four. The determinant has four rows of coefficients of $K$ and three of $D$, so degree at most 24. [verify.py](verify.py) verifies the determinant identity by exact interpolation at 25 distinct rational points. We use **only** that a common root forces this determinant to vanish, not that a vanishing determinant selects the physical maximizing branch.

For $p=(y/4)/(1+y)$ the polynomial $(1+y)^4J(p)$ has strictly negative coefficients. For $p=(1/4+y/3)/(1+y)$ it is
$$
(1684/81)y^4-(1303/27)y^3-(42515/144)y^2-(8713/24)y-2139/16.
$$
Descartes' rule and the opposite endpoint signs give precisely one root in $(1/4,1/3)$ and no root in $(0,1/4)$. Direct rational evaluation brackets it between $0.32053506$ and $0.32053508$.

The actual $D(p,r(p))$ is continuous. At $p=1/4,r=0$ it equals $-3/256$. At $p=1/3$ it equals $r^2(5-3r-9r^2)/3>0$ since $0<r<1/24$. Consequently it must change sign somewhere and can do so only at the single root of $J$ identified above. It is negative below that root and positive above it up to $1/3$.

## 2. Independent parametrization without an eliminant converse

Set $w=x-4r$. At stationarity,
$$
x=2w-w^3,\quad p=(1+2w-w^3)/4,\quad r=(w-w^3)/4,\quad C=(1-w^2)^3/4.
$$
The sign of $r$ and $|r|<|x|/8$ (or $r=x=0$) imply $|w|<1$. Then $|x|=2|w|-|w|^3<1$ gives $|w|<(\sqrt5-1)/2<5/8$. On this range $p(w)$ is strictly increasing. Direct substitution yields
$$
256D=(1+w)^2 Q(w),\qquad Q(w)=16w^4-28w^3-3w^2+22w-3.
$$
For $w=-v$, $0\le v\le5/8$, the positive terms $v(16v^3+28v^2)$ are at most $22v$, and $Q(w)<0$. For $0\le w\le1/3$, $Q'(w)\ge22-84/9-2>0$. At $p=1/3$, $1/6<w<1/3$ and $Q(1/6)>0$. This locates exactly one sign change in the *actual* feasibility expression throughout $0<p\le1/3$, independently of a resultant argument. [independent.py](independent.py) also checks $16J(p(w))=Q(w)B(w)$ with explicit rational polynomial $B$, gives separate Sturm counts, and encloses the physical root by bisection of $Q$.
