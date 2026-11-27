# Explicit stability of near-equators in dimensions six and seven

A six-dimensional kissing code with 40 designated points within **Euclidean chord distance $1/100$** of the signed vertices of a normalized $D_5$ equator has at most **72** points. No designated pair has to be exactly antipodal, and none of the designated points has to be in the hyperplane. The remaining points are arbitrary real unit vectors. Four certificates follow; all distances are on the **unit** sphere after a single isometric placement of the comparison directions.

| Ambient dimension | Reference equator | Distinct designated points | Allowed chord error, each point | Bound on whole code |
|---:|---|---:|---:|---:|
| 6 | $A_5$ | 30 | $1/160$ | 72 |
| 6 | $D_5$ | 40 | $1/100$ | 72 |
| 7 | $D_6$ | 60 | $1/360$ | 126 |
| 7 | $E_6$ | 72 | $1/260$ | 126 |

In particular, at the first excess sizes 73 and 127 these neighborhoods are forbidden; this is a perturbation result, not a claim ruling out every configuration. The actual points may be off their nominal directions independently and need not have any symmetries or exact root inner products. A Gram-matrix variant below dispenses with an explicit fit.

The argument uses a **criterion for arbitrary reference directions**, which need not be roots. A cap matching lemma, not a worst-case bound on every pair, is important for the stated tolerances. For a non-root example, a 44-point half-cube/coordinate section in seven dimensions has whole-code size at most **74**, as proved below (no sharpness claim). The one-sided proof for [exact root equators](KissingEquatorialProjectivization.md), the [punctured ADE criterion](KissingADEProjectivizationClassification.md), and the [five-dimensional near-orthoplex theorem](KissingFiveNearlyOrthogonalFrame.md) are different results. [Novgorodtsev, §3](https://www.preprints.org/manuscript/202610.0335) already uses covering constants for exact cross sections; the covering inequality alone is not the novelty here.

## A cap matching and a weighted certificate

Throughout, $d=6$ or $7$, with $P=36$ or $63$ respectively. Work on the unit sphere. The even kernel
$$
       f(t)=t^4-t^2/4,\qquad c=\frac{3}{d(d+2)}-\frac1{4d}=\frac3{4P}
$$
has nonnegative spherical-harmonic coefficients in every positive degree. Indeed $t^4$ has a positive degree-four coefficient, its degree-two part is $6/(d+4)$ times that of $t^2$, and the displayed $c$ is the constant term. The spherical addition theorem therefore gives, for arbitrary real weights, $\sum_{ij}w_iw_j f(x_i\cdot x_j)\ge c(\sum_iw_i)^2$.

**Cap matching lemma.** Among the points of any kissing code with height at least $h\ge\sqrt{2/11}$ above a fixed hyperplane, the pairs with scalar product strictly less than $-1/2$ form a matching. Otherwise take two such neighbors of $x$, with average $m$. Then $\|m\|^2\le3/4$ by their mutual kissing constraint, and $m$ has height at least $h$. Thus
$$
        x\cdot m\ge h^2-\sqrt{(1-h^2)(3/4-h^2)}\ge-1/2,
$$
contradicting the two strict bad products. If $h^2>3/4$ the two neighbors are impossible already from $\|m\|$. The last inequality is exactly $11h^2\ge2$ after squaring. No antipodality or frame is assumed.

Now take $p$ unit reference axes $u_i$ spanning a hyperplane, represented by arbitrary choices of sign, and suppose $2p$ distinct designated code points are within chord distance $z$ of the $\pm u_i$, one per sign. Put
$$
 \gamma=\min_{\|w\|=1,\,w\in \operatorname{span}(u_i)}\max_i |w\cdot u_i|,
 \quad \Lambda=\lambda_{\max}\!\left(\sum_i u_i u_i^T\right),
 \quad E=\sum_{i\ne j} f(u_i\cdot u_j).
$$
Let $a\ge1/2$ bound $|y\cdot u_i|$ for each nondesignated point $y$. For the small errors used here one may take
$$
 a=\frac12+\frac{13}{15}z-\frac{z^2}{4}.
$$
Indeed the side angle is at least $\pi/3-2\arcsin(z/2)$, whose cosine is $1/2-z^2/4+(\sqrt3/2)z\sqrt{1-z^2/4}$, and $\sqrt3/2<13/15$. This triangle bound applies to both signs. Alternatively $a=1/2+z$ follows directly from Cauchy–Schwarz.

Write $U=(a/\gamma)^2$ and suppose $U\le9/11$. Each remaining point has squared horizontal length at most $U$, since its normalized horizontal direction has some $|u_i|$-projection at least $\gamma$. Thus all have nonzero height, of absolute size at least $\sqrt{1-U}$. On one side all residual products are at least $1-2U$. Set
$$
 b=\max(1/2,2U-1),\quad T=\Lambda U(a^2-1/4),\quad q=P+1-p>0 .
$$
For one residual point $y$, $\sum_i f(u_i\cdot y)\le T$ by the frame operator bound. Distinct residual pairs outside the negative matching contribute at most zero; an ordered bad pair contributes at most $f(b)$. Among $q$ residual points there are at most $q$ such ordered pairs.

If a code has $2P+1$ or more points, some side therefore has at least $q$ residuals. Apply the kernel inequality to the $p$ reference directions with weight $t>0$, and to any $q$ such residuals with weight one. A necessary condition is
$$
 c(pt+q)^2\le t^2(3p/4+E)+2tqT+q(3/4+f(b)).
$$
This is the promised **root-free** certificate: failure of this scalar inequality at any positive $t$ proves the bound $2P$. Reference directions need not themselves be code points. If $A=3p/4+E-cp^2>0$ and $B=q(cp-T)>0$, testing the maximizing $t=B/A$ amounts to requiring
$$
            cq^2-3q/4-q f(b)+ B^2/A>0.
$$

For the four root references, $E=0$, $\Lambda=p/(d-1)$ by irreducibility and unit normalization, and $\gamma^{-2}=2R^2$ where $R^2$ is the squared circumradius of the usual root polar in squared-length-two normalization. In table order the values of $R^2$ are $3/2,5/4,3/2,4/3$; see the [root-polar computation](KissingADEProjectivizationClassification.md). The [short rational replay](verify-kissing-perturbed-equators.py) checks the $U$ and $B$ conditions and verifies the last strict margins are respectively greater than $0.0109,0.0042,0.0092,0.0037$. This proves the table.

**Without a fitted equator.** Let $C$ be the $(d-1)\times p$ matrix of unit comparison columns with $CC^T=\Lambda I$, and $W$ the $d\times p$ matrix of the observed positive representatives. Suppose $\|W^TW-C^TC\|_{\rm op}\le e<\Lambda$, and every observed negative representative has distance at most $\eta$ to the negative of its positive mate. It is enough that $\sqrt e+e/\Lambda+\eta$ is at most the chord allowance above. To prove this, $\Pi=C^TC/\Lambda$ is an orthogonal projection, with $\|W(I-\Pi)\|_{\rm op}\le\sqrt e$. Let $F=WC^T/\Lambda$. Then $\|F^TF-I\|_{\rm op}\le e/\Lambda$ and an isometric factor $Q$ in its polar decomposition satisfies $\|F-Q\|_{\rm op}\le e/\Lambda$. Since $FC=W\Pi$, each observed positive column is within $\sqrt e+e/\Lambda$ of the corresponding $QC$ column. Add $\eta$ for the negative sign. This uses only approximate Gram data; an actual codimension-one span for the observed points is not assumed.

## A 44-point non-root example

In a six-dimensional equator take the twelve signed coordinate units and all 32 vectors $(\pm1,\ldots,\pm1)/\sqrt6$ with an even number of minus signs. These are 22 antipodal lines. Their maximum absolute off-axis scalar product is $1/\sqrt6<1/2$. Their **exact covering constant** is $\gamma=2/3$.

To check the latter, scale a direction so the largest absolute scalar product against the 22 axes is at most one. Sort the absolute coordinates as $1\ge a_1\ge\cdots\ge a_6\ge0$. The worst sign parity for coverage gives the inequality $a_1+\cdots+a_5-a_6\le\sqrt6$ (the other parity has the stronger all-plus inequality). The sorted simplex has vertices $v_j$ consisting of $j$ ones and $6-j$ zeroes, for $0\le j\le6$. The left side at these vertices is $0,1,2,3,4,5,4$. Clip the simplex by the displayed inequality: its vertices are $v_0,v_1,v_2$ and crossings on edges from one of these three to $v_3,\ldots,v_6$. The squared norm at a crossing on $[v_i,v_j]$ is $i+(j-i)((\sqrt6-i)/(L_j-i))^2$, with $L_j=j$ for $j\le5$ and $L_6=4$. Each is at most $9/4$, attained on $[v_0,v_6]$ in the odd sign chamber. Convexity proves the covering value; the replay checks all twelve quadratic comparisons exactly.

If a seven-dimensional kissing code contains this exact section, each outsider has absolute height at least $\sqrt7/4$. On a given side the normalized horizontal directions of two nonpolar outsiders have scalar product at most $1/9$: for heights $s,t\ge\sqrt7/4$, the upper bound $(1/2-st)/\sqrt{(1-s^2)(1-t^2)}$ is decreasing in each variable (its partial derivative in $s$ has the sign of $s/2-t$). A pole is alone on its side. Finally in six dimensions the cubic $g(x)=(x-1/9)(x+2/3)^2$ has positive Gegenbauer coefficients in degrees 1, 2, 3 and constant term $25/162$. It is nonpositive on $[-1,1/9]$ and $g(1)/(25/162)=16$. If equality held, the degree-one moment would give zero vector sum and all distinct products would be $-2/3$ or $1/9$. In any row the number of $-2/3$ entries would be $24/7$, not an integer. Thus each side has at most 15 points and the whole configuration has at most $44+2\cdot15=74$. This is a restricted upper bound, not a new construction of 74 points.
