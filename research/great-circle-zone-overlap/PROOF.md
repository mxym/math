# From spherical-zone overlap to projective Riesz energy

For a line $[u]$ with unit representative in $\mathbb R^3$, its great-circle zone $Z_u$ on the unit sphere has geodesic half-width $1/n$. Thus $Z_u=\{x:|u\cdot x|\le h\}$, $h=\sin(1/n)$. Write $|\cdot|$ for ordinary surface area (sphere area $4\pi$) and $\sigma$ for the rotation-invariant **probability** measure on the space of unoriented lines $P=\mathbb RP^2$. Let $s>0$ be fixed. Compare
\[
 A_s(n)=\min_{P^n}\sum_{i\ne j}|Z_{u_i}\cap Z_{u_j}|^s,\qquad
 R_s(n)=\min_{P^n}\sum_{i\ne j}r_{ij}^{-s},\qquad
 r_{ij}=\sqrt{1-(u_i\cdot u_j)^2}.
\]
Both sums count **ordered** pairs. A repeated line has infinite bare interaction and finite geometric interaction. The actual overlap minimum exists by compactness and continuity (moving zone boundaries have area zero); the bare minimum exists by lower semicontinuity and a distinct finite-energy competitor. Allowing coincident lines in the geometric minimization costs no generality for the infimum if distinct lines are stipulated, by approximation.

**Theorem.** The ratio $Q_n=A_s(n)/[(8h^2)^s R_s(n)]$ tends to one. More precisely, for $s>1$ and all sufficiently large $n$,
\[
 1\le Q_n\le 1+O_s\!\left(\begin{cases}
 n^{2/s-2}&1<s<2,\\[1mm]
 (\log n)/n&s=2,\\
 1/n&s>2.
 \end{cases}\right)
\]
The normalized counting measures of geometric minimizers converge weakly to $\sigma$ on $P$, not necessarily to uniform measure for a choice of signed poles on the sphere. In particular the **leading constants** in Steinerberger's three orders for the true zone overlap are
\[
 A_s(n)\sim
 \begin{cases}
 8^s\displaystyle\int_0^1(1-z^2)^{-s/2}\,dz\; n^{2-2s}, &0<s<2,\\
 32\,n^{-2}\log n,&s=2,\\
 8^s C_{s,2}(2\pi)^{-s/2} n^{1-3s/2},&s>2 .
 \end{cases}
\]
Here $\log$ is natural; $C_{s,2}$ is the standard **ordered-pair** hypersingular Riesz constant on the area-one square, not a new evaluation of it. At $s=1$ this says $A_1(n)\to4\pi$; consequently the minimum of the normalized squared $L^2$ multiplicity tends to $2$, since the diagonal contributes $nh\to1$.

## 1. A comparison at shrinking width, including the diagonal

Set $J_h(u,v)=|Z_u\cap Z_v|/(8h^2)$ and write $c=|u\cdot v|$, $r=\sqrt{1-c^2}$. In the orthogonal plane with coordinates $(x,y)$ along $u$ and its orthogonal complement toward $v$, the band constraints read $|x|\le h$, $|cx+ry|\le h$. Both hemispheres together project to the **ordinary-area** density $2(1-x^2-y^2)^{-1/2}$ on the unit disk: each graph $\pm\sqrt{1-x^2-y^2}$ has that Jacobian without the 2. The assertion at $r=0$ follows directly from a single zone; alternatively choose any perpendicular coordinate. For $r>0$ the parallelogram before intersection with the disk has area $4h^2/r$, and its greatest squared radius is $2h^2/(1-c)=2(1+c)h^2/r^2\le 4h^2/r^2$ (maximize the squared norm at a vertex). Hence when $r\ge4h$,
\[
 1\le r J_h\le(1-4h^2/r^2)^{-1/2}\le1+C h^2/r^2. \tag{1}
\]
Uniformly also
\[
 c_0/(h+r)\le J_h\le C_0/(h+r).\tag{2}
\]
Indeed, the rectangle $|x|\le h/2$, $|y|\le h/[2(h+r)]$ is in both strips and inside the disk for $h\le1/2$. Its Euclidean area is $h^2/(h+r)$ and the density is at least $2$. For the upper bound use (1) when $r\ge4h$; otherwise a whole zone has area $4\pi h$, since $u\cdot x$ is uniform on $[-1,1]$ under normalized area. Thus the inequalities include nearly coincident and identical lines. The pointwise fixed-angle formula alone cannot justify passing a limit through a minimum indexed by $n$.

## 2. One-pole replacement

Minimize either ordered energy with pair kernel $J_h^s$ or $r^{-s}$. Fix a pole $i$ at an optimum. Its local energy $L_i$, the sum over the other $n-1$ sites counted once, is no larger than after replacing that pole by any competitor, since the global increment is twice the local increment. Remove projective caps $r(y,u_j)<b$ about all other poles, $b=(2n)^{-1/2}$. One such cap has probability $1-\sqrt{1-b^2}\le b^2$, because $|y\cdot u_j|$ is uniform on $[0,1]$. The remaining set has measure at least $1/2$. Integrate the replacement inequality there, using $J_h\le C/r$ from (2) for the soft kernel. The pushforward of $\sigma$ by $r$ has density $r/\sqrt{1-r^2}$, giving
\[
 L_i\le C_s n\int_b^1 \frac{r^{1-s}}{\sqrt{1-r^2}}\,dr\le C'_s H_s(n),\qquad
 H_s(n)=\begin{cases}
 n & 0<s<2,\\
 n\log n&s=2,\\
 n^{s/2}&s>2 .
 \end{cases}
\]
The bounds follow by splitting at $1/2$ (the square-root singularity at $1$ is integrable). One pair costs at least $c_s/(h+r_{ij})^s$ by (2), and the bare case is at least as simple. Thus $h+r_{ij}\ge c'_s H_s(n)^{-1/s}$. For $s>1$ we have $h=o(H_s(n)^{-1/s})$. In both minimizers, eventually every gap obeys $r_{ij}\ge c''_s H_s(n)^{-1/s}>4h$, excluding even potential repetitions in soft minimizers. Apply (1) first to the geometric optimum (lower bound the value by the bare optimum), then to the bare optimum as trial for the geometric problem. Since $(1+z)^s=1+O_s(z)$ for $0\le z\le1$, this proves the claimed two-sided ratio with relative remainder $O_s(h^2 H_s(n)^{2/s})$. In particular geometric optima are themselves asymptotically optimal for the bare energy in this range.

## 3. Integrable powers and equidistribution

For $0<s<2$ one can also argue directly, including $0<s\le1$. Put $K_M(r)=\min(r^{-s},M)$, with value $M$ at $r=0$. For each fixed $M>0$, $J_h^s\ge K_M$ everywhere for all sufficiently small $h$: use (1) for $r\ge4h$, and for $r<4h$ use (2) to get $J_h^s\ge(c_0/(5h))^s\ge M$. Let $\mu$ be a weak subsequential limit of minimizing empirical measures. After restoring and then subtracting the diagonal of $K_M$, continuity on $P^2$ gives
\[
 \liminf\frac{A_s(n)}{n^2(8h^2)^s}\ge\iint K_M\,d\mu\,d\mu.
\]
Here and below the liminf on this display is taken along the chosen subsequence. Let $M\to\infty$. Conversely independent Haar poles provide an expected sum $n(n-1)(8h^2)^s\int J_h(u,v)^s\,d\sigma(v)$, with any fixed $u$. By (1),(2), off the diagonal the integrand converges to $r^{-s}$ and is dominated by $C_s r^{-s}$, integrable since $s<2$. The limiting upper bound is
\[
 W_s=\int r(u,v)^{-s}\,d\sigma(v)=\int_0^1(1-z^2)^{-s/2}\,dz .
\]
By the projective equilibrium theorem of Chen, Hardin and Saff (Theorem 4.1, or strict positive definiteness of Euclidean Riesz energy on the projector image), $\sigma$ is the unique minimizing probability measure on $P$ for this energy. Its constant potential gives energy $W_s$. Thus both bounds agree, and every subsequential limit is $\sigma$. The same truncation and random trial directly for the bare kernel give $R_s(n)/n^2\to W_s$ (also a standard classical theorem), proving the ratio including the smallest powers.

## 4. The critical and hypersingular constants

The established projective embedding, rescaled here, is $[u]\mapsto uu^\top/\sqrt2$ into real symmetric matrices with the Frobenius norm. Squaring the distance gives $(2-2(u\cdot v)^2)/2=r^2$. Its differential sends a tangent vector $w\perp u$ to $(wu^\top+uw^\top)/\sqrt2$, of Frobenius length $|w|$. It therefore preserves the quotient spherical area locally. The image is a smooth compact 2-manifold of Hausdorff area $4\pi/2=2\pi$ in the normalization giving the unit square measure one. By Hardin and Saff's minimal Riesz energy theorem for rectifiable manifolds, for this very ordered-pair bare kernel
\[
 \frac{R_2(n)}{n^2\log n}\longrightarrow\frac{|B^2|}{2\pi}=\frac12,\qquad
 \frac{R_s(n)}{n^{1+s/2}}\longrightarrow\frac{C_{s,2}}{(2\pi)^{s/2}}\quad(s>2).
\]
Their asymptotically minimizing arrays converge to normalized Hausdorff area (which is the image of $\sigma$). Section 2 shows that geometric optima are such arrays. Multiplying by $(8h^2)^s\sim 8^s n^{-2s}$ proves the asserted constants. There is no claim of crystallization, a discrepancy rate, a closed numerical value for $C_{s,2}$, or equality of the two kinds of finite minimizers.

## 5. The separate finite-p scaling question

Let $X=\sum_i1_{Z_{u_i}}$, with probability area on the sphere. Its integral is exactly $nh$. For iid Haar poles and a fixed observation point, $X\sim\mathrm{Binomial}(n,h)$, so $\mathbb E\int X^p$ stays bounded for each fixed $p\ge1$ (use $\mathbb E e^{X}\le\exp(nh(e-1))$, so all positive moments are bounded). Fubini gives an arrangement with bounded $L^p$ norm; the lower bound $nh$ follows from Hölder. Thus the minimal norm is of order one for each fixed finite $p>2$. This elementary observation about the order, related to prior random-zone constructions, gives neither sharp leading $p$-dependent constants for $p>2$ nor a uniform $p=\infty$ bound. The pair energy with exponent $s$ is not the multiplicity moment with exponent $p$ except for the indicated off-diagonal identity at $(s,p)=(1,2)$.
