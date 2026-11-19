# Exact minimum overlap for crossing geodesic tubes in the hyperbolic plane

Let $n\ge2$ distinct complete unoriented geodesics in the curvature $-1$ hyperbolic plane meet **pairwise at interior points** (so no parallel or ultraparallel pairs). Let $T_i$ be the closed tube of geodesic half-width $\delta>0$ about the $i$th line. Put $a=\sinh\delta$ and, for $0<\theta<\pi$, define
\[
 F_\delta(\theta)=4\int_{\theta/2}^{(\pi+\theta)/2}
 \left(\sqrt{1+a^2/\sin^2u}-1\right)\,du .
\]

**Theorem.** For every real $s>0$, the minimum of the sum of the $s$th powers of ordinary hyperbolic intersection areas is
\[
 \min\sum_{i\ne j}|T_i\cap T_j|^s
   = n\sum_{k=1}^{n-1}F_\delta(\pi k/n)^s. \tag{1}
\]
The sum counts ordered pairs. Equality holds precisely for the equally spaced pencil: the geodesics share a point and their unoriented directions there have successive gaps $\pi/n$. The minimizer is thus unique up to hyperbolic isometry and relabeling. The assumption of interior intersection of the central geodesics is essential; there is no analogous positive minimum for arbitrary mutually distant geodesics.

This is one precise version of the negative-curvature question raised by Steinerberger (2016, §2) after his Euclidean and spherical strip results. It is not a claim about every hyperbolic Kakeya problem or curves on a quotient surface.

### 1. Exact angular kernel

Use polar distance $l$ and direction $\phi$ centered at the crossing of two lines making angle $\theta$. The perpendicular distance $d$ to the line of angular direction zero satisfies $\sinh d=\sinh l\,|\sin\phi|$ (the right-triangle sine rule, also immediate in the hyperboloid model using its unit normal). The radial endpoint of the intersection therefore has hyperbolic sine $a/\max(|\sin\phi|,|\sin(\phi-\theta)|)$. Integrating ordinary area $\sinh l\,dl\,d\phi$ gives the radial contribution $\sqrt{1+a^2/\max(|\sin\phi|,|\sin(\phi-\theta)|)^2}-1$. The angular integrand has period $\pi$; on a period, the first sine has the larger absolute value on $[\theta/2,(\pi+\theta)/2]$, since the difference of the squares is $\sin(2\phi-\theta)\sin\theta$. Reflection $\phi\mapsto\theta-\phi$ interchanges the two pieces and makes their integrals equal. This proves the formula $F_\delta$. It is finite at every interior angle, positive, and symmetric about $\pi/2$.

We need strict convexity of the **power**, including $s<1$. Write $g(u)=\sqrt{1+a^2/\sin^2u}-1$, $t=-\log\sin u$, $w=(1+a^2 e^{2t})^{-1/2}$. Rationalizing $g$ gives $(\log g)_t=1+w$ and $(\log g)_{tt}=-w(1-w^2)$. Consequently
\[
 (\log g)''(u)=1+w+(1+w^3)\cot^2u>0.
\]
For two different angles and a strict convex combination, apply strict log convexity at each pair of points $v+\theta_1/2,v+\theta_2/2$ with $0<v<\pi/2$, integrate, then apply Hölder. This proves strict log convexity of $F_\delta$, hence strict convexity of every power $f(\theta)=F_\delta(\theta)^s$. Symmetry then gives strict decrease on $(0,\pi/2]$.

### 2. Reducing the angular energy to a pencil

The argument here works for any symmetric strictly convex angular cost on $(0,\pi)$, equivalently its restriction $f$ to acute angles is strictly convex and strictly decreasing (we only need these two properties of the restriction).

Choose one of the original lines as anchor. Move each of the other lines by the hyperbolic translation along the anchor taking its crossing to one fixed point $O$ on the anchor. Translation preserves the anchor and parallel-transports its tangent frame along itself, so the resulting pencil retains the angles of all pairs incident to the anchor. For two other lines, if their three crossings with each other and the anchor are not concurrent, the three lines bound a nondegenerate geodesic triangle with interior angles $A,B,C$. In particular, when the anchor is the side between the vertices of angles $A,B$, orient this side from the first vertex to the second. The other two lines, directed towards the third vertex on the same chosen side, then have directions $A$ and $\pi-B$ relative to this transported frame. Their angle after the collapse, before folding to the acute value, is $\pi-A-B=C+D$, where $D=\pi-A-B-C>0$ by the triangle angle defect. Hence the three original acute angles are $\alpha_i=\min(A_i,\pi-A_i)$; the three respective replacements of the pair opposite its anchor are
\[
 \beta_i=\min(A_i+D,\pi-A_i-D)=\min(A_i+D,A_j+A_k).
\]
They are positive, excluding coincident directions in the collapsed pencil. A concurrent triple is unchanged up to isometry.

We claim $\sum_i f(\beta_i)<\sum_i f(\alpha_i)$ for any nondegenerate triangle. Relabel so $A\le B\le C$, hence $\alpha_A=A,\alpha_B=B,\alpha_C\ge B$. Since $B+C>A$, $\beta_A>A$. Since $A+C>B$, $\beta_B>B$. If $\beta_C\ge\alpha_C$ we are done. Otherwise, $C+D>\alpha_C$, so $\beta_C=A+B$. Put $\ell=\alpha_C-A-B>0$. From $\alpha_C\le\pi-C$ and $\alpha_C\le C$ we have $\ell\le D$ and $\ell\le C-A-B$, hence $\beta_A\ge A+\ell$. Also $\ell<\alpha_C-A$ since $B>0$. Strict convexity applied at the two interior convex combinations of the endpoints $A,\alpha_C$ therefore gives
\[
 f(A+\ell)+f(\alpha_C-\ell)<f(A)+f(\alpha_C).
\]
Using decrease and $\beta_B>B$ proves the claim in this case too.

Average the total **unordered** pair energy of the collapsed pencil over all $n$ anchors. Each pair contributes its original value for its two incident anchors. For the other anchors, group terms by unordered triples. In each triple, summing the three changes is exactly the just-proved triangle comparison (zero for concurrent triples). The average total energy cannot increase, and decreases strictly if any triple is nonconcurrent. When $n\ge3$ an arrangement not entirely concurrent contains such a triple: take two lines and a third missing their intersection. Thus every nonpencil is strictly beaten by at least one pencil. For $n=2$ the arrangement is already a pencil.

### 3. The minimizing pencil

In a pencil, lay out unoriented directions cyclically at $x_1<\cdots<x_n<x_1+\pi$ and extend $x_{i+n}=x_i+\pi$. For each $1\le k<n$ the $n$ forward differences $x_{i+k}-x_i$ have average $k\pi/n$, since each elementary gap occurs $k$ times. Symmetry identifies the angular cost without folding. Strict-convex Jensen, summed over $k$, gives the right side of (1). Equality for $k=1$ requires all gaps to coincide; equispacing attains every equality. This proves the finite theorem.

### 4. Constants at Steinerberger's width

Write $E_s(n)$ for the minimum in (1) when $\delta=1/n$. Then
\[
 E_s(n)\sim
 \begin{cases}
 \displaystyle\frac{4^s}{\pi}\int_0^\pi\sin^{-s}u\,du\; n^{2-2s}, &0<s<1,\\
 \displaystyle(8/\pi)\log n,&s=1,\\
 \displaystyle 2\sum_{k\ge1}L_k^s\;n^{1-s},&s>1,
 \end{cases}\qquad
 L_k=4\int_{\pi k/2}^{\infty}(\sqrt{1+v^{-2}}-1)\,dv.
\]
For the proof, $a_n=\sinh(1/n)\sim1/n$. In the angular integral, $\sqrt{1+x}-1\le x/2$ at $x=a_n^2/\sin^2u$. Since $\int_{\theta/2}^{(\pi+\theta)/2}\csc^2u\,du=2/\sin\theta$, it follows that $F_{1/n}(\theta)\le4 a_n^2/\sin\theta$. For $\theta=\pi k/n$, $j=\min(k,n-k)$, the maximum of $x$ on the integration interval is $O(j^{-2})$, uniformly, by symmetry and $\sin(\pi j/(2n))\ge j/n$. Since $2/(1+\sqrt{1+x})=1+O(x)$, we have
\[
 F_{1/n}(\pi k/n)=4a_n^2\csc(\pi k/n)\,[1+O(j^{-2})]. \tag{2}
\]
For $0<s<1$, on each compact interior subinterval (2) gives the limiting Riemann integral; after scaling by $n^{2s-2}$ the omitted endpoint parts $j\le\epsilon n$ contribute at most $C_s n^{s-1}\sum_{j\le\epsilon n}j^{-s}\le C'_s\epsilon^{1-s}$. For $s=1$, the relative error in (2) contributes $O(1)$ to the energy, by $\sum j^{-3}<\infty$. The identity $\csc x=x^{-1}+O(x)$ on $(0,\pi/2]$ gives $\sum_{k=1}^{n-1}\csc(\pi k/n)=(2n/\pi)\log n+O(n)$, proving the middle line.

For fixed $k$, set $v=nu$ in the exact integral. The lower endpoint is $\pi k/2$, the upper one $n\pi/2+\pi k/2$. Pointwise $a_n/\sin(v/n)\to1/v$. For $n\ge2k$, $v/n\le3\pi/4$ and $\sin(v/n)\ge c v/n$ there, so the integrand extended by zero past the upper endpoint is dominated by $C/v^2$ for $v\ge\pi k/2$. Dominated convergence gives $n F_{1/n}(\pi k/n)\to L_k$. Moreover $nF_{1/n}(\pi k/n)\le C/k$ for $1\le k\le n/2$. Reflect by symmetry, counting the middle term at half weight when $n$ is even; dominated convergence in the summable series for $s>1$ gives the last line. The fixed-$k$ boundary profile is retained in this regime; simply replacing all hyperbolic tube areas by Euclidean strip areas gives a different constant.
