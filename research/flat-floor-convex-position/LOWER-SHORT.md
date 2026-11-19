# The triangle is the unique minimizer with a marked planar floor

Let $K$ be any compact planar convex body of positive area above a supporting line, and $F$ any specified nondegenerate segment of $K$ on that line. Write $Q_n(K,F)$ for the probability that $n$ independent uniform points of $K$ are all on the boundary of their convex hull with $F$. Almost surely this is equivalent to all the sampled points being vertices. For every integer $n\ge2$,
$$
 Q_n(K,F)\ \ge\ t_n=\frac{2^n}{n!(n+1)!}.
$$
Equality holds exactly for a triangle with $F$ its entire bottom side. In particular no restriction to the vertical strip over $F$ is needed. This proves the lower inequality in the planar flat-floor Conjecture 1.8 of Marckert–Morin, arXiv:2411.08456v2. Their Theorems 1.5 and 1.7 already establish the case $n=2$; the triangle value is classical (Bárány–Rote–Steiger–Zhang; also Marckert–Morin Theorem 3.3).

**A geometric lower bound.** Enlarging $F$ to the entire bottom side cannot increase $Q_n$: a sampled point in the hull of the other points and the smaller floor remains in the enlarged hull. First use the full bottom side, with ends $A,B$ in increasing horizontal order. Translate and rescale independently in the horizontal and vertical directions so that the bottom is at zero, the maximum height is one, and the area is one. The width $w(v)$ of the horizontal slice $I(v)$ at height $v$ is continuous and concave, positive on $(0,1)$, and $\int_0^1 w=1$. Indeed the left endpoint function is convex and the right endpoint concave; at each end compactness gives upper semicontinuity of width and concavity gives the matching lower limit. Write $w_0(v)=2(1-v)$ for the width of the reference triangle.

Fix the unique highest sampled point $P$ at height $v$, at fraction $s$ along $I(v)$ from left to right. Write $L,R$ for the left and right ends of that slice. The two triangles $ALP$ and $BPR$ lie in $K$ by convexity. Their interiors are disjoint. Their areas are $v s w(v)/2$ and $v(1-s)w(v)/2$. We retain configurations in which the remaining $m=n-1$ points fall in these triangles and, in each triangle, form a convex chain above its chord $AP$ or $BP$ with the chord endpoints (that is, all points are vertices together with those endpoints).

Those two events suffice. The accepted left chain bounds its local hull on the left of the chord $AP$. Since $A$ and $P$ are the unique bottom and top vertices there, the chain is the graph of a convex left endpoint function $x_{\rm L}(u)$ of height $0\le u\le v$. The other chain similarly gives a concave right endpoint $x_{\rm R}(u)$. An empty chain is simply its chord. For $0<u<v$, the left chain stays weakly left of the chord $AP$, the right weakly right of the chord $BP$, and these chords are in strict left-to-right order. Consequently $x_{\rm L}\le x_{\rm R}$ and the region between the functions is convex. Its two boundary chains retain all their vertices (there are almost surely no collinearities), and they meet at the common highest vertex. No abscissa restriction on the original body is used.

Conversely, for any triangle over its full bottom side, the part below height $v$ is precisely the union of $ALP$, $ABP$, $BPR$ up to their boundaries. No further sample can be in the interior of $ABP$ in a successful configuration, and each local chain must be convex. The retained event is therefore exact for every triangle.

Choose the label of $P$ in $n$ ways and integrate its position unconditionally; each retained configuration has exactly one such label because all remaining points are below it. The other points have probability equal to their respective triangle areas times uniform conditional point probabilities (the area normalization was one). With $t_0=1$ and the standard affine invariance of triangular chain probabilities, we obtain
$$
 Q_n(K,F)\ \ge\
 C_n\int_0^1 v^{n-1}w(v)^n\,dv,\qquad
 C_n=\frac n{2^{n-1}}\int_0^1\sum_{j=0}^{m}{m\choose j}
        s^j(1-s)^{m-j}t_jt_{m-j}\,ds>0.                         \tag{1}
$$
Here $dP=w(v)\,ds\,dv$. Equality in (1) for the reference triangle means $C_n\int_0^1 v^{n-1}w_0(v)^n\,dv=t_n$. It remains to compare the scalar integrals.

**A one-dimensional comparison.** For $J(w)=\int_0^1 v^{n-1}w(v)^n\,dv$, the supporting line to $x^n$ at $w_0(v)=2(1-v)$ gives
$$
 J(w)-J(w_0)\ \ge\ n2^{n-1}\int_0^1[v(1-v)]^{n-1}\bigl(w(v)-w_0(v)\bigr)\,dv. \tag{2}
$$
The weight $g(v)=[v(1-v)]^{n-1}$ is symmetric. Thus the last integral is unchanged if we replace $w$ by $\bar w(v)=(w(v)+w(1-v))/2$ and $w_0$ by its symmetrization, the constant one. Now $\bar w$ is symmetric and concave, hence nondecreasing on $[0,1/2]$ (each intermediate point lies between a point and its reflection, which have equal values). The weight $g$ is also nondecreasing there. With $X,Y$ independent uniform on this half-interval, $\mathbb E\bar w(X)=\int_0^1 w=1$, so the integral in (2) is $\frac12\mathbb E[(g(X)-g(Y))(\bar w(X)-\bar w(Y))]\ge0$. This proves $J(w)\ge J(w_0)$. For $n\ge2$, the strictly convex tangent inequality is strict wherever $w(v)\ne w_0(v)$ in $(0,1)$; equality of the integrals therefore forces $w=w_0$ by continuity.

**Equality in the geometric problem.** If the original full-floor body attains $t_n$ it must have affine width $w_0$. Its left endpoint is convex and, as the right endpoint minus this affine width, also concave. Both endpoints are therefore affine, and the top width zero forces a triangle. Every full-floor triangle attains $t_n$ as above.

Finally a proper marked subsegment in such a triangle increases the probability strictly. Affinely put the full bottom edge at $[0,1]$ and reflect if necessary so the marked right endpoint is $s<1$. Choose $s<x_1<\cdots<x_n<1$ and $y_i=\eta(x_i-s)^2$ with $\eta>0$ small enough that all these points lie in the interior of the triangle. Each is strictly exposed from below among the others and the marked ends by the tangent to this parabola: the tangent is strictly below zero on the marked segment. With the entire bottom side, on the other hand, the first $n-1$ points are strictly inside the triangle under the last one, since $(x-s)^2/x$ strictly increases for $x>s$. The strict conditions persist on small open neighborhoods of all samples, an event of positive probability. This proves the equality statement also for general markings.
