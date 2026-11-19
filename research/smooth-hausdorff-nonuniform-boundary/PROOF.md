# Nonuniform boundary sampling and the Hausdorff error of a smooth random inscribed polytope

Let $K\subset\mathbb R^d$, $d\ge2$, be a convex body with $C^3$ boundary and everywhere positive Gaussian curvature $\kappa$. Take the convex hull $K_n$ of $n$ iid boundary points with strictly positive Hölder probability density $h$ relative to surface area. Set $m=d-1$, let $g$ be the positive metric of the second fundamental form, write $dv_g=\sqrt\kappa\,dS$, and let $f=h/\sqrt\kappa$, $f_0=\min f$. Let $\omega_m$ be the Euclidean unit-ball volume, and set
$$
 \alpha_m=\frac1{m!}\left(\frac{\sqrt\pi\,\Gamma(1+m/2)}{\Gamma((m+1)/2)}\right)^{m-1}.
$$
For all sufficiently large $n$ define $w_n>m$ by
$$
 \Lambda_n(w_n)=1,\qquad
 \Lambda_n(w)=\alpha_m n\int f\,(wf/f_0)^{m-1}\exp(-wf/f_0)\,dv_g.
 \tag{1}
$$
Then, for the standard Gumbel law $G$,
$$
 n\omega_m f_0 (2\delta_H(K_n,K))^{m/2}-w_n\ \Rightarrow\ G .
 \tag{2}
$$
Equivalently, with $a_n=\tfrac12(w_n/(n\omega_m f_0))^{2/m}$ and $b_n=2a_n/(m w_n)$, one has $(\delta_H-a_n)/b_n\Rightarrow G$. The density may have any set of minimizers in the metric volume parametrization, including a flat plateau. For $f$ constant this recovers the optimal-density case of [Sonnleitner, Theorem 1](https://arxiv.org/html/2508.16442v1); the extension to other boundary densities is asked directly after that theorem. We assume positivity and Hölder regularity, not merely arbitrary integrability.

## The centering

We will establish the covering-radius version on a compact boundaryless $m$-manifold with $C^2$ charts and a $C^1$ positive metric. Let $R_n$ be the covering radius in that metric. The measure of every sufficiently small metric ball of radius $s$ is $\omega_m s^m(1+O(s))$, uniformly for its metric volume. This follows by freezing the metric at its center in one of finitely many charts extending beyond their compact working domains; the metric and volume elements vary by $O(s)$. All manifold constants may depend on the manifold, the density and the finite atlas.

Write $0<\beta\le1$ for a Hölder exponent of $f$. For $w\ge m$, integrating over a ball of radius $w^{-1/\beta}$ at any minimum and also using the uniform upper bound on $f$ gives constants $c,C>0$ with
$$
 c n w^{m-1-m/\beta}e^{-w}\ \le\ \Lambda_n(w)\ \le\ C n w^{m-1} e^{-w}.
 \tag{3}
$$
Thus (1) has exactly one solution above $m$ for large $n$ by strict monotonicity there, and $w_n=\log n+O(\log\log n)$. On normalizing its integrand to a probability measure at $w_n$, the mass of every set $f\ge f_0+\epsilon$ tends to zero by (3) and exponential suppression. Consequently $\Lambda_n(w_n+x)\to e^{-x}$ for fixed real $x$ by taking the ratio of integrands. Throughout, $w=w_n+x$ and $r=(w/(n\omega_m f_0))^{1/m}$.

## A uniform small-cell estimate from Janson's fixed-domain theorem

Use a homogeneous Poisson process of intensity $\lambda$ in Euclidean $m$-space. Consider a parallelepiped $P=b A[-1/2,1/2]^m$ with $A$ ranging over a fixed compact set of nonsingular matrices, and an empty open ball of radius $s$ **contained** in $P$. Translates of $P$ are allowed. Put $u=\lambda\omega_m s^m$, $\theta=\lambda |P|u^{m-1}e^{-u}$. Whenever $u\to\infty$, $s/b\to0$, and $\theta\to0$, its no-such-ball probability $p$ satisfies
$$
 -\log p=(\alpha_m+o(1))\theta .
 \tag{4}
$$
This is a uniform sequential assertion, not an application of weak convergence at a diverging centered threshold.

Take $t=\lceil\theta^{-1/m}\rceil$ and tile a translate of $tP$ by $t^m$ copies of $P$. If $p_*$ denotes its no-ball probability, then $p_*\le p^{t^m}$ by independence. An empty ball contained in $tP$ which is not wholly inside one tile has center within $s$ of a tile face. Use an $s/u$-net of these candidate centers **chosen among centers whose balls are contained in $tP$**. A maximal separated set has cardinality at most $C t^m |P|(s/b)(u/s)^m$: its disjoint half-mesh balls fit in thickened face strips of volume $O(t^m b^{m-1}s)$ (including points just outside $tP$). At a net center a ball of radius $s(1-1/u)$ would be empty, with probability at most $e^{-u+O(1)}$. The union bound is $O(t^m\theta\,s/b)=o(1)$. Hence
$$p^{t^m}=p_*+o(1).$$
The expected count $N=\lambda t^m|P|$ satisfies $Nu^{m-1}e^{-u}=t^m\theta\to1$ and $u=\log N+(m-1)\log\log N+o(1)$. For a *fixed* shape the homogeneous maximal-spacing theorem of [Janson, 1987, Theorem 1](https://doi.org/10.1214/aop/1176992269), applied after dilation to a domain of volume one, gives $p_*\to\exp(-\alpha_m)$. Its usual formulation is iid uniform with integer sample size. Poissonization follows by sandwiching the count between $N\pm N^{2/3}$ (rounded), with probability tending to one: the intensity threshold $u$ changes by $O(u N^{-1/3})=o(1)$ and both log centerings by $o(1)$. A strict versus nonstrict threshold makes no difference by squeezing and continuity of the limit.

For possibly varying $A$, pass along a subsequence $A\to A_*$. In the dilation by $1/(tb)$, for every fixed small $\epsilon>0$ the domain is between $(1-\epsilon)A_*[-1/2,1/2]^m$ and $(1+\epsilon)A_*[-1/2,1/2]^m$. Couple by a common homogeneous ambient Poisson process with the same ball radius and intensity in all domains: containment of an empty ball is monotone in the domain. The expected counts in the two fixed-shape comparison domains have ratios tending to $(1\pm\epsilon)^m$ relative to $N$. Their no-ball probabilities therefore tend to $\exp(-\alpha_m(1\pm\epsilon)^m)$. Let $\epsilon\downarrow0$ to obtain the same limit; every sequence has this subsequential comparison. Taking logarithms of $p^{t^m}$ and using $t^m\theta\to1$ proves (4).

## Independent cell comparison, with unweighted geodesic radius

Let the Poisson sample have intensity $n f\,dv_g$. Fix chart cubes with compact closures inside extended chart domains whose interiors cover the manifold, and assign overlaps in fixed chart order. Apart from the finitely many original chart faces this partitions the manifold into disjoint chart pieces; their boundaries lie in finitely many compact smooth face pieces. In each piece use grid cubes of side $b=(\log n)^{-B}$ whose closures lie in its interior. Choose $B>m/\beta+2$. The complement of their union lies in an $O(b)$-tube around the original chart faces and has volume $O(b)$. There are $O(b^{-m})$ cells. The $Cr$-collar of all grid faces has volume $O(r/b)$, since each cell has side comparable to $b$ in the metric and $r=o(b)$. These estimates persist under an additional thickening by $r/w$ with the same orders. Smooth charts and finitely many faces suffice; no generic transversality of different charts is needed.

Let $D$ be the complement together with this grid-face collar for a sufficiently large fixed $C$. An empty metric ball of radius $r$ centered in $D$ has probability $o(1)$ to occur anywhere in $D$. Indeed a maximal separated $r/w$-net of $D$ has size at most $C'(w/r)^m(b+r/b)$ by the volume bounds on its thickening. A possible empty ball requires a net-centered ball of radius $r(1-1/w)$ to be empty. Its sampling intensity is at least $w(1-O(1/w+r))=w-O(1)$ by $f\ge f_0$ and small-ball volume. The net bound is therefore
$$
 O\big(nw^{m-1}e^{-w}(b+r/b)\big)=o(1)
$$
by (3), whence $nw^{m-1}e^{-w}=O(w^{m/\beta})$.

Freeze the metric in each cell at its center $y_i$ and apply the linear map given by the positive square root of its coordinate metric matrix. In these coordinates each cell is a Euclidean parallelepiped $P_i$ as in (4); its metric volume element is $(1+O(b))$ times Lebesgue measure there. Its intensity is between the constants $\lambda_i^\pm=n f(y_i)(1\pm C_1b^\beta)$. Couple these homogeneous processes below and above the true one in each cell. For radii of order $r$, an intrinsic ball around a point in a cell is between the two Euclidean balls of radii $r(1\pm C_2b)$, in the extended chart. The metric is comparable on the surrounding $O(b)$ neighborhood: a path of length $O(r)$ cannot leave that neighborhood and the straight coordinate segment gives the reverse inclusion. Thus an empty Euclidean ball of radius $r(1+C_2 b)$ wholly contained in a cell gives an intrinsic empty ball of radius $r$; conversely an intrinsic empty ball of radius $r$ centered outside $D$ gives a wholly contained empty Euclidean ball of radius $r(1-C_2 b)$ in its cell. Open-ball threshold conventions can equally be handled by bracketing fixed $x$ by $x\pm\epsilon$.

All two-sided homogeneous cell parameters satisfy uniformly
$$
 u_i= w f(y_i)/f_0+o(1),\qquad
 \theta_i=(1+o(1))n|P_i| f(y_i)
        (w f(y_i)/f_0)^{m-1}e^{-wf(y_i)/f_0}.
$$
Indeed $w(b+b^\beta)\to0$, and $\max_i\theta_i=O(b^m w^{m/\beta})=o(1)$. The uniform estimate (4) applies. The exponent sum $\alpha_m\sum_i\theta_i=(1+o(1))\Lambda_n(w)+o(1)$: relative errors from replacing volume, density, and even the exponential by their central values tend uniformly to zero, and the omitted $O(b)$ region contributes at most $O(b nw^{m-1}e^{-w})=o(1)$. Independence of cell events and the negligible bad-center probability now sandwich the no-empty-ball probability between quantities tending to $\exp(-e^{-x})$.

This argument also applies with intensity $(n\pm n^{2/3})f$ at the **same** radius $r$: all $u_i$ change by $O(w n^{-1/3})=o(1)$ and all preceding bounds and limiting sums remain identical. Monotonicity in the number of points and concentration of the two Poisson counts around their means sandwich the iid $n$-point covering radius. We have proved
$$n\omega_m f_0 R_n^m-w_n\Rightarrow G.$$

## From the covering radius to the polytope

With $g$ the second fundamental form, [Sonnleitner, Theorem 2](https://arxiv.org/html/2508.16442v1) gives $|\delta_H(K_n,K)-R_n^2/2|\le C R_n^3$ when $R_n$ is sufficiently small. The proved limit gives $R_n=O_{\mathbb P}((\log n/n)^{1/m})$. Therefore $n|(2\delta_H)^{m/2}-R_n^m|=O_{\mathbb P}(n R_n^{m+1})=o_{\mathbb P}(1)$, valid also for $m=1$ by the relative $1+O(R_n)$ comparison. This proves (2); first-order expansion at $w_n\to\infty$ gives the affine normalization claimed above.
