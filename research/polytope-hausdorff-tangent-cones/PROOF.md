# The Hausdorff limit for sampling a polytope, inside or on its boundary

Fix a full-dimensional bounded convex polytope $K\subset\mathbb R^d$, $d\ge2$. Let $K_n$ be the convex hull of $n$ iid points uniformly sampled either inside $K$ or on its boundary, with respect to volume or surface area respectively. Write $s=d$ or $s=d-1$ in those cases, and $a=\operatorname{vol}_d(K)$ or $a=\mathcal H^{d-1}(\partial K)$ accordingly.

For each vertex $v$ put $C_v=\operatorname{cone}(K-v)$. In the volume case let $\mu_v$ be Lebesgue measure on $C_v$ divided by $a$; in the surface case let it be $\mathcal H^{d-1}$ on $\partial C_v$ divided by $a$. Let $\Pi_v$ be **independent** Poisson processes of these intensities and let
$$
Z_v=\operatorname{dist}(0,\overline{\operatorname{conv}}\Pi_v).
$$
Then the vector of $n^{1/s}\operatorname{dist}(v,K_n)$ converges in distribution to $(Z_v)_v$. In particular, for $r\ge0$,
$$
\lim_{n\to\infty}\mathbb P\{n^{1/s}\delta_H(K,K_n)\le r\}
=\prod_{v}\mathbb P\{Z_v\le r\}.
$$
The limit has no atoms and is nondegenerate; every positive moment of the normalized Hausdorff distance converges to the corresponding finite positive moment. The vertex factors admit the deterministic finite sum of integrals (1) below. No simplicity of $K$ is needed. The results for polygons are prior results; this answers the higher-dimensional polytopal question in Sonnleitner's introduction, not the adjacent smooth-body/density question.

## A finite determining neighborhood in a Poisson cone

Write $C=C_v$, $\mu=\mu_v$, $\Pi=\Pi_v$. The cone is full-dimensional, polyhedral and pointed. Some unit linear functional is uniformly positive on $C\cap S^{d-1}$. The nearest Poisson point to the origin has positive finite norm almost surely: the measures of bounded balls are finite, those of shrinking balls tend to zero, and $\mu(C)=\infty$. Applying the uniformly positive functional shows that $D=\operatorname{dist}(0,\overline{\operatorname{conv}}\Pi)>0$ almost surely. Write $z$ for the nearest point and $u=z/D$. By metric projection, $u\cdot x\ge D$ on the entire closed hull.

Almost surely $u$ lies in the interior of the dual cone. Indeed, for each of the finitely many unit extreme rays $e$, and each positive integer $m$, there are points of $\Pi$ of norm greater than $m$ within $1/m$ of the half-line $\mathbb R_+ e$. These sets have infinite intensity: in the volume case translate a small ball in the interior of $C$ along the ray, keeping it in the tube; in the surface case use a relative ball on any facet containing the ray. The balls can be disjoint. This also works on a one-dimensional facet. Thus any unit $w$ with $w\cdot e\le0$ has $\inf_{x\in\Pi} w\cdot x\le0$. Applying this simultaneously to the rays gives
$$
b:=\min_{y\in C\cap S^{d-1}}u\cdot y>0.
$$

The set of contact points $A=\{x\in\Pi:u\cdot x=D\}$ is finite and nonempty: the cap $u\cdot x\le D+1$ is bounded by coercivity, and the supporting infimum is $D$. The gap $u\cdot x-D$ is bounded below by a strictly positive constant on the other Poisson points. For finite convex combinations converging to $z$, the weighted sum of these gaps tends to zero. Hence the total weight of the noncontact points vanishes, as does their weighted sum of norms by $|x|\le(u\cdot x)/b$. Consequently $z\in\operatorname{conv}A$.

In particular, almost surely all sufficiently large balls of radius $R$ contain $A$ and satisfy $Rb>D$. For such a ball the nearest point to the convex hull of $\Pi\cap B(0,R)$ is exactly $z$; **no addition of any points of $C$ outside that ball can change it**, because every such point has scalar product with $u$ greater than $D$. Equivalently the finite configuration passes the following observable test: its hull is nonempty, its nearest point $z_R$ has positive norm, and $R\min_{y\in C\cap S^{d-1}}(z_R/|z_R|)\cdot y>|z_R|$. This test implies the same protection for any finite sample. It takes account of remote points even in obtuse cones and with boundary sampling.

## Joint transfer and moments

For each fixed $R$, the physical balls $B(v,Rn^{-1/s})$ are disjoint for all large $n$. In a small neighborhood of a vertex the polytope coincides with its translated tangent cone; in that neighborhood their boundaries coincide as well. The mass of each ball is exactly $\lambda_v/n$, with $\lambda_v=\mu_v(B(0,R))$. After the change of scale the vector of occupancy counts is multinomial with these cell probabilities and one residual cell. It converges in total variation to independent Poisson counts of means $\lambda_v$: the mass function converges pointwise and the limit sums to one. Given the counts, the local positions are independent draws from the normalized restrictions of the same $\mu_v$, exactly as in the Poisson experiment. Therefore the *full local configurations jointly* can be coupled identically with probability tending to one at each fixed $R$. Every scaled sample point belongs to the corresponding $C_v$, even if it came from another facet or another vertex neighborhood. When all finite determining tests pass the complete vectors of distances agree under this coupling. First taking $n\to\infty$, then $R\to\infty$, proves the claimed vector limit (indeed convergence in total variation). The distance to a convex set is convex and $K_n\subset K$, so the Hausdorff distance is precisely the maximum of the vertex distances.

For each $v$, the sampling mass within distance $t$ of $v$ is at least $c_v t^s$ for $0\le t\le\operatorname{diam}K$, by its exact small-radius value and monotonicity at larger radii (decrease the constant there). If there is a sampled point in this ball then $\operatorname{dist}(v,K_n)\le t$. The union bound now gives $\mathbb P(n^{1/s}\delta_H>r)\le\sum_v \exp(-c_vr^s)$ for $r\ge0$, also beyond the maximal possible error. This implies convergence of every positive moment. Each $Z_v$ has positive probability to be below any given $r>0$ (a near point suffices) and positive probability to exceed it (fix an interior dual unit normal and require its finite cap at level $2r$ to be empty).

## Formula for one vertex

For $1\le j\le d$ and a tuple $x=(x_1,\dots,x_j)$ in the support of $\mu$, consider only affinely independent tuples. Let $z_x$ be the orthogonal projection of the origin onto their affine span, $D_x=|z_x|$, $u_x=z_x/D_x$ when $D_x>0$. Call a tuple admissible if $D_x>0$, $z_x$ belongs to the relative interior of their simplex, and $u_x$ is in the interior of the dual cone. For unit $u$ there let $\kappa(u)=\mu\{y:u\cdot y<1\}$. For any Borel $J\subset(0,\infty)$,
$$
\mathbb P(D\in J)=\sum_{j=1}^{d}\frac1{j!}
 \int {\bf1}\{x\ {\rm admissible},\ D_x\in J\}
 \exp\{-\kappa(u_x)D_x^s\}\,\mu^{\otimes j}(dx). \tag{1}
$$
Thus the distribution can also be evaluated without simulating the Poisson hull. In the surface model the integrations use the ordinary facet area measures of the polyhedral cone, with no lower-dimensional edge mass except where a facet itself is a ray.

To prove (1), choose from $A$ a minimal subset whose convex hull contains $z$. This gives an affinely independent tuple, in a hyperplane of dimension $d-1$, with $z$ in its relative interior. Since $z$ is perpendicular to its affine directions, $z=z_x$. Given any admissible tuple, its positive-offset hyperplane $\{y:u_x\cdot y=D_x\}$ has $\mu$-measure zero, even when $\mu$ is supported on facet planes: all those planes pass through the origin and cannot coincide with this one. The multivariate Poisson Mecke formula then shows that almost surely no admissible tuple from $\Pi$ has any remaining point on its hyperplane (apply first to bounded tuple windows and exhaust). Therefore the minimal subset is unique, up to order, and gives all the contacts. Conversely an admissible tuple is exactly this unique unordered subset if the open cap below its hyperplane contains no other point; on that event the metric projection is $z_x$ by the supporting inequality. Mecke's formula counts such tuples with the independent Poisson void probability in (1), using homogeneity of degree $s$. This argument accounts for the possibility of fewer than $d$ contacts.

There are no positive atoms: for each $r>0$, $\{D_x=r\}$ has zero $\mu^{\otimes j}$-measure on admissible tuples, since simultaneous scaling multiplies $D_x$ by the scale. For example decompose the product cone measure into directions and common radius in $\mathbb R^{dj}$; homogeneity gives radial density proportional to $\rho^{sj-1}d\rho$. Together with positivity and the two strict tail events this proves the stated distributional properties.
