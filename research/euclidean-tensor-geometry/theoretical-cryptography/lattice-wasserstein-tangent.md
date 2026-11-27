# Tangent quadratic transport of lattice laws and Gaussian Voronoi width

For a full-rank Euclidean lattice \(L\subset\mathbb R^n\), let \(W_2\) be the usual transportation distance on probability measures supported on \(L\), with direct cost \(\|x-y\|^2\). Define the different ground cost
\[
d_L(v)=\min\left\{\sum_{j=1}^\ell\|v_j\|^2:\ \ell\ge0,\ v_j\in L\setminus\{0\},\ \sum_j v_j=v\right\}.
\tag{1}
\]
For \(v=0\) the empty choice gives zero. This is the path metric obtained by allowing a squared-cost displacement to use a sequence of lattice steps. We also write \(d_L(x,y)=d_L(y-x)\).

For a zero-mass signed measure \(\eta\) of finite first moment, write \(\|\eta\|_{\mathrm{KR},d}\) for the \(1\)-transport cost from its negative part to its positive part under a metric \(d\), with the common mass not normalized to one. This equals the supremum of the signed integral against \(1\)-Lipschitz functions by transport duality.

**Theorem.**

1. Suppose \(\mu_0(x)>0\) for every \(x\in L\), \(\mu_0\) has finite second moment, and \(h\mapsto\mu_h\) is differentiable at zero in the weighted variation norm \(\sum_x(1+\|x\|^2)|\mu(x)|\), with derivative \(\dot\mu_0\). Then
\[
\lim_{h\to0}\frac{W_2(\mu_h,\mu_0)^2}{|h|}
=\|\dot\mu_0\|_{\mathrm{KR},d_L}.
\tag{2}
\]
In particular changing masses on fixed lattice sites has square-root metric order when the derivative is nonzero.
2. Let \(\mu_s\) have probabilities proportional to \(e^{-\|x\|^2/(2s^2)}\) on \(L\). Let \(V_L\) denote the Voronoi cell of \(0\), and \(h_{V_L}(z)=\sup_{c\in V_L}\langle c,z\rangle\) its support function. For a standard Gaussian \(Z\) on \(\mathbb R^n\), as \(s\to\infty\),
\[
\lim_{h\to0}\frac{W_2(\mu_{s+h},\mu_s)^2}{|h|}
=2\,\mathbb E h_{V_L}(Z)+O_L(s^{-1}).
\tag{3}
\]
The limit in \(h\) is taken first for each fixed \(s\). In contrast the two continuous isotropic Gaussians have quadratic transport cost \(n h^2\).
3. The continuous displacement relaxation of (1) is the norm
\(\Gamma_L(v)=2 h_{V_L}(v)\). For every \(v\in L\),
\[
\Gamma_L(v)\le d_L(v)\le\Gamma_L(v)+C_L
\tag{4}
\]
with a lattice-dependent constant independent of \(v\). Equality holds for all \(v\in L\) for every lattice of rank at most four. It can fail in rank five: an example below has \(d_L(v)=11/2\) and \(\Gamma_L(v)=5\). A family in increasing rank has ratios tending to \(3/2\).

All statements concern abstract Euclidean lattice laws. No modulus or cryptographic algorithm enters the model.

## 1. The first-order transport formula

The minimum in (1) exists: any fixed finite cost bound allows only finitely many nonzero step vectors (each length is bounded) and finitely many steps (each squared length is at least \(\lambda_1(L)^2\)). The resulting translation-invariant cost is a metric. For nonzero \(v\),
\[
\lambda_1(L)\|v\|\le d_L(v)\le C'_L\|v\|,\qquad d_L(v)\le\|v\|^2 .
\]
The lower bound follows by summing step lengths and the upper linear bound by using a fixed lattice basis. The last inequality uses the one-step choice.

For the lower bound in (2), replace the direct squared cost by the smaller metric \(d_L\). Kantorovich–Rubinstein duality gives
\[
W_2(\mu_h,\mu_0)^2\ge \|\mu_h-\mu_0\|_{\mathrm{KR},d_L}.
\]
The norm on the right is continuous in first-moment weighted variation since a \(1\)-Lipschitz test can be set to zero at the origin, so its value at \(x\) is bounded by \(C'_L\|x\|\) in absolute value. This yields the claimed lower limit as \(h\to0\).

For the reverse direction, let \(\eta\) be any finite-support zero-mass approximation to \(\dot\mu_0\) in second-moment weighted variation, obtained by restricting to an increasing finite set and balancing with a term at \(0\). Let \(h>0\) for now. Choose a finite transport of \(\eta^-\) to \(\eta^+\) of optimal \(d_L\) cost and expand each transported pair into a shortest squared-cost path as in (1). Every step of every path contributes the indicated mass multiplied by \(h\), giving a finite system of transfers along individual edges. The incoming minus outgoing mass at a vertex \(x\) is \(h\eta(x)\). The path vertices have positive \(\mu_0\)-mass, so when \(h\) is small enough the total outgoing mass at each vertex is at most \(\mu_0(x)\). Leave the untransferred mass on the diagonal. This is a direct quadratic-cost coupling of \(\mu_0\) and \(\mu_0+h\eta\), with cost at most \(h\|\eta\|_{\mathrm{KR},d_L}\). The relay is a simultaneous description of the couplings, not a change of the transport problem to another dynamic metric.

For two probabilities \(\sigma,\tau\) on \(L\), couple their common masses on the diagonal and the remaining masses arbitrarily. The inequality \(\|x-y\|^2\le2(\|x\|^2+\|y\|^2)\) gives
\[
W_2(\sigma,\tau)^2\le 2\sum_x\|x\|^2|\sigma(x)-\tau(x)|.
\]
With \(\sigma=\mu_h,\tau=\mu_0+h\eta\), this supplies an error at most \(2h\|\dot\mu_0-\eta\|_{\mathrm{weighted}}+o(h)\). Apply the triangle inequality for \(W_2\), divide by \(\sqrt h\), and then approximate \(\dot\mu_0\) arbitrarily closely with \(\eta\). The negative side uses \(-\eta\) and the same norm. This proves (2). In the exact linear, finite-perturbation case, the relay coupling and the lower bound in fact give equality for all sufficiently small \(|h|\). Positivity on the possible relay sites matters: for a probability supported on \(\{0,2\}\), moving mass \(h>0\) from \(0\) to \(2\) costs exactly \(4h\), although \(d_{\mathbb Z}(2)=2\) using the vacant site \(1\).

## 2. The continuous relaxation and its arithmetic gap

The inequalities for the Voronoi cell are \(\langle c,w\rangle\le\|w\|^2/2\) for all \(w\in L\). Only finitely many nonzero \(w\) are needed: include the signed basis vectors to enclose a bounded region first, after which Cauchy–Schwarz makes sufficiently long vectors redundant. Let \(S\subset L\) be a finite symmetric set of normals giving all the inequalities and containing a basis. Linear programming duality in \(\mathbb R^n\) gives
\[
\Gamma_L(v)=
\min_{\lambda_w\ge0,\ \sum_{w\in S}\lambda_w w=v}
     \sum_{w\in S}\lambda_w\|w\|^2
=\max_{c\in V_L}2\langle c,v\rangle.
\tag{5}
\]
As \(V_L\) is centrally symmetric and full-dimensional, this is a norm. The lower inequality in (4) follows by applying any feasible \(2c\) to the steps in (1). For the upper bound, round an optimal coefficient vector in (5) down coordinatewise. The residual vector belongs to \(L\) and the fixed bounded set \(\{\sum_{w\in S}\theta_w w:0\le\theta_w\le1\}\). Correct it with a path in (1), at cost at most the maximum \(d_L\) of the finitely many possible residuals. This proves (4), including the stable identity \(d_L(kv)/k\to\Gamma_L(v)\).

There is an exact saturation criterion at each Voronoi vertex \(c\). Let \(S_c=\{w\in L\setminus\{0\}:\|w\|^2=2\langle c,w\rangle\}\), the other nearest points to \(c\) besides \(0\). If \(v\) belongs to the nonnegative cone of \(S_c\), then \(c\) attains the maximum in (5), by each active inequality. In that cone,
\[
d_L(v)=\Gamma_L(v)
\quad\Longleftrightarrow\quad
v\ \text{is a nonnegative integer sum of vectors in }S_c .
\tag{6}
\]
Indeed, equality forces every step of a minimizing path to saturate the inequality at \(c\), and the converse is direct. The cones obtained this way cover \(\mathbb R^n\) by LP dual optima: a Voronoi vertex can maximize any linear functional, and its normal cone is generated by its active inequalities.

In ranks at most four, first take a metric for which each full Delaunay cell is a simplex. The classical low-dimensional Delaunay-volume result implies that its vertices form an affine basis of \(L\). Thus every \(S_c\) at a Voronoi vertex is an integral basis, and its cone is saturated, giving equality in (4). For clarity this also covers degenerate metrics by approximation. In fixed lattice coordinates, simplicial metrics are dense: for each affinely independent \(0,w_1,\ldots,w_n\) and an extra lattice point \(w=\sum_i a_iw_i\) distinct from them, the tie equation after eliminating the center is the linear condition \(\|w\|_Q^2=\sum_i a_i\|w_i\|_Q^2\) on the Gram matrix \(Q\). This condition is not identically true, since \(aa^{\mathsf T}=\operatorname{diag}(a)\) implies \(a=0\) or a coordinate unit vector. Avoid the countably many proper hyperplanes. A general cell can be translated so that one vertex is \(0\). For each fixed lattice vector, \(d_{L,Q}\) is continuous under changing \(Q\): nearby positive-definite metrics have comparable squared lengths, so costs of every path are multiplied by factors \(1+o(1)\) uniformly, and taking minima preserves the comparison. The norm \(\Gamma_{L,Q}\) is likewise continuous by the same comparison in the real relaxation, allowing all lattice step vectors in (5), which does not change its value. Taking a simplicial sequence to an arbitrary metric proves the rank bound.

For a gap take \(L=\mathbb Z^5+\frac12\mathbf1\mathbb Z\), equipped with the Euclidean inner product represented by \(Q=I+\mathbf1\mathbf1^{\mathsf T}\). Define the linear functional \(\ell(z)=2\sum_i z_i\). For \(z\in\mathbb Z^5\),
\[
\|z\|_Q^2-\ell(z)=\sum_i z_i(z_i-1)+S(S-1)\ge0,\qquad S=\sum_i z_i,
\]
with equality exactly at \(0,e_1,\ldots,e_5\). For half-coset \(z_i=k_i+1/2\), put \(K=\sum k_i\), so \(S=K+5/2\). Its gap is at least
\[
|K|-5/4+(K+5/2)(K+3/2)\ \ge\ 1/2,
\]
using \(\sum k_i^2\ge|K|\); the minimum is reached at \(K=-1,-2\), and on either side the quadratic increases. Thus the functional \(\ell\) is a feasible dual bound \(2\langle c,\cdot\rangle_Q\), and on \(v=\frac12\mathbf1\) equality of the relaxed cost with \(\ell(v)=5\) follows by using real coefficients \(1/2\) on the \(e_i\)'s. Every lattice path to \(v\) needs at least one half-coset step, so costs at least \(5+1/2\). Take \(v-e_1\) followed by \(e_1\), whose squared costs are \(7/2\) and \(2\), attaining \(11/2\).

The same model in dimension \(n\), with \(Q=I+\lambda\mathbf1\mathbf1^{\mathsf T}\) and \(\ell(z)=(1+\lambda)\sum z_i\), gives a larger relative obstruction. Write \(R=\sum z_i\) for a half-coset step. Its gap is at least
\[
|R-n/2|-n/4+\lambda R(R-1),
\qquad R\in n/2+\mathbb Z .
\]
For \(\lambda=n^{-1/2}\) and sufficiently large \(n\), the minimum is attained at an \(R\) nearest to \((1+\lambda)/(2\lambda)\) in this grid, within \([-n/2,n/2]\). On this interval the lower bound is \(n/4-R+\lambda R(R-1)\); for \(R\ge n/2\) the other branch is increasing. The minimum gap is \(n/4-O(\sqrt n)>0\). It is attained by taking \(n/2-R\) of the coordinates to be \(-1/2\) and the rest \(+1/2\), so adding one coordinate vector for each negative coordinate completes a minimizing path to \(v=\frac12\mathbf1\). The relaxed cost is \((1+\lambda)n/2\). The ratio between the true and relaxed costs therefore tends to \(3/2\), without asserting a universal upper bound of that value.

## 3. The Gaussian width calculation

The scale family in the theorem is differentiable in second-moment weighted variation at each fixed \(s>0\): Gaussian decay dominates the differentiated polynomial factors locally uniformly in \(s\). Its derivative is
\[
s\,\partial_s\mu_s(x)
 = \mu_s(x)\left(\|x/s\|^2-\mathbb E_{\mu_s}\|X/s\|^2\right).
\tag{7}
\]
Let \(\eta_s\) put these signed masses at \(x/s\), and let \(d_{L,s}(x/s,y/s)=d_L(x-y)/s\). By linear scaling of mass and cost, 
\[
\|\partial_s\mu_s\|_{\mathrm{KR},d_L}
=\|\eta_s\|_{\mathrm{KR},d_{L,s}} .
\]
By (4) the last differs by at most \(C_L/s\) times the positive mass of \(\eta_s\) from \(\|\eta_s\|_{\mathrm{KR},\Gamma_L}\). That mass is bounded independently of large \(s\), as follows from the same Riemann-sum estimate used next.

Let \(\varphi_n(z)\) be the standard Gaussian density and \(\eta(dz)=(\|z\|^2-n)\varphi_n(z)\,dz\). One has
\(\|\eta_s-\eta\|_{\mathrm{KR},\Gamma_L}=O_L(s^{-1})\). To verify this with the changing supports, tile using a bounded fundamental parallelepiped of \(L/s\) around each \(x/s\), and put the signed integral over each cell at its lattice site. This changes every normalized \(\Gamma_L\)-Lipschitz test integral against \(\eta\) by \(O_L(s^{-1})\), since all moved distances are \(O_L(s^{-1})\) and \(\eta\) has finite variation. For \(f=\varphi_n\) and \(f=\|\cdot\|^2\varphi_n\), replacing the cell integrals by the cell volume times \(f(x/s)\) has first-moment weighted variation error \(O_L(s^{-1})\). Indeed the mean-value theorem bounds the error by the cell diameter times the cell volume times \(C_L(1+\|x/s\|)^k e^{-c\|x/s\|^2}\); these envelopes summed with the cell volumes and first-moment weights are bounded uniformly for \(s\ge1\) (compare to similar Gaussian envelopes on the full cells). It follows that the normalizing factor equals its continuous value up to relative error \(O_L(s^{-1})\), and the second moment in (7) is \(n+O_L(s^{-1})\). Inserting these into (7) gives the stated KR approximation.

It remains to compute the continuous signed cost under the possibly non-Euclidean norm \(\Gamma_L\). Both signs of \(\eta\) have uniform independent angle, with negative mass at radii \(r<\sqrt n\) and positive mass at \(r>\sqrt n\). Couple them with the same angle \(\theta\) and any coupling of the corresponding radial masses. On a ray, \(\Gamma_L(r_+\theta-r_-\theta)=(r_+-r_-)\Gamma_L(\theta)\). Its cost is exactly \(\int\Gamma_L(z)\,\eta(dz)\), and this is also a dual lower bound since \(\Gamma_L(\cdot)\) is \(1\)-Lipschitz for its own metric. Homogeneity and the Gaussian radial moment identity \(\mathbb E R^3=(n+1)\mathbb E R\) give
\[
\|\eta\|_{\mathrm{KR},\Gamma_L}
=\mathbb E[(\|Z\|^2-n)\Gamma_L(Z)]
=\mathbb E\Gamma_L(Z).
\]
This proves (3) by (2). For instance on \(\mathbb Z^n\), \(2h_{V_L}(z)=\|z\|_1\), so (3) tends to \(n\sqrt{2/\pi}\) rather than zero.

## Prior work and scope

[Kantorovich distance on a finite metric space, by Montrucchio and Pistone](https://arxiv.org/abs/1905.07547) discusses the signed-measure Arens–Eells norm and transport duality used here. [Peyré, *Generalized Wasserstein Distances*](https://www.gpeyre.com/ot4ml/myst/_build/html/generalized_wasserstein/), notes exact local quadratic transport when the atom locations move and weights stay fixed; this differs from the fixed-support, moving-weight tangent above. [Santos–Schürmann–Vallentin, *Lattice Delone Simplices with Super-Exponential Volume*](https://arxiv.org/abs/math/0507119), discusses Voronoi's classical low-rank unimodularity and examples of higher-rank nonunimodular Delaunay simplices. The contribution here is the link from local transport to the squared-step metric, its explicit integrality defect, and the large-width Gaussian support-function formula, not the classical cell geometry itself.

The result pertains to the ordinary static \(W_2\) distance, not to a separately defined graph-flow transport metric. The accompanying verification concerns generated lattices and probability masses, not the behavior of any scheme.

Replay with `node verify-lattice-wasserstein-tangent.js`. The last run passed 1,040,941 elementary exact checks (including the finite relay comparisons and scalar arithmetic inequalities for the gap family) and 16 numerical checks of the line's width derivative.
