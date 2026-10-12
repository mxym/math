# Random-determinant rigidity, sharp symmetric cone bounds, and spectral nonattainment

**mxym — AI-assisted research manuscript. Entry 005, version 3, 7 October 2026.**

This is a continuation, not a replacement, of [version 2](../v2/paper.md) and its [spectral supplement](../v2/ASYMPTOTIC_SPECTRAL_REDUCTION.md). It closes the explicitly reserved nonpolytopal equality case, proves a dimensionwise qualitative stability statement, and gives a sharp upper bound under central symmetry. An additional theorem rules out a finite maximizer for the spectral parameter itself. No first-discovery, peer-review, or proof-assistant claim is made.

## 1. Statements and conventions

For a full-dimensional convex body $K\subset\mathbb R^d$, $d\ge1$, retain

$$R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!},$$

where $h_{\Pi K}(u)$ is the $(d-1)$-volume of the orthogonal projection onto $u^\perp$ for a unit vector $u$. An interval has $R=2$. Write $\mathcal P K$ for a pyramid over $K$. Version 2 defines the continuous positive affine invariant

$$a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1.$$

The join is $A*B=\operatorname{conv}\{(x,0,0):x\in A;\ (0,y,1):y\in B\}$; Cartesian products use independent coordinate spaces. Superscript $*k$ means a join of $k$ copies.

For polytopes, if $u_i$ is the facet area times the outward unit normal and $b_i$ is the facet area times the support number, the equivalent definition is

$$a(K)=\frac{\sum_{|I|=d+1}|\det((u_i,b_i):i\in I)|}
 {d|K|\sum_{|J|=d}|\det(u_j:j\in J)|}.$$

The following conclusions have complete written proofs below.

**General rigidity.** For every full-dimensional convex body, with no smoothness or polytope assumption,

$$\boxed{a(K)=\frac1{d+1}\quad\Longleftrightarrow\quad K\text{ is a simplex}.}$$

**Affine stability.** For every fixed $d$ and $\varepsilon>0$, there is a $\delta(d,\varepsilon)>0$ such that

$$a(K)\le\frac1{d+1}+\delta(d,\varepsilon)$$

implies, for every maximum-volume inscribed simplex $S$ with centroid $z$,

$$\boxed{S\subseteq K\subseteq z+(1+\varepsilon)(S-z).}$$

This is a uniform qualitative modulus in each dimension, not an explicit power law or an algorithm for computing $\delta$.

**Sharp symmetric upper bound.** If $K$ is centrally symmetric, then

$$\boxed{a(K)\le\frac12.}$$

The constant is attained in every dimension by parallelotopes. Every centrally symmetric planar body has $a=1/2$, and so does every product of centrally symmetric bodies of dimensions one and two. No classification of all upper-bound equality cases in dimensions at least three is claimed.

**Spectral nonattainment.** Put

$$Q(K)=\frac{a(K)R(K)}{g(d)},\qquad \lambda(K)=Q(K)^{1/(d+1)}.$$

For every positive-dimensional convex body $K$, every integer $k\ge1$ satisfying $k\lambda(K)^2\ge4a(K)^2(d+1)$ obeys

$$\boxed{\lambda\bigl(K^{*k}\times K^{*k}\bigr)>\lambda(K).}$$

Here $*$ is join. A Cartesian square suffices, with an explicit sufficient threshold for the number of join factors. Hence no finite-dimensional body attains the spectral supremum in any class closed under products and joins. This strengthens nonattainment for the different functional $R^{1/d}$ in v2; it does not identify either supremum.

The rigidity proof comes from a statement about arbitrary centered probability laws, not just surface area measures. We give that statement first.

## 2. A random-determinant theorem with complete equality cases

Let $\nu$ be a Borel probability measure on $\mathbb R^d$ with

$$\int\|x\|\,d\nu(x)<\infty,\qquad \int x\,d\nu(x)=0,$$

and suppose its support spans $\mathbb R^d$. Let $X_1,X_2,\ldots$ be independent with law $\nu$, and define

$$A(\nu)=\mathbb E|\det(X_1,\ldots,X_d)|,$$

$$B(\nu)=\mathbb E\left|\det\begin{pmatrix}X_1&\cdots&X_{d+1}\\1&\cdots&1\end{pmatrix}\right|.$$

These are $d!$ times the expected volumes of the simplex anchored at the mean and of the unanchored random simplex, respectively. The hypotheses imply $0<A<\infty$ and $B<\infty$: independence and the determinant bound give integrability, while neighborhoods of $d$ independent support points give positivity of $A$. A noncentered law is covered after subtracting its mean.

### Theorem 2.1. Sharp comparison and rigidity for arbitrary laws

$$\boxed{A(\nu)\le B(\nu)<(d+1)A(\nu).}$$

Equality in the lower bound holds if and only if the support of $\nu$ consists of exactly $d+1$ affinely independent points. Their probabilities are positive, and the centering condition puts zero in the interior of their simplex. The constant $d+1$ in the strict upper bound is the supremum over the stated class, but is not attained.

### Proof of the inequalities

Write $w(x)=(x,1)$. For a fixed ordered $d$-tuple $\mathbf x=(x_1,\ldots,x_d)$ define

$$F_{\mathbf x}(y)=\det(w(x_1),\ldots,w(x_d),w(y)),\qquad D_{\mathbf x}=\det(x_1,\ldots,x_d).$$

Centering and linearity in the last column give

$$\int F_{\mathbf x}(y)\,d\nu(y)=D_{\mathbf x}.$$

Consequently

$$G(\mathbf x):=\int|F_{\mathbf x}(y)|\,d\nu(y)-|D_{\mathbf x}|\ge0,\qquad
B-A=\int G\,d\nu^{\otimes d}. \tag{2.1}$$

This includes singular horizontal tuples; none is discarded. Expansion in the last row of the lifted determinant gives $B\le(d+1)A$.

For strictness of this upper bound, choose independent support points $x_1,\ldots,x_d$. At the $(d+1)$-tuple $(x_1,x_1,x_2,\ldots,x_d)$ the lifted determinant is zero, but the sum of the absolute horizontal cofactors is $2|\det(x_1,\ldots,x_d)|>0$. By continuity the triangle-inequality gap is positive on a product of neighborhoods of these points. Every such neighborhood has positive $\nu$-measure, so its integrated gap is positive. This argument also covers $d=1$.

### Proof of lower-bound rigidity

On every compact set of $d$-tuples, $|F_{\mathbf x}(y)|$ is bounded by a constant times $1+\|y\|$. Thus $G$ is continuous, by dominated convergence. If $B=A$, equation (2.1), nonnegativity and continuity imply

$$G(\mathbf x)=0\quad\hbox{for every }\mathbf x\in(\operatorname{supp}\nu)^d. \tag{2.2}$$

In particular, for every such tuple, $F_{\mathbf x}$ cannot take both a positive and a negative value on the support. Indeed, continuity would then give positive measure to both signs, making the triangle inequality strict.

Zero is in the interior of the convex hull of a finite subset of the support. Here is a useful proof that does not assume compact support. For each unit $u$ there is a support point $x$ with $\langle u,x\rangle<0$; otherwise centering would force $\langle u,X\rangle=0$ almost surely, contrary to full span. The corresponding open hemispheres cover the unit sphere. A finite subcover provides finitely many support points whose convex hull contains zero in its interior, by separation. Choose a minimal positive dependence among at most $d+1$ of them:

$$\sum_{i=1}^k p_i v_i=0,\qquad p_i>0,\qquad k\le d+1.$$

Existence of at most $d+1$ terms follows by the usual elementary elimination proof of Caratheodory's theorem: perturb a nonnegative affine dependence until a coefficient vanishes, and repeat. Minimality of the positive dependence implies that the horizontal rank is $k-1$. Otherwise a second independent null vector allows another such elimination. Since $\sum_i p_i>0$, the lifted vectors $w(v_i)$ are independent.

The lifted support spans $\mathbb R^{d+1}$. To see this, an affine functional vanishing on the support has zero constant term by centering, and then zero linear part by full span. If $k\le d$, extend the $k$ lifted vectors to a lifted basis selected from the support, and remove one vector outside the chosen $k$. The remaining $d$-tuple has horizontal determinant zero but admits a nonzero lifted extension from the support. Its integral of $|F|$ is positive, so $G>0$, contradicting (2.2). Therefore $k=d+1$.

Let $\Delta=\operatorname{conv}(v_1,\ldots,v_{d+1})$. For the $d$-tuple obtained by omitting $v_i$, the affine functional $F$ vanishes on the opposite facet, and its value at zero is nonzero. The sign condition following (2.2) places the whole support in the closed halfspace containing zero. Intersecting these $d+1$ halfspaces gives

$$\operatorname{supp}\nu\subseteq\Delta. \tag{2.3}$$

Suppose a support point $z$ is not a vertex. Write $w(z)=\sum_i\alpha_i w(v_i)$ in barycentric coordinates. By (2.3), the coefficients are nonnegative and sum to one, and at least two, say $\alpha_p,\alpha_q$, are positive. Form the $d$-tuple consisting of $z$ and the $d-1$ original vertices other than $v_p,v_q$. Its lifted columns are independent. The two numbers $F(v_p)$ and $F(v_q)$ are nonzero, since adding either missing vertex completes a lifted basis. They satisfy

$$\alpha_p F(v_p)+\alpha_q F(v_q)=F(z)=0.$$

They therefore have opposite signs, contradicting (2.2). The support consists precisely of the $d+1$ vertices.

Conversely, suppose the centered law is supported on the vertices of a simplex. A $d$-tuple with a repeated vertex has $F=0$. For a tuple of distinct vertices, $F$ is zero at the selected vertices and can be nonzero at just the one omitted vertex. Thus it has only one sign on the support, giving $G=0$ for every tuple and hence $B=A$.

### Sharpness of the upper constant

Let $\nu_0$ be any centered, spanning simplex-vertex law, and for $0<t<1$ set

$$\nu_t=(1-t)\delta_0+t\nu_0.$$

An anchored determinant is nonzero only if all $d$ samples come from $\nu_0$. An unanchored determinant has at most one zero sample. Thus

$$A(\nu_t)=t^d A(\nu_0),$$

$$B(\nu_t)=(d+1)(1-t)t^d A(\nu_0)+t^{d+1}B(\nu_0),$$

and therefore

$$\boxed{\frac{B(\nu_t)}{A(\nu_t)}=d+1-dt\longrightarrow d+1.}$$

This finishes the theorem. $\square$

## 3. The exact defect and finite strictness witnesses

For a real number $r$ put $r_+=\max(r,0)$, and for the fixed tuple in Section 2 define

$$p(\mathbf x)=\int (F_{\mathbf x})_+\,d\nu,\qquad
q(\mathbf x)=\int (-F_{\mathbf x})_+\,d\nu.$$

Then $p-q=D_{\mathbf x}$, so (2.1) is the exact identity

$$\boxed{B-A=2\int\min\{p(\mathbf x),q(\mathbf x)\}\,d\nu^{\otimes d}(\mathbf x).} \tag{3.1}$$

The right side includes all singular horizontal tuples. Equation (3.1) gives both a diagnostic for failed equality and a quantitative certificate interface.

For example, let $x_1,\ldots,x_d,y_+,y_-$ be distinct atoms with positive probabilities $r_1,\ldots,r_d,s_+,s_-$. Suppose

$$F_{\mathbf x}(y_+)=D_+>0,\qquad F_{\mathbf x}(y_-)=-D_-<0.$$

The $d!$ permutations of the first $d$ atoms contribute disjoint ordered tuples to (3.1), giving

$$\boxed{B-A\ge 2d!\left(\prod_{i=1}^d r_i\right)
       \min\{s_+D_+,s_-D_-\}>0.} \tag{3.2}$$

For arbitrary laws, replace atoms by neighborhoods on which both determinant signs have a uniform strict margin; the product of their positive measures gives an analogous bound. Such a sign-changing tuple exists whenever $B>A$: otherwise the nonnegative integrand in (3.1) would vanish everywhere on the support. Thus every failure of simplex support has a witness using at most $d+2$ support points. Formula (3.2), unlike the geometric stability modulus below, is explicit.

## 4. Cone-volume laws and arbitrary convex bodies

Translate an interior point of $K$ to zero. Write $h=h_K$, $v=|K|$, and let $S_K$ be surface area measure on the unit sphere. We use the classical identities

$$\int u\,dS_K(u)=0,\qquad \int h(u)\,dS_K(u)=dv. \tag{4.1}$$

The normalized cone-volume measure is $h(u)dS_K(u)/(dv)$. Push it forward under

$$u\longmapsto \frac{u}{h(u)}$$

to obtain a probability law $\nu_K$ on $\mathbb R^d$. It is centered by (4.1), has compact support, and spans the space. For the last claim, Cauchy's projection formula shows that surface area measure is not supported in any proper linear subspace: every projection of a full-dimensional body has positive volume. Every point $u/h(u)$ lies on $\partial K^\circ$.

### Proposition 4.1. Exact probabilistic representation

$$\boxed{a(K)=\frac{B(\nu_K)}{(d+1)A(\nu_K)}.} \tag{4.2}$$

**Proof.** For a polytope put $u_i=s_i n_i$, $b_i=s_i h_i$. The law has atoms $x_i=u_i/b_i=n_i/h_i$ with probabilities $b_i/(dv)$. Distinct-subset expansion, including the permutation factors, gives

$$A(\nu_K)=\frac{d!}{(dv)^d}\sum_{|I|=d}|\det(u_i:i\in I)|,$$

$$B(\nu_K)=\frac{(d+1)!}{(dv)^{d+1}}
\sum_{|I|=d+1}|\det((u_i,b_i):i\in I)|.$$

This proves (4.2) for polytopes. For general $K$, take full-dimensional polytopes converging in Hausdorff distance, all containing a common ball about zero. Their support functions converge uniformly, are bounded away from zero, and their surface area measures converge weakly. Consequently the corresponding $\nu_K$ converge weakly on a common compact set. The determinant expectations converge, as do the invariant $a$ and the positive denominator $A$. This proves (4.2). $\square$

For clarity, weak continuity of surface area measure, Cauchy's formula, the volume first-variation formula below, and Brunn--Minkowski are classical convex-geometric inputs, not newly asserted theorems. References are given in Section 9. The continuity passage proves the identity; the equality classification is proved independently next, not inferred from continuity of strict inequalities.

### Theorem 4.2. Simplex rigidity without a polytope assumption

For every full-dimensional convex body in dimension $d\ge1$,

$$a(K)\ge\frac1{d+1},$$

with equality if and only if $K$ is a simplex.

**Proof.** The inequality and the necessity that $\nu_K$ have exactly $d+1$ support points follow from (4.2) and Theorem 2.1. Write these points as $x_1,\ldots,x_{d+1}$. They form a simplex containing zero in its interior, so

$$T=\{z:\langle x_i,z\rangle\le1\text{ for }i=1,\ldots,d+1\}$$

is a bounded simplex containing $K$. The radial map $u\mapsto u/h_K(u)$ is injective, and its weighting density is strictly positive. Therefore $S_K$ is supported on the $d+1$ directions $u_i=x_i/\|x_i\|$. In those directions,

$$h_T(u_i)=h_K(u_i)=1/\|x_i\|.$$

Here is an explicit reason this forces $K=T$, avoiding an unproved passage from discrete normals to a polytope. The classical first-variation formula and Brunn--Minkowski give

$$\left.\frac{d}{dt}\right|_{t=0+}|K+tT|
=\int h_T\,dS_K
\ge d|K|^{(d-1)/d}|T|^{1/d}.$$

The inequality follows by differentiating
$|K+tT|^{1/d}\ge |K|^{1/d}+t|T|^{1/d}$ at zero. Since the integral equals $\int h_K\,dS_K=d|K|$, it follows that $|T|\le|K|$. Together with $K\subseteq T$, equality of volumes gives $K=T$. Strict inclusion of full-dimensional compact convex sets would contain a positive-volume cap, so it cannot preserve volume. In dimension one the conclusion also follows directly because every convex body is an interval.

The converse was computed for simplices in v2 and also follows from their $(d+1)$-point cone-volume laws and Theorem 2.1. $\square$

In particular the cone ratio satisfies the sharp lower bound

$$\frac{R(\mathcal P K)}{R(K)}
\ge\left(1+\frac1d\right)^d\frac{d+2}{d+1},$$

with equality exactly for simplex bases. The general strict upper estimate $a(K)<1$ also follows from Theorem 2.1, although that is not asserted to be the best convex-body upper bound.

## 5. Dimensionwise affine stability

### Theorem 5.1. Stability in maximum-simplex position

Fix $d\ge1$ and $\varepsilon>0$. There is a positive $\delta(d,\varepsilon)$ with the stability property stated in Section 1. The choice is uniform over all full-dimensional convex bodies of that dimension and over every maximum-volume inscribed simplex of each body.

**Proof.** Fix a reference simplex $\Delta$ with centroid zero. For each body and each maximum-volume inscribed simplex, apply an invertible affine map taking the simplex to $\Delta$. Such a simplex exists by compactness of $K^{d+1}$ and is nondegenerate because $K$ has interior.

Let $v_1,\ldots,v_{d+1}$ be the vertices of $\Delta$, and let $\alpha_i(x)$ be its barycentric coordinate functions. Replacing vertex $v_i$ by a point $x$ changes the simplex volume by the factor $|\alpha_i(x)|$. Maximality therefore gives

$$\Delta\subseteq K\subseteq P:=\{x:|\alpha_i(x)|\le1\text{ for every }i\}. \tag{5.1}$$

The set $P$ is bounded, since $x=\sum_i\alpha_i(x)v_i$. The normalized bodies form a compact family in Hausdorff distance: their support functions are uniformly bounded and uniformly Lipschitz, so Arzela--Ascoli and the support-function characterization give subsequential compactness. The common inscribed simplex keeps all limits full-dimensional.

The maximum volume of an inscribed simplex is continuous on this family. This follows either by compact maximization of the determinant, or by approximating the finitely many vertices for the lower limit and taking convergent maximizing vertices for the upper limit.

Suppose the asserted uniform modulus fails. There are normalized bodies $K_j$ with $a(K_j)\to1/(d+1)$ for which $K_j\not\subseteq(1+\varepsilon)\Delta$, while $\Delta$ is a maximum-volume inscribed simplex of each $K_j$. Take a Hausdorff limit $K_\infty$. Continuity of $a$ and Theorem 4.2 imply that $K_\infty$ is a simplex. Its maximum inscribed simplex volume is $|\Delta|$ by continuity; since $K_\infty$ itself is a simplex, $|K_\infty|=|\Delta|$. The inclusion $\Delta\subseteq K_\infty$ yields $K_\infty=\Delta$.

Let $r>0$ satisfy $rB_2^d\subseteq\Delta$. Hausdorff convergence then gives, eventually,

$$K_j\subseteq\Delta+\varepsilon r B_2^d\subseteq(1+\varepsilon)\Delta,$$

contradicting the choice of $K_j$. Undoing the affine maps gives precisely the stated inclusions about the centroid of the originally chosen simplex. $\square$

The proof gives no explicit exponent or lower estimate for $\delta(d,\varepsilon)$. Formula (3.2) gives a local, measure-weighted defect witness, but converting those weights and determinants into a uniform explicit affine-distance bound remains a separate problem.

## 6. A sharp bound for symmetric boundary laws

The next statement concerns an even probability law $\nu$ supported on the boundary of an origin-symmetric full-dimensional convex body $C$. Full span is assumed. Compactness supplies all moment hypotheses. The boundary condition is essential.

### Lemma 6.1. A balanced Rademacher estimate

If $c_1,\ldots,c_N$ are real and $|c_i|\le\frac12\sum_j|c_j|$ for every $i$, then independent uniform signs satisfy

$$\mathbb E_\epsilon\left|\sum_i\epsilon_i c_i\right|
\le\frac12\sum_i|c_i|. \tag{6.1}$$

For $N=3$ equality always holds under the balance hypothesis; for $N=2$ it also holds.

**Proof.** Remove the zero vector case and normalize the sum of absolute coefficients to one. The polytope

$$\{t\in[0,1/2]^N:\sum_i t_i=1\}$$

has as its vertices exactly the vectors having two coordinates $1/2$ and all others zero. Indeed two coordinates strictly between their bounds allow a small opposite perturbation; at an extreme point at most one coordinate is interior, and the sum constraint rules out exactly one interior coordinate. The convex function $t\mapsto\mathbb E|\sum_i\epsilon_i t_i|$ takes the value $1/2$ at every vertex, proving (6.1). For three balanced nonnegative coefficients, averaging the four sign patterns modulo common sign gives

$$\tfrac14\bigl[(c_1+c_2+c_3)+(-c_1+c_2+c_3)
 +(c_1-c_2+c_3)+(c_1+c_2-c_3)\bigr]
=\tfrac12(c_1+c_2+c_3).$$

Balance makes all four bracketed terms nonnegative. The two-coefficient assertion is immediate. $\square$

### Theorem 6.2. Symmetric boundary comparison

For the even boundary law just specified,

$$\boxed{B(\nu)\le\frac{d+1}{2}A(\nu).} \tag{6.2}$$

In dimension two, equality holds for every such law.

**Proof.** Fix $x_1,\ldots,x_{d+1}\in\partial C$. Let $c_i$ be the signed horizontal cofactors, so

$$\sum_i c_i x_i=0.$$

If all cofactors vanish the desired pointwise estimate is trivial. Otherwise the Minkowski norm with unit ball $C$, for which $\|x_i\|_C=1$, gives

$$|c_i|=\|c_i x_i\|_C\le\sum_{j\ne i}|c_j|.$$

The coefficients satisfy Lemma 6.1. Under independent sign changes of the sampled points, the absolute lifted determinant is $|\sum_i\epsilon_i c_i|$: a common product of all signs cancels in absolute value. Evenness of the law allows this independent sign averaging without changing $B$. Applying (6.1) and then integrating gives

$$B\le\frac12\sum_{i=1}^{d+1}\mathbb E|c_i|=\frac{d+1}{2}A.$$

For $d=2$ the pointwise three-coefficient identity is equality, so its integral is equality as well. $\square$

### Corollary 6.3. Sharp symmetric cone bound

If $K$ is centrally symmetric, translate its center to zero. Its cone-volume law $\nu_K$ is even and supported on $\partial K^\circ$. Equations (4.2) and (6.2) prove

$$a(K)\le\frac12,\qquad
\frac{R(\mathcal P K)}{R(K)}\le\frac32\left(1+\frac1d\right)^d.$$

Parallelotopes attain equality, using the interval value $a=1/2$ and the dimension-weighted product formula from v2. Theorem 6.2 gives $a=1/2$ for every centrally symmetric planar body; products of such bodies and intervals again attain equality. These observations establish sharpness in every dimension, not a complete classification of all maximizers.

Planar constancy does not extend to all centrally symmetric bodies in higher dimensions. For the three-dimensional crosspolytope $O_3=\operatorname{conv}(\pm e_1,\pm e_2,\pm e_3)$, the volume is $4/3$ and the eight facet data are $(u_\epsilon,b_\epsilon)=(\epsilon/2,1/2)$, $\epsilon\in\{-1,1\}^3$. Thus its cone-volume law is uniform on the eight cube vertices. Direct rational determinant sums, independently reproduced in the certificate, give

$$A=\frac32,\qquad B=\frac{45}{16},\qquad
\boxed{a(O_3)=\frac{15}{32}<\frac12,\qquad R(O_3)=9.}$$

Using the dimension-weighted product formula, for every $d\ge3$ the product of $O_3$ and $d-3$ intervals has

$$a=\frac12-\frac3{32d}<\frac12.$$

The boundary hypothesis cannot be replaced by evenness alone. For the equally weighted law on $\{\pm e_1,\ldots,\pm e_d\}$ one has $B/A=(d+1)/2$. Mix it with an atom of mass $1-t$ at zero. The same decomposition as in Section 2 gives

$$\frac{B}{(d+1)A}=1-\frac t2>\frac12\qquad(0<t<1).$$

This is a centered, spanning, even law, but is not a law supported on the boundary of an origin-symmetric convex body. It is an explicit guard against omitting the geometric assumption.

## 7. No finite maximizer of the join spectral parameter

The spectral supplement to v2 proves that joins preserve $\lambda$ under self-joining and that a join-closed class containing a point has asymptotic $R$-growth rate $e\sup\lambda$. Nonattainment of $R^{1/d}$ alone does not imply nonattainment of $\lambda$, so the latter needs its own argument.

### Theorem 7.1. Explicit spectral amplification by a Cartesian square

Let $K$ have positive dimension $d$, and let $a=a(K)>0$, $Q=Q(K)>0$, and $\lambda=Q^{1/(d+1)}$. For every integer $k\ge1$ satisfying

$$\boxed{k\lambda^2\ge4a^2(d+1),} \tag{7.1}$$

the body $L=K^{*k}\times K^{*k}$ satisfies $\lambda(L)>\lambda(K)$. Its dimension is $2k(d+1)-2$. Such an integer $k$ always exists.

**Proof.** Put $D=d+1$, $N=kD-1$ and $J=K^{*k}$. The exact v2 formulas give

$$a(J)=a/k,\qquad Q(J)=Q^k=\lambda^{N+1}.$$

Using the product rule, and simplifying factorials,

$$Q(J\times J)=\frac{k}{a}\frac{g(N)^2}{g(2N)}\lambda^{2N+2}
=\frac{k}{a}\frac{\binom{2N}{N}}{4^N}\lambda^{2N+2}.$$

Thus the exact strict comparison is

$$\boxed{\lambda(J\times J)>\lambda(K)
\quad\Longleftrightarrow\quad
\frac{k\lambda}{a}\frac{\binom{2N}{N}}{4^N}>1.} \tag{7.2}$$

For all $N\ge1$, the elementary central-binomial bound is

$$\frac{\binom{2N}{N}}{4^N}\ge\frac1{2\sqrt N}.$$

For completeness, equality holds at $N=1$. The ratio of successive normalized central binomial coefficients is $(2N+1)/(2N+2)$, and its square is at least $N/(N+1)$ because $(2N+1)^2-4N(N+1)=1$. This proves the bound by induction.

Condition (7.1) implies

$$k^2\lambda^2\ge4a^2kD>4a^2(kD-1)=4a^2N.$$

Consequently the right side of (7.2) is at least $k\lambda/(2a\sqrt N)>1$, proving strict amplification. $\square$

No asymptotic estimate, unbounded solver search, or numerical logarithm enters this proof. For rational $a,Q$, the exact strict comparison (7.2) can be checked without taking an irrational root:

$$\boxed{\left(\frac{k}{a}\frac{\binom{2N}{N}}{4^N}\right)^{d+1}Q>1.} \tag{7.3}$$

Even the sufficient condition (7.1) is rationally checkable, by raising positive quantities to the integer power $d+1$:

$$k^{d+1}Q^2\ge\bigl(4a^2(d+1)\bigr)^{d+1}.$$

The theorem applies to the recursive point-generated product/join class, any other product/join-closed class containing $K$, and all convex bodies. It remains valid when the corresponding supremum is infinite. It shows that no finite hull vertex or finite seed can be a final spectral maximizer. It does **not** show that the existing $T_5$-based orbit is optimal, improve its certified numerical rate, or provide an upper envelope for all operation trees.

The supplied exact tests include nontrivial seed values $Q<1$ and $Q>1$, not only simplex seeds with $Q=1$. The universal conclusion follows from the proof above, not from those examples.

## 8. Reproduction and proof scope

The finite data and exact checker accompany this note in `certificates/` and `code/`. The producer uses unordered distinct-subset sums and rational Gaussian elimination. Spectral recipes are evaluated through the factorial product/join formulas, while the checker uses the central-binomial reduction and cross-powered rational comparisons. The checker independently enumerates ordered tuples and uses a permutation determinant, verifies centering and span, recomputes both expectations and the complete defect identity, checks equality classification on the fixed test laws, validates explicit sign-changing witnesses, and checks symmetric-boundary assumptions from rational norm slabs. It also computes all 56 horizontal and 70 lifted minors of the octahedron directly. It imports no producer code.

The tests include nonuniform simplex laws, laws with an interior atom, dependent horizontal tuples, symmetric boundary laws, and the explicit failure when the boundary assumption is removed. Deliberate mutations must be rejected, including a change of the mean, a false symmetry-bound claim and a corrupted determinant result. Python optimization must not disable checks. These are finite arithmetic consistency tests; Theorems 2.1, 4.2, 5.1, 6.2 and 7.1 are proved by the written arguments, not by extrapolating the tests.

This note has not been independently human-refereed or fully formalized. The explicit quantitative affine stability modulus, the complete equality class for the symmetric upper bound in higher dimensions, and the optimal recursive-class spectral supremum remain undetermined here.

## 9. Inputs, comparison and provenance

**Internal dependencies.** Entry 005 v2 supplies the facet definition of $a$, its affine invariance and continuity, and the exact product/join/pyramid formulas. The v2 spectral supplement supplies the earlier definition of $\lambda$ and its relation to asymptotic growth. The present general probability theorem, its defect identity, the extension to arbitrary-body equality, the qualitative stability argument, the symmetric-boundary estimate and the spectral nonattainment argument are the additional statements being recorded. The inequalities based only on Jensen and triangle inequalities are elementary; they are not advertised as an important new inequality merely because their equality cases are useful here.

**Classical convex-geometric inputs.** R. Schneider, *Convex Bodies: The Brunn--Minkowski Theory*, second expanded edition, Cambridge University Press, 2014, covers surface area measures, their weak continuity, Cauchy's projection formula, volume first variation and Brunn--Minkowski. K. J. Boroczky and M. Henk, *Cone-volume measure and stability*, [author-hosted manuscript](https://www.renyi.hu/~carlos/cone-volume-stability.pdf), gives the standard cone-volume measure definition in equation (1.1). Our law is its normalization followed by the explicitly displayed radial map; cone-volume measure itself is not introduced here.

**Random-simplex background.** L. Rademacher, *On the monotonicity of the expected volume of a random simplex*, Mathematika 58 (2012), 77--91, DOI 10.1112/S0025579311002063, [author-hosted paper](https://www.math.ucdavis.edu/~lrademac/monotonicity.pdf), studies inclusion monotonicity and records the second-moment covariance identity. Those statements are different from the first-absolute-moment equality classification for arbitrary centered laws proved here. The broad random-simplex literature has not been exhaustively compared.

**Cone literature.** C. Saroglou, *Volumes of projection bodies of some classes of convex bodies*, Mathematika 57 (2011), 329--353, DOI 10.1112/S0025579311001860, studies sharp three-dimensional cone, double-cone and zonoid extrema. Cone extrema and planar special cases therefore have substantial prior literature. The publisher abstract and author listing were checked; full-text retrieval failed in this pass. No claim of disjointness from all its formulas is made.

**Upstream.** OpenAI family 088, *A product counterexample to the simplex maximum for projection-body volume*, pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, supplies the attributed classical product/simplex starting point used by entry 005. Its unrestricted counterexamples and the earlier work it cites are not reclassified as our discoveries. The source was read again in this pass. No theorem in the present note assumes the correctness of unrelated upstream conjecture-resolution manuscripts.

The publication record documents when this repository disclosed these statements; it is not a certificate of first priority. Further prior-work comparison may require changing the novelty assessment without deleting correct proofs.
