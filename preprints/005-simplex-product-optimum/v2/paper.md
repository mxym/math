# Projection-volume calculus for joins and Cartesian products

**mxym — AI-assisted research manuscript. Version 2, core proof disclosure, 7 October 2026.**

This extends entry 005; it does not change or contradict the exact optimization over products of simplices in v1.1. All priority and best-known-bound comparisons remain unverified. The results below have written proofs, but are not externally refereed or proof-assistant formalized.

## 1. Definitions and main conclusions

For a full-dimensional convex body $K\subset\mathbb R^d$, $d\ge1$, put

$$R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!},\qquad c_d=(d+1)g(d).$$

Here $h_{\Pi K}(u)$ is the $(d-1)$-dimensional volume of the orthogonal projection of $K$ onto $u^\perp$, for unit $u$. For a nondegenerate interval the convention is $\Pi K=[-1,1]$, so $R(K)=2$. A point has formal parameters $d=0$, $g(0)=1$, $R=1$, and $a=1$, used only for the join formulas below.

The **join** of $A\subset\mathbb R^r$ and $B\subset\mathbb R^s$ is

$$A*B=\operatorname{conv}\{(x,0,0):x\in A;\ (0,y,1):y\in B\}\subset\mathbb R^{r+s+1}.$$

A join with a point is a pyramid, denoted $\mathcal P K$. Its affine shape is independent of the chosen apex off the affine hull of its base. Cartesian products are taken in independent coordinate spaces. Iteration is denoted $\mathcal P^t$.

We define a positive affine invariant $a(K)$ and prove the following calculus. In the product line $d=r+s$; in the join line $n=r+s+1$:

$$\boxed{R(A\times B)=R(A)R(B),\qquad a(A\times B)=\frac{r a(A)+s a(B)}{r+s}.}$$

$$\boxed{R(A*B)=\frac{g(n)}{g(r)g(s)}R(A)R(B)\bigl(a(A)+a(B)\bigr),\qquad a(A*B)=\frac{a(A)a(B)}{a(A)+a(B)}.}$$

In particular, for $K$ of dimension $d$ and every integer $t\ge0$,

$$\boxed{R(\mathcal P^t K)=\frac{g(d+t)}{g(d)}R(K)(1+t a(K)),\qquad a(\mathcal P^t K)=\frac{a(K)}{1+t a(K)}.}$$

These are identities, not inequalities obtained by numerical optimization. They hold for all full-dimensional convex bodies by the continuity argument in Section 5.

Three consequences are proved here:

* The fourteen-dimensional polytope $\mathcal P^6(T_4\times T_4)$ has $R/c_{14}=385/384>1$. More generally, an explicit pyramid family exceeds the simplex value in every dimension at least fourteen.
* For a fixed body $K$, some pyramid over a Cartesian power improves its per-dimension value if and only if $R(K)^{1/d}<e(1+a(K))$.
* More strongly, **every fixed body can be improved as a repeated block**: a join of two sufficiently large Cartesian powers has strictly larger per-dimension value. Consequently the supremum of $R(K)^{1/\dim K}$ over all dimensions cannot be attained by any finite-dimensional body. The same nonattainment statement holds in every class containing a positive-dimensional body and closed under products and joins.

No assertion here identifies a maximizer in a fixed unrestricted dimension, improves the known smallest dimension of an unrestricted counterexample, or determines the optimal asymptotic constant.

## 2. Lifted facet zonotopes

Let $K$ first be a full-dimensional polytope of dimension $d\ge1$ and volume $v$. For each facet $i$, let $s_i$ be its $(d-1)$-volume, $\nu_i$ its outward unit normal, and $h_i$ its support number. Define

$$u_i=s_i\nu_i,\qquad b_i=s_i h_i.$$

In dimension one the two endpoint facets have zero-dimensional volume one. Translation of the origin is allowed. The divergence theorem, applied to constant vector fields and the radial vector field, gives

$$\sum_i u_i=0,\qquad \sum_i b_i=dv.$$

For clarity, the first identity also follows by the cancellation of oriented facets of a triangulation. When the origin is interior, the second follows by partitioning $K$ into the pyramids with apex zero and bases its facets. Translation does not change either identity.

Write

$$P(K)=\sum_{|I|=d}|\det(u_i:i\in I)|,\qquad S(K)=\sum_{|I|=d+1}|\det((u_i,b_i):i\in I)|.$$

Columns are placed in any fixed order; the absolute values remove the order dependence. Cauchy's projection formula and the zonotope volume formula imply

$$P(K)=|\Pi K|,\qquad S(K)=\left|\sum_i[0,(u_i,b_i)]\right|_{d+1}.$$

To fix normalizations: almost every line parallel to a unit vector meets exactly one entrance and one exit facet, whence $h_{\Pi K}(u)=\tfrac12\sum_i|\langle u_i,u\rangle|$. Thus $\Pi K$ is a translate of $\sum_i[0,u_i]$. The volume of a zonotope with generators $w_i$ in dimension $m$ is the sum of the absolute $m$-minors. One proof adds the generators successively: adding $[0,w]$ increases volume by $|w|$ times the volume of the orthogonal projection onto $w^\perp$. Induction in the number of generators and in the dimension gives precisely the determinant sum, also for dependent generators.

Define

$$\boxed{a(K)=\frac{S(K)}{d v P(K)}.}$$

The lifted generators span dimension $d+1$: their sum is $(0,dv)$, and their horizontal projections span dimension $d$. Hence $S(K)>0$ and $a(K)>0$.

### Lemma 2.1. Affine invariance and a lower bound

Both $R$ and $a$ are affine invariant, and

$$\frac1{d+1}\le a(K)\le1.$$

For a simplex, $a(T_d)=1/(d+1)$.

**Proof.** Under $x\mapsto Lx+t$, put $D=|\det L|$. Facet data transform as

$$u_i'=D L^{-\mathsf T}u_i,\qquad b_i'=D b_i+\langle t,u_i'\rangle.$$

The horizontal map has absolute determinant $D^{d-1}$, while the map on lifted generators has absolute determinant $D^d$. The denominators in $R$ and $a$ scale by exactly these factors. This proves invariance, including orientation-reversing maps.

Choose any $d$-set $J$ with independent horizontal generators and solve $\langle u_j,x_J\rangle=b_j$ for $j\in J$. For an additional index $i$, the absolute lifted determinant is

$$|\det(u_j:j\in J)|\,|b_i-\langle u_i,x_J\rangle|.$$

The signed residuals sum to $dv$. The triangle inequality, followed by summing over $J$, therefore gives

$$(d+1)S(K)\ge dv P(K).$$

Dependent $J$ contribute a nonnegative quantity on the left and zero to the required lower bound. Each lifted $(d+1)$-minor is counted exactly $d+1$ times in this sum.

For the upper bound translate an interior point to zero, so every $b_i>0$. Expanding each lifted determinant in its last row and summing gives

$$S(K)\le\sum_{|J|=d}|\det(u_j:j\in J)|\sum_{i\notin J}b_i\le dv P(K).$$

For a simplex there are exactly $d+1$ facets. Its unique lifted determinant equals $dv$ times each absolute horizontal $d$-minor; alternatively use the simplex computation below. Thus $a=1/(d+1)$. $\square$

For the standard simplex $T_d=\operatorname{conv}(0,e_1,\ldots,e_d)$, the horizontal generators are $-e_i/(d-1)!$ and $(1,\ldots,1)/(d-1)!$. All its $d+1$ maximal minors have absolute value $1/(d-1)!^d$, and $|T_d|=1/d!$. Therefore $R(T_d)=c_d$. In particular, the calculation includes $d=1$.

## 3. Products and pyramids

For $A$ and $B$ of positive dimensions $r,s$, write their volumes as $v,w$ and their horizontal and support data as $(u_i,b_i)$ and $(z_j,c_j)$. The product has facet data

$$(w u_i,0;w b_i),\qquad (0,v z_j;v c_j).$$

A nonzero horizontal maximal minor uses $r$ generators of the first kind and $s$ of the second. A nonzero lifted maximal minor uses either $(r+1,s)$ or $(r,s+1)$. Thus

$$P(A\times B)=w^r v^s P(A)P(B),$$

$$S(A\times B)=w^{r+1}v^s S(A)P(B)+w^r v^{s+1}P(A)S(B).$$

Dividing by the defining volume factors proves the product identities in Section 1.

Next realize $\mathcal P K=\operatorname{conv}(K\times\{0\},(0,1))$. Its volume is $v/(d+1)$, and its facet area-normal vectors are

$$(-v e_{d+1}),\qquad \frac1d(u_i,b_i).$$

Indeed the side over facet $i$ lies in $\langle u_i,x\rangle+b_i t=b_i$; integrating its parallel sections, or using the base-times-height formula, gives the factor $1/d$. For the interval base the same statement is the elementary edge-normal formula for a triangle.

The projection-body minors containing the bottom facet sum to $vP(K)/d^d$, while the minors not containing it sum to $S(K)/d^{d+1}$. Consequently

$$P(\mathcal P K)=\frac{vP(K)}{d^d}(1+a(K)).$$

At the origin $(0,0)$ the lifted bottom vector is $(0,-v,0)$ and each lifted side vector is $(u_i,b_i,b_i)/d$. All side vectors lie in the hyperplane in which the last two coordinates agree. Every nonzero lifted maximal minor therefore includes the bottom vector, giving

$$S(\mathcal P K)=\frac{v}{d^{d+1}}S(K).$$

It follows that

$$R(\mathcal P K)=\left(1+\frac1d\right)^d(1+a(K))R(K),\qquad a(\mathcal P K)=\frac{a(K)}{1+a(K)}.$$

Since $g(d+1)/g(d)=(1+1/d)^d$, iteration telescopes to the stated formula for $\mathcal P^t K$.

## 4. The full join formula

Let $r,s\ge1$, $n=r+s+1$, and $J=A*B$. Slicing at the last coordinate $t$ gives

$$v_J=|J|=\frac{r!s!}{n!}|A||B|.$$

Let

$$\alpha=\frac{(r-1)!s!}{(r+s)!}|B|=\frac{n v_J}{r|A|},\qquad \beta=\frac{r!(s-1)!}{(r+s)!}|A|=\frac{n v_J}{s|B|}.$$

The facets are joins of a facet of one factor with the whole other factor. Their area-normal vectors are

$$\alpha(u_i,0,b_i),\qquad \beta(0,z_j,-c_j).$$

For example, a side of the first kind has area Jacobian $(1-t)^{r-1}t^s\sqrt{1+h_i^2}$ times the product area on its two factors. Integration gives the factor $(r-1)!s!/(r+s)!$; multiplying by its unit normal gives the displayed vector. The second kind is identical with the factors exchanged.

The horizontal maximal minors split into the two patterns $(r+1,s)$ and $(r,s+1)$, hence

$$P(J)=\alpha^{r+1}\beta^s S(A)P(B)+\alpha^r\beta^{s+1}P(A)S(B).$$

With the origin used in the definition of $J$, the lifted vectors are

$$\alpha(u_i,0,b_i,b_i),\qquad \beta(0,z_j,-c_j,0).$$

The two families lie in complementary subspaces of dimensions $r+1$ and $s+1$. Thus

$$S(J)=\alpha^{r+1}\beta^{s+1}S(A)S(B).$$

Substituting $S(A)=r|A|P(A)a(A)$, and the analogous identity for $B$, gives

$$R(J)=\frac{g(n)}{g(r)g(s)}R(A)R(B)(a(A)+a(B)),\qquad a(J)=\frac{a(A)a(B)}{a(A)+a(B)}.$$

A point factor reduces to Section 3; two point factors give an interval. This accounts for every zero-dimensional boundary case used in recursive constructions.

A useful diagonal form is obtained by setting

$$H(K)=\frac1{a(K)},\qquad Q(K)=\frac{a(K)R(K)}{g(\dim K)}.$$

Then

$$\boxed{H(A*B)=H(A)+H(B),\qquad Q(A*B)=Q(A)Q(B).}$$

In particular, for the join of $k$ copies of a $d$-dimensional body $K$, writing $N=k(d+1)-1$,

$$R(K^{*k})=g(N)\frac{k}{a(K)}Q(K)^k.$$

## 5. Extension to arbitrary convex bodies

For a full-dimensional convex body define

$$a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1.$$

This agrees with the facet definition for polytopes. It is continuous under Hausdorff convergence of full-dimensional bodies. Here are sufficient details: after translating an interior point to zero, approximating polytopes and their limit contain a common ball. Hausdorff closeness then gives two-sided multiplicative containments with factors tending to one. The same containments hold after every orthogonal projection, so the support functions of the projection bodies converge uniformly and their volumes converge. Ordinary volume convergence follows from the original containments. Pyramids, joins in the displayed coordinates, and products also converge in Hausdorff distance.

Approximate each factor by full-dimensional polytopes and pass to the limit in the identities already proved. The lower bound $a(K)\ge1/(d+1)$ and the upper bound $a(K)\le1$ pass to the limit as well. In particular the invariant remains positive. All the formulas above therefore hold for arbitrary full-dimensional convex bodies without smoothness or strict-convexity assumptions.

## 6. Exact pyramid tests and the fourteen-dimensional construction

### Theorem 6.1. Eventual comparison with a simplex

For $K$ of dimension $d$, some iterated pyramid over $K$ has $R>c_{d+t}$ if and only if

$$a(K)R(K)>g(d).$$

When this strict inequality holds, the exact admissible nonnegative integers $t$ are those satisfying

$$t\bigl(a(K)R(K)-g(d)\bigr)>(d+1)g(d)-R(K).$$

**Proof.** The ratio is

$$\frac{R(\mathcal P^tK)}{c_{d+t}}=\frac{R(K)}{g(d)}\frac{1+t a(K)}{d+t+1}.$$

The second factor is nondecreasing in $t$ because $(d+1)a(K)\ge1$, and its limit is $a(K)$. Rearranging the strict comparison proves both statements, including the equality boundary. $\square$

Take $K=T_4\times T_4$. The identities above give

$$d=8,\qquad a(K)=\frac15,\qquad \frac{R(K)}{g(8)}=\frac{875}{128}.$$

For every $n\ge8$ we therefore have the exact formula

$$\boxed{\frac{R(\mathcal P^{n-8}(T_4\times T_4))}{c_n}=\frac{175(n-3)}{128(n+1)}.}$$

The ratio exceeds one exactly when $47n>653$, namely for integers $n\ge14$. At $n=14$ it is $385/384$. The body has $n+2$ facets: the base product has ten, and each pyramid adds one.

This does not improve the known unrestricted dimension-nine counterexamples cited by the upstream source. It improves the elementary construction scope of our v1.1, whose *product-only* first failure was dimension twenty. No global minimal-dimension assertion follows from this example alone.

### Theorem 6.2. Exact criterion for product-pyramid amplification

Set $\rho=R(K)^{1/d}$. There exist integers $k,t\ge1$ such that

$$R(\mathcal P^t(K^k))^{1/(kd+t)}>\rho$$

if and only if

$$\rho<e(1+a(K)).$$

**Proof.** The ratio of the new value to $\rho^{kd+t}$ is

$$\frac{g(kd+t)}{g(kd)}\frac{1+t a(K)}{\rho^t}.$$

Every factor $g(m+1)/g(m)=(1+1/m)^m$ is strictly less than $e$, and $1+t a\le(1+a)^t$ for integer $t\ge1$. This excludes an improvement when $\rho\ge e(1+a)$, including equality. Conversely take $t=1$ and let $k\to\infty$; the remaining ratio tends to $e(1+a)/\rho>1$. $\square$

## 7. Universal strict amplification by a join

### Theorem 7.1. No finite-dimensional optimal repeated block

Let $K$ be any full-dimensional convex body of positive dimension $d$, and put $a=a(K)>0$ and $\rho=R(K)^{1/d}$. For every integer $m\ge1$ with

$$2a\sqrt{3md+1}\ge\rho,$$

the body

$$L=(K^m)*(K^m),\qquad \dim L=2md+1,$$

satisfies $R(L)^{1/(2md+1)}>\rho$. Such an $m$ always exists.

**Proof.** Put $q=md$. The calculus gives

$$\frac{R(L)}{\rho^{2q+1}}=\frac{2a}{\rho}\frac{g(2q+1)}{g(q)^2}=\frac{2a}{\rho}\frac{(2+1/q)^{2q}}{\binom{2q}{q}}.$$

The elementary central-binomial bound

$$\binom{2q}{q}\le\frac{4^q}{\sqrt{3q+1}}\qquad(q\ge1)$$

follows by induction. The initial case is equality. In the induction step the needed squared comparison reduces to

$$(3q+1)(2q+2)^2-(3q+4)(2q+1)^2=q\ge0.$$

Since $(2+1/q)^{2q}>4^q$, the displayed ratio is strictly larger than $(2a/\rho)\sqrt{3q+1}$. The stated sufficient condition proves the result. $\square$

The conclusion applies, in particular, to every member of the class generated from points by finitely many products and joins. This class strictly enlarges products of simplices. Thus a finite list of proposed repeated blocks cannot close its all-dimensional optimization: each individual block admits a strictly better block in the same class. This is a structural obstruction to a finite-block optimum, not a determination of the limiting optimum.

## Provenance and verification scope

The product identity and simplex value are inherited from classical projection-body geometry and were rederived in OpenAI, *A product counterexample to the simplex maximum for projection-body volume*, 24 September 2026, family 088, pinned upstream commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Entry 005 v1.1 supplies the exact optimization over simplex products. The lifted invariant, full join calculus, amplification statements, and explicit pyramid extension in this note are the additional results being recorded here, subject to literature comparison rather than a priority claim.

The proofs above use facet geometry, determinant identities, ordinary volume continuity, and elementary real analysis. No floating-point optimization, SAT/SMT answer, unverified solver assumption, or private transcript is a proof dependency. This source disclosure does not claim external independent review or complete formalization.
