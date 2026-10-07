# Projection-volume calculus for joins and Cartesian products

**mxym — AI-assisted research manuscript. Version 2, complete written proof and exact certificates, 7 October 2026.**

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

The following consequences are proved here:

* The lower bound $a(K)\ge1/(d+1)$ has equality exactly for simplices among full-dimensional polytopes.

* The fourteen-dimensional polytope $\mathcal P^6(T_4\times T_4)$ has $R/c_{14}=385/384>1$. More generally, an explicit pyramid family exceeds the simplex value in every dimension at least fourteen.
* For a fixed body $K$, some pyramid over a Cartesian power improves its per-dimension value if and only if $R(K)^{1/d}<e(1+a(K))$.
* More strongly, **every fixed body can be improved as a repeated block**: a join of two sufficiently large Cartesian powers has strictly larger per-dimension value. Consequently the supremum of $R(K)^{1/\dim K}$ over all dimensions cannot be attained by any finite-dimensional body. The same nonattainment statement holds in every class containing a positive-dimensional body and closed under products and joins.

* The first counterexample within the entire point-generated product/join class occurs in dimension fourteen, with exact maximum $(385/384)c_{14}$ there.
* An explicit self-similar family has a rigorously certified asymptotic rate $2.8534<\Lambda<2.8535$, and gives an eventual factor greater than $1.015^n$ over the complete simplex-product optimum in every sufficiently large dimension.

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

### Theorem 2.2. Equality characterizes simplices among polytopes

For a full-dimensional polytope $K$ of dimension $d\ge1$,

$$\boxed{a(K)=\frac1{d+1}\quad\Longleftrightarrow\quad K\text{ is a simplex}.}$$

**Proof.** Translate an interior point to zero, so every $b_i>0$. For a $d$-set $J$, let

$$E_J=\sum_{i\notin J}|\det(w_j:j\in J;w_i)|-dv|\det(u_j:j\in J)|,
\qquad w_i=(u_i,b_i).$$

The argument in Lemma 2.1 gives $E_J\ge0$ for every $J$, and

$$\sum_{|J|=d}E_J=(d+1)S-dvP.$$

Consequently equality in the lemma forces every $E_J=0$. For a horizontally independent $J$, it also forces every residual $b_i-\langle u_i,x_J\rangle$ to be nonnegative: their sum is $dv>0$, and equality in the triangle inequality forbids a negative summand. Thus $x_J\in K$.

There is a minimal positive dependence

$$\sum_{i\in I}\lambda_i u_i=0,\qquad \lambda_i>0,$$

on a set $I$ of size $k\le d+1$, because zero lies in the convex hull of the normals and Caratheodory's theorem permits at most $d+1$ terms. This instance of Caratheodory can also be obtained by repeatedly perturbing a nonnegative dependence within its nullspace until one coefficient vanishes. Minimality implies that the horizontal rank on $I$ is $k-1$: otherwise an independent perturbation of the dependence would remove another positive coefficient. Its nullspace is one-dimensional. Since $\sum_{i\in I}\lambda_i b_i>0$, the lifted vectors $(w_i)_{i\in I}$ are independent.

If $k\le d$, extend these lifted vectors to a basis of $\mathbb R^{d+1}$ chosen from all the $w_i$, which span that space. Remove one vector outside $I$ to obtain a $d$-set $J$ containing $I$. Its horizontal determinant is zero, but restoring the removed vector gives a nonzero lifted determinant. Thus $E_J>0$, a contradiction. Hence $k=d+1$.

The $d+1$ halfspaces $\langle u_i,x\rangle\le b_i$, $i\in I$, bound a simplex $\Delta$. To verify this explicitly, every $d$-subset of these normals is independent. Let $v_i$ be the intersection of all their hyperplanes except the $i$th. With $B=\sum_{i\in I}\lambda_i b_i>0$, the residuals satisfy

$$\lambda_j(b_j-\langle u_j,v_i\rangle)=B\,\mathbf1_{i=j}.$$

For any point in the intersection of the halfspaces, its nonnegative barycentric coordinates are $\lambda_i(b_i-\langle u_i,x\rangle)/B$; they sum to one, and independence shows they express $x$ as their combination of the $v_i$. Thus the intersection is exactly $\operatorname{conv}(v_i:i\in I)$. Every $v_i$ is an $x_J$ for a horizontally independent $J$, hence lies in $K$ by the equality argument above. Since the defining halfspaces already give $K\subseteq\Delta$, we obtain $K=\Delta$. The converse is Lemma 2.1. $\square$

This equality classification is asserted here for polytopes only. Continuity transfers the inequality to arbitrary convex bodies, but by itself does not transfer this equality classification.

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


## 8. Sharp finite optimization in the product-join closure

Let $\mathcal C_0$ consist of a point. Recursively let $\mathcal C_n$ consist of affine images of all joins $A*B$, where $A\in\mathcal C_r$, $B\in\mathcal C_s$, $r+s+1=n$, and all Cartesian products $A\times B$, where $r,s\ge1$ and $r+s=n$. This is a class of affine shapes of polytopes; a finite expression is required. Products with points do not add shapes and are omitted. Both children of every permitted operation have strictly smaller dimension. Thus the recursion is well founded. In particular all simplices, simplex products and their iterated pyramids belong to this class.

### Theorem 8.1. The first failure in the full recursive class

For $1\le n\le13$,

$$\max_{K\in\mathcal C_n}R(K)=c_n.$$

In dimension fourteen,

$$\boxed{\max_{K\in\mathcal C_{14}}R(K)=\frac{385}{384}c_{14}.}$$

The maximizing value in the second statement is attained by the explicit body in Section 6. This theorem is restricted to $\mathcal C_n$, not all convex bodies. It does not assert uniqueness of the maximizing affine shape.

**Proof and finite certificate interface.** Work with the coordinates

$$(x,y)=(R(K),a(K)R(K)).$$

The second coordinate is not the volume of $K$. For positive dimensions $r,s$, the product operation becomes

$$B_{r,s}^{\times}((x,y),(x',y'))=
\left(xx',\frac{r yx'+s xy'}{r+s}\right).$$

For $r,s\ge0$, writing $n=r+s+1$ and $C=g(n)/(g(r)g(s))$, the join operation becomes

$$B_{r,s}^{*}((x,y),(x',y'))=C(xy'+yx',yy').$$

The initial point has coordinates $(1,1)$. Each operation is bilinear with nonnegative coefficients and is coordinatewise monotone on the nonnegative quadrant.

For each $0\le n\le14$ the supplied certificate specifies a finite list $E_n$ of rational pairs, each supplied with a recipe in the lower-dimensional lists. Let $H_n$ be the nonnegative downward closure of $\operatorname{conv}(E_n)$: a vector belongs to $H_n$ when it is nonnegative and is coordinatewise bounded by a convex combination of the listed vectors. The independent checker verifies the following finite statements:

1. $E_0=\{(1,1)\}$, and every pair in every $E_n$ is exactly attained by its recorded recipe.
2. For every admissible **ordered** dimension split, every image of a pair of listed vertices under the corresponding product or join lies in $H_n$.
3. The largest first coordinate in $E_n$ is $c_n$ for $1\le n\le13$ and $(385/384)c_{14}$ for $n=14$.

These finite assertions imply the theorem without an untested pruning assumption. Indeed, by induction every attainable input is bounded by a convex combination of listed vertices. Positivity and bilinearity bound its output by a convex combination of all vertex-pair outputs. Assertion 2 and convex downward closure place that output in $H_n$. Assertion 1 gives the matching lower bound. The lists are therefore exact certificates for this finite range, not merely a heuristic collection of good constructions.

Here is the explicit arithmetic test for membership, to make the checking logic transparent. The certificate lists vertices $(x_i,y_i)$ in strictly increasing $x_i$ and strictly decreasing $y_i$, with a strictly concave upper polygonal chain. A nonnegative pair $(x,y)$ lies in $H_n$ exactly when

$$x\le x_{\mathrm{last}},\qquad y\le y_{\mathrm{first}},$$

and, for every consecutive pair of vertices,

$$(y-y_i)(x_{i+1}-x_i)\le(y_{i+1}-y_i)(x-x_i).$$

The checker verifies the sorting, concavity, every one of these inequalities, and every recipe by rational arithmetic. With a single listed vertex the two coordinate bounds suffice. The vertex counts in dimensions zero through fourteen are

$$1,1,1,2,2,2,2,3,2,3,3,5,5,7,7.$$

The complete rational vertices and recipes, not rounded decimal summaries, are in `certificates/exact.json`. The source `code/check.py` does not import the certificate producer or reuse its convex-hull construction. Its positive-bilinear closure test is justified above. This completes the finite arithmetic part of the proof. $\square$

## 9. A self-similar family with a certified asymptotic rate

Define

$$K_0=T_5,\qquad K_{j+1}=(K_j\times K_j)*(K_j\times K_j),$$

and write $d_j=\dim K_j$, $R_j=R(K_j)$ and $a_j=a(K_j)$. These are explicit polytopes in $\mathcal C_{d_j}$, specified by finite recursive recipes. The calculus proves

$$d_j=\frac{16\cdot4^j-1}{3},\qquad a_j=\frac1{6\cdot2^j},\qquad R_0=\frac{625}{4},$$

$$R_{j+1}=R_j^4 D_j,\qquad
D_j=2a_j\frac{g(4d_j+1)}{g(2d_j)^2}.$$

### Lemma 9.1. Uniform exact tail control

For every $j\ge0$,

$$3<D_j<6.$$

**Proof.** The two elementary central-binomial bounds are

$$\frac{4^q}{2\sqrt q}\le\binom{2q}{q}\le\frac{4^q}{\sqrt{3q+1}}
\qquad(q\ge1).$$

The right inequality was proved in Section 7. For the left one, equality holds at $q=1$. Dividing consecutive normalized central binomial coefficients shows that the induction step is equivalent to

$$\left(\frac{2q+1}{2q+2}\right)^2\ge\frac q{q+1},$$

which follows on multiplying by $4(q+1)^2$, since $(2q+1)^2-4q(q+1)=1$.

Put $q=2d_j$. As before,

$$\frac{g(2q+1)}{g(q)^2}
=\frac{4^q}{\binom{2q}{q}}
 \left(1+\frac1{2q}\right)^{2q}.$$

The last factor is strictly between $2$ and $e$. Its lower bound follows from the constant and linear terms of the binomial expansion, and its upper bound from $\log(1+x)<x$. Therefore

$$D_j>4a_j\sqrt{6d_j+1}
 =\frac23\sqrt{32-4^{-j}}\ge\frac23\sqrt{31}>3,$$

$$D_j<4e a_j\sqrt{2d_j}
 <\frac{2e}{3}\sqrt{\frac{32}{3}}<6.$$

For the last strict inequality it suffices to use $e<11/4$ and square positive quantities. One elementary proof of this bound is to sum $1/k!$ through $k=3$, and bound the remaining tail by $\frac1{24}\sum_{m\ge0}5^{-m}=5/96$; the resulting $261/96$ is less than $11/4$. $\square$

### Theorem 9.2. Strict growth and certified limit

The sequence $R_j^{1/d_j}$ is strictly increasing and has a limit $\Lambda$ satisfying

$$\boxed{2.8534<\Lambda<2.8535.}$$

More generally, every level gives certified analytic enclosures

$$\boxed{(3R_j^3)^{1/(3d_j+1)}<\Lambda<(6R_j^3)^{1/(3d_j+1)}.}$$

**Proof.** Iterating $R_{j+1}<6R_j^4$ gives

$$R_j^3\le R_0^{3\cdot4^j}6^{4^j-1}
 =\frac{(6R_0^3)^{4^j}}6
 <\frac{3^{16\cdot4^j}}6
 <3^{16\cdot4^j-1}=3^{3d_j}.$$

The first inequality is an equality at $j=0$ and is strict afterward; the displayed strict conclusions hold in either case. The finite inequality used here is $6(625/4)^3<3^{16}$, verified by clearing denominators. Consequently $R_j^{1/d_j}<3$. Since $D_j>3>R_j^{1/d_j}$ and $d_{j+1}=4d_j+1$, the recurrence gives

$$R_{j+1}=R_j^4D_j>\left(R_j^{1/d_j}\right)^{4d_j+1}.$$

This proves strict increase; the bound by three proves convergence. Iterating the logarithmic recurrence from level $j$, dividing by the corresponding dimension and taking the limit yields the absolutely convergent series

$$\log\Lambda=
\frac{\log R_j+\sum_{t=0}^{\infty}4^{-t-1}\log D_{j+t}}
     {d_j+1/3}.$$

The bounds in Lemma 9.1 and $\sum_{t\ge0}4^{-t-1}=1/3$ imply the stated enclosures.

For the numerical rational endpoints we take $j=6$, for which $d_6=21845$ and $3d_6+1=65536$. The certificate stores the **entire exact rational number** $R_6$, obtained from the specified recurrence. The independent checker reconstructs it using the different formula involving central binomial coefficients, and verifies the two integer inequalities obtained by clearing positive denominators in

$$\left(\frac{14267}{5000}\right)^{65536}<3R_6^3,
\qquad 6R_6^3<\left(\frac{5707}{2000}\right)^{65536}.$$

Combined with the infinite tail enclosure, these prove $2.8534<\Lambda<2.8535$. No floating-point evaluation of a logarithm or of an infinite product is used in this certification. $\square$

### Corollary 9.3. An exponential improvement in all sufficiently large dimensions

There is an explicitly defined $L_n\in\mathcal C_n$ for every positive integer $n$ such that

$$\lim_{n\to\infty}R(L_n)^{1/n}=\Lambda.$$

If $M_n$ is the maximum over products of simplices in entry 005 v1.1, then for all sufficiently large $n$,

$$\boxed{R(L_n)>\left(\frac{203}{200}\right)^n M_n.}$$

This is an eventual inequality; no explicit starting dimension is claimed.

**Proof.** For $n\ge25$, choose the largest $j$ such that $d_j\le\sqrt n$. Put $k=\lfloor n/d_j\rfloor$ and $r=n-kd_j$. Use

$$L_n=K_j^k\times T_r,$$

omitting the residual factor when $r=0$. For $n<25$ use a simplex. Then $j\to\infty$, $0\le r<d_j\le\sqrt n$, and $kd_j/n\to1$. The product identity yields

$$\frac{\log R(L_n)}n
 =\frac{kd_j}{n}\frac{\log R_j}{d_j}+\frac{\log c_r}n.$$

The residual term is zero at $r=0$; otherwise $\log c_r=O(r+\log(r+1))$, for example by $r!\ge(r/e)^r$. That factorial bound follows by comparing $\sum_{i=1}^r\log i$ with $\int_1^r\log t\,dt$. Thus the residual term tends to zero, proving the limit.

The result in v1.1 gives $M_n^{1/n}\to\rho=c_{13}^{1/13}$. Two more exact inequalities, independently checked in the supplied code, are

$$c_{13}<\left(\frac{561993}{200000}\right)^{13},\qquad
\frac{14267}{5000}>\frac{203}{200}\frac{561993}{200000}.$$

Together with Theorem 9.2 these imply $\Lambda>(203/200)\rho$, and convergence gives the eventual comparison. $\square$

## 10. Reproduction, independent checks, and remaining scope

From this directory run:

```sh
python3 code/generate.py --output certificates/exact.json
python3 code/check.py certificates/exact.json --self-test --report results/check.json
python3 -O code/check.py certificates/exact.json --self-test --report results/optimized_check.json
```

Python 3.10 or newer and the standard library suffice. `Fraction` and arbitrary-precision integers are used throughout. The large stored integers require disabling Python's integer-string conversion limit when that limit is present; both scripts do this explicitly. This does not change the arithmetic semantics. The producer fixes all mathematical inputs; the independent checker imports neither the producer nor its convex-hull algorithm. Its exceptions remain active under `python -O`.

In addition to the certificate tests justified in Sections 8 and 9, the checker computes actual facet normals and maximal minors for fourteen low-dimensional product/join/pyramid tests. It then constructs the rational facet data for $\mathcal P^6(T_4\times T_4)$ and sums all $\binom{16}{14}=120$ horizontal and $\binom{16}{15}=16$ lifted maximal minors by fraction-free elimination. Each exact division is checked. The resulting rational facet data, projection volume, lifted volume and invariants are included in the replay report. Four deliberately corrupted certificates must be rejected.

The numerical verification is independent in the sense of separate algorithms and exact replayable arithmetic. It is **not** an external human review, a proof-assistant formalization, or an independent validation of every infinite analytic step. The affine geometry, continuity passage, positive-bilinear hull argument and infinite tail argument have complete written proofs above and remain subject to mathematical scrutiny.

The principal unresolved extremal question is the optimal all-dimensional asymptotic rate in $\mathcal C$, or among all convex bodies. Theorem 7.1 rules out attainment by any single finite-dimensional repeated block but does not identify the supremum. Theorem 9.2 certifies one explicit family's rate, not its optimality. A dimension-uniform upper envelope preserved by **both** product and join would be needed to close the corresponding upper-bound problem; the finite hulls through fourteen do not provide one. The unrestricted fixed-dimensional projection-volume maximum, including dimensions four through eight, is not settled here.

## Provenance and verification scope

The product identity and simplex value are inherited from classical projection-body geometry and were rederived in OpenAI, *A product counterexample to the simplex maximum for projection-body volume*, 24 September 2026, family 088, pinned upstream commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Entry 005 v1.1 supplies the exact optimization over simplex products. The lifted invariant, full join calculus, amplification statements, and explicit pyramid extension in this note are the additional results being recorded here, subject to literature comparison rather than a priority claim.

The proofs above use facet geometry, determinant identities, ordinary volume continuity, and elementary real analysis. No floating-point optimization, SAT/SMT answer, unverified solver assumption, or private transcript is a proof dependency. This source disclosure does not claim external independent review or complete formalization.

For the post-disclosure comparison with Brannen (1996), Lutwak--Yang--Zhang (2001), Saroglou (2011), and Feng--Hu--Liu--Xu (2026), see [RESEARCH_LOG.md](RESEARCH_LOG.md). The existing dimension-nine counterexamples and earlier cone studies are explicitly acknowledged there. Full bibliographic novelty has not been established.
