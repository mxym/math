# A strict infinite hierarchy of product depth, with an exact second-level projection-body spectrum

**Research note — 8 October 2026.** Continuation of manuscript 005. The basic affine-geometric product/join calculus and two universal two-layer block inequalities are explicitly imported from earlier public 005 manuscripts. The depth hierarchy and second-depth classification below are new deductions and calculations within this research sequence. Prepared with AI assistance; not an external human review, whole-paper Lean formalization or world-first priority certification.

## Abstract

We introduce *product depth* as the largest number of Cartesian-product nodes along a root-to-leaf path in a point-generated affine product/join expression. Let \(\mathcal C^{[k]}\) denote all bodies of product depth at most \(k\). We prove a **strict, effectively computable infinite hierarchy theorem**: in every finite level \(k\), the exact spectral optimum \(\lambda_k=\sup_{K\in\mathcal C^{[k]}}(a(K)R(K)/g(d))^{1/(d+1)}\) is attained by a finite polytope, while \(1=\lambda_0<\lambda_1<\lambda_2<\cdots\nearrow\lambda_*\), where \(\lambda_*\) is the full product/join supremum. Each fixed-depth class has an exact asymptotic projection-volume root rate \(e\lambda_k\), so **no bounded product-depth grammar has the full class's asymptotic optimum**. The proof combines a uniform sublinear product-gain bound with an explicit central-binomial amplification operator, including a positive **dimension-only rational lower bound on every spectral increase**. It also yields a provably terminating exact-arithmetic procedure to compute the optimal algebraic spectral constant at *any fixed product depth*; it requires neither a numerical extrapolation nor knowledge of the unknown final constant.

We also **solve completely the entire second level** (arbitrary dimensions, nonhomogeneous operands and joins). Its unique optimal *primitive product state* is the Cartesian square of a join of two copies of \(T_5\times T_5\); it has dimension 42 and exact rational \(Q=257554342358885086515/36893488147419103232\). Thus
\[
 \boxed{\lambda_1=(189/128)^{1/11},\qquad
        \lambda_2=(257554342358885086515/36893488147419103232)^{1/43}.}
\]
This is not a classification restricted to balanced recursive or finite-dimensional seeds: the second-level upper bound covers **every** allowed two-product-depth expression in **every dimension**. The proof uses two analytic infinite-parameter tails and an independent exact-rational replay of 2,770,504 finite product candidates over 1,214 dimension splits. A 170-dimensional third-depth witness is certified strictly stronger. The unrestricted \(\lambda_*\) remains undetermined.

## 1. Construction grammars and geometric state

For a full-dimensional convex polytope \(K\subset\mathbb R^d\), let \(\Pi K\) denote its projection body. Define
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!}.
\]
The affine-invariant parameter \(a(K)>0\) is defined by normalized lifted-facet determinant sums in [entry 005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md). Set
\[
 D(K)=d+1,\quad H(K)=1/a(K),\quad
 Q(K)=\frac{a(K)R(K)}{g(d)},\quad
 \lambda(K)=Q(K)^{1/D(K)}.
 \tag{1.1}
\]
For the formal zero-dimensional point \(\mathbf 0\) use \((D,H,Q)=(1,1,1)\). For positive-dimensional members of the point-generated product/join class, the inherited geometric estimates imply
\[
 \boxed{2\le H(K)\le D(K),\qquad Q(K)>0.}
 \tag{1.2}
\]
The exact inherited **join rule** is
\[
 (D,H,Q)(A*B)=\bigl(D_A+D_B,H_A+H_B,Q_AQ_B\bigr).
 \tag{1.3}
\]
For nontrivial Cartesian products with \(r=\dim A\ge1\), \(s=\dim B\ge1\), \(n=r+s\), \((H,Q)(A)=(h,u)\), \((H,Q)(B)=(j,v)\), the product rule is
\[
 \boxed{\begin{aligned}
 D(A\times B)&=n+1,\\
 H(A\times B)&=\frac n{r/h+s/j},\\
 Q(A\times B)&=uv\,\frac{g(r)g(s)}{g(n)}\frac{sh+rj}{n}.
 \end{aligned}}
 \tag{1.4}
\]
These formulas are rederived and proved in 005 v2; they are **mathematical inputs** here. All affine maps allowed in the grammar are invertible on full affine hulls. Products with points are redundant and may be removed, and joins are understood as binary affine joins (arbitrary finite joins are obtained by associativity).

Define the **product depth** recursively: a point has depth zero; a join has the maximum depth of its two children; a product of two positive-dimensional bodies has one plus the maximum depth of its two children. For a body \(K\) admitting multiple expressions, \(K\in\mathcal C^{[k]}\) when it admits *some* expression of depth at most \(k\). Put \(\mathcal C^{[k]}_d=\{K\in\mathcal C^{[k]}:\dim K=d\}\). For \(k=0\) these are precisely the simplices (affine joins of points). The class \(\mathcal C^{[1]}\) consists exactly of **joins of points and products \(T_p\times T_q\)** with \(p,q\ge1\): every nontrivial product is immediately below the join layer. This is the two-layer class \(\mathcal B\) analyzed in the earlier [sharp block-spectrum paper](../two-layer-projection-depth-separation/paper.md).

Every \(\mathcal C^{[k]}\) contains the point and is join closed. Their union over all finite \(k\) equals the full class \(\mathcal C\), since every finite expression tree has finite depth. Define the normalized logarithmic spectral maxima
\[
 q_k=\sup_{K\in\mathcal C^{[k]},\ d\ge1}\frac{\log Q(K)}{d+1},
 \qquad \lambda_k=e^{q_k},\qquad q_*=\sup_{K\in\mathcal C}\frac{\log Q(K)}{D(K)}.
 \tag{1.5}
\]
These suprema are finite by the independent uniform Bellman ceiling already proved for the full point-generated class; Section 3 also supplies a self-contained finite-depth bound. The full \(q_*\) is known finite but **not** determined exactly.

## 2. Main structural theorem: a strict hierarchy at every depth

**Theorem A (strict depth hierarchy and finite attainment).** For every integer \(k\ge0\), \(q_k\) is attained by a finite positive-dimensional polytope of product depth exactly \(k\). Moreover, there is a provably terminating algorithm using exact rational state arithmetic and certified logarithm intervals that determines the algebraic number \(\lambda_k=e^{q_k}\) at every fixed \(k\). The strict inequalities are
\[
 \boxed{0=q_0<q_1<q_2<\cdots<q_k<q_{k+1}<\cdots\nearrow q_*<\infty.}
 \tag{2.1}
\]
In particular every fixed finite product depth has a **strictly smaller** spectral supremum than the unrestricted point-generated class. Each \(\lambda_k\) is **algebraic**, because its maximizing \(Q\) is a rational number and its maximizing \(D\) is a positive integer; the result gives an exact algebraic approximation hierarchy, even though the limit may not be explicitly known.

Moreover, letting
\[
 \Gamma_k:=\lim_{d\to\infty}\sup_{K\in\mathcal C^{[k]}_d}R(K)^{1/d},
 \qquad
 \Gamma_{\mathcal C}:=\lim_{d\to\infty}\sup_{K\in\mathcal C_d}R(K)^{1/d},
\]
we have the exact identities
\[
 \boxed{\Gamma_k=e\lambda_k,\qquad
 \Gamma_0<\Gamma_1<\Gamma_2<\cdots\nearrow\Gamma_{\mathcal C}.}
 \tag{2.2}
\]
In fact there is a **strict exponential penalty** for restricting to any fixed depth. Because both asymptotic limits exist and are positive,
\[
 \boxed{\lim_{d\to\infty}
 \left(\frac{\max_{K\in\mathcal C_d}R(K)}
 {\max_{K\in\mathcal C^{[k]}_d}R(K)}\right)^{1/d}
 =\frac{\lambda_*}{\lambda_k}
 \ge\frac{\lambda_{k+1}}{\lambda_k}>1.}
 \tag{2.3}
\]
The rightmost strict algebraic lower factor \(\lambda_{k+1}/\lambda_k\) can itself be **computed exactly** by the effective recursion below. Thus an unrestricted tree can beat every fixed-depth grammar by a dimension-exponential factor, not merely by an additive asymptotic loss. In particular, any sequence of point-generated expression trees whose normalized root volumes are asymptotically optimal for the full \(\mathcal C\)-growth rate must have unbounded product depth. This is a global structural obstruction, not a finite-parameter observation. An explicit improvement operator in the proof increases the product depth of *any* finite maximizer while strictly increasing its spectral value.

The proof is in Sections 3–4. We then identify \(q_1\) (inherited) and obtain a new complete exact expression for \(q_2\) in Sections 5–8.

## 3. A uniform sublinear product-gain lemma

For \(n\ge2\), define the positive elementary bound
\[
 U(n)=\frac{1+n/2}{1-1/(12n)}\sqrt{\frac{2}{\pi_0 n}},
 \qquad \pi_0=333/106<\pi.
 \tag{3.1}
\]
Its coefficients and the strict inequality \(\pi_0<\pi\) are independently certified by Machin's arctangent formula with rational Taylor intervals in the accompanying checker.

**Lemma 3.1 (universal product multiplier bound).** For any positive-dimensional \(A,B\) of dimensions \(r,s\) in the point-generated class, their product multiplier \(C x\) from (1.4) obeys
\[
 \boxed{\frac{g(r)g(s)}{g(r+s)}\frac{sH_A+rH_B}{r+s}<U(r+s).}
 \tag{3.2}
\]
In particular \(\log U(n)=O(\log n)=o(n)\).

**Proof.** By (1.2), \(H_A\le r+1\), \(H_B\le s+1\). Thus
\[
 \frac{sH_A+rH_B}{n}\le1+\frac{2rs}{n}.
\]
The right side multiplied by \(g(r)g(s)/g(n)\) is exactly the \(Q\)-value of the Cartesian product of an \(r\)-simplex and an \(s\)-simplex. Let \(t=rs/n\). We have \(1/2\le t\le n/4\). The classical two-sided Robbins bounds for \(m!\), with their positive remainder corrections omitted on the favorable side, imply
\[
 \frac{g(r)g(s)}{g(n)}
 <e^{1/(12n)}\sqrt{\frac{n}{2\pi rs}}.
\]
The function \((1+2t)/\sqrt t\) is nondecreasing for \(t\ge1/2\), because its derivative is \((2t-1)/(2t^{3/2})\ge0\). Consequently
\[
 Cx < e^{1/(12n)}(1+n/2)\sqrt{\frac2{\pi n}}
 <U(n),
\]
using \(e^y<(1-y)^{-1}\) for \(0<y<1\) and \(\pi>\pi_0\). The formula for \(U\) immediately gives \(\log U(n)=O(\log n)\). \(\square\)

**Lemma 3.2 (depth recursion and a finite-attainment criterion).** For every \(k\ge1\),
\[
 \boxed{q_k=\max\left\{q_{k-1},\quad
 \sup_{\substack{r,s\ge1\\A\in\mathcal C^{[k-1]}_r\\B\in\mathcal C^{[k-1]}_s}}
 \frac{\log Q(A\times B)}{r+s+1}\right\}.}
 \tag{3.3}
\]
Furthermore, for any \(r+s=n\),
\[
 \frac{\log Q(A\times B)}{n+1}
 <q_{k-1}+\frac{q_{k-1}+\log U(n)}{n+1}.
 \tag{3.4}
\]
If \(q_k>q_{k-1}\), then \(q_k\) is attained by a **finite** body whose root operation is a nontrivial product of depth-\((k-1)\) children.

**Proof.** The join law (1.3) implies
\[
 \frac{\log Q(A*B)}{D_A+D_B}
 =\frac{D_A}{D_A+D_B}\frac{\log Q(A)}{D_A}
 +\frac{D_B}{D_A+D_B}\frac{\log Q(B)}{D_B}.
\]
Thus joins never create a spectral value larger than that of a constituent. Every tree of depth at most \(k\) decomposes into outer joins of either depth-\((k-1)\) bodies, points or **products of two depth-\((k-1)\) bodies**, which proves (3.3). For the product of two such bodies, \(\log Q(A)+\log Q(B)\le q_{k-1}(r+s+2)\). Add (3.2) and divide by \(n+1\) to obtain (3.4).

Since \(\log U(n)=o(n)\), the right side of (3.4) converges to \(q_{k-1}\) uniformly over all product splits and bodies as \(n\to\infty\). If \(q_k>q_{k-1}\), choose a threshold strictly between them. All products beating this threshold have output dimensions bounded by a fixed integer. In each fixed dimension only finitely many affine-equivalence operation-tree types occur. More precisely, after removing neutral products with the point, **the number of join nodes in a binary construction tree equals its ambient dimension**: this follows immediately by induction from \(d(A*B)=d(A)+d(B)+1\), \(d(A\times B)=d(A)+d(B)\), and \(d(\mathbf0)=0\). Every genuine product has two children of positive dimension, so induction also bounds its number of product nodes by \(d-1\). Thus a dimension-\(d\) normalized tree has at most \(2d-1\) internal operation nodes, yielding only finitely many tree shapes and rational \((D,H,Q)\) states up to that dimension (affine changes leave the state invariant). Therefore the strict upper supremum is a maximum at some finite product state, not merely an unattained limiting value. \(\square\)

The last argument also proves all finite-depth \(q_k\) are finite inductively from \(q_0=0\), without importing the full-class Bellman bound: the supremum of the right side of (3.4) over positive integer \(n\) is finite.

## 4. Explicit strict spectral amplification and proof of Theorem A

**Lemma 4.1 (central-binomial spectral ascent).** Suppose \(K\) has positive dimension \(d\), state \((D,H,Q)\) and spectral value \(\lambda=Q^{1/D}\ge1\). Set \(m=D\), form the \(m\)-fold affine join \(J=K^{*m}\), and then the Cartesian square \(L=J\times J\). Then
\[
 \boxed{\lambda(L)>\lambda(K),\qquad
 \operatorname{productdepth}(L)\le\operatorname{productdepth}(K)+1.}
 \tag{4.1}
\]
This construction is explicit: it uses **exactly \(D\)** join copies and one additional product operation, requiring no limiting choice of an unspecified sufficiently large integer.

**Proof.** For point-generated positive-dimensional bodies, (1.2) gives \(H\ge2\) and \(D\ge2\). Put \(N=mD-1=D^2-1\). By the exact join law, \((D,H,Q)(J)=(mD,mH,Q^m)\). Then (1.4) gives
\[
 Q(L)=Q^{2m}\,(mH)\frac{g(N)^2}{g(2N)}
 =Q^{2m}\,(mH)\frac{\binom{2N}{N}}{4^N}.
 \tag{4.2}
\]
Since \(D(L)=2mD-1\), the strict desired comparison is equivalent to
\[
 \boxed{\lambda\,(mH)\frac{\binom{2N}{N}}{4^N}>1.}
 \tag{4.3}
\]
For every positive integer \(N\),
\[
 \frac{\binom{2N}{N}}{4^N}\ge\frac1{2\sqrt N}.
 \tag{4.4}
\]
This follows by induction, with equality at \(N=1\): the ratio of consecutive left sides is \((2N+1)/(2N+2)\) and its square exceeds \(N/(N+1)\), because \((2N+1)^2-4N(N+1)=1\). Now \(m=D\), \(H\ge2\), \(\lambda\ge1\), so the left side of (4.3) is bounded below by
\[
 \frac{\lambda mH}{2\sqrt{mD-1}}
 \ge\frac D{\sqrt{D^2-1}}>1.
\]
Thus (4.3) holds strictly, proving (4.1). Joins preserve product depth and one top product raises it by at most one. \(\square\)

The same inequalities give an explicit **quantitative spectral gain** depending on the input dimension alone:
\[
 \begin{aligned}
 \log\lambda(L)-\log\lambda(K)
 &>\frac{1}{2(2D^2-1)}\log\frac{D^2}{D^2-1}\\
 &>\boxed{\frac{1}{2D^2(2D^2-1)}}.
 \end{aligned}
 \tag{4.4a}
\]
For the last strict bound use the elementary inequality \(\log(1+x)>x/(1+x)\) with \(x=1/(D^2-1)\). In particular if \(D_k\) is the augmented dimension of **any attained depth-\(k\) maximizer**, then
\[
 \boxed{q_{k+1}-q_k>\frac{1}{2D_k^2(2D_k^2-1)}.}
 \tag{4.4b}
\]
This is a closed positive lower gap certificate at *every* level, even when the next optimizer has not yet been enumerated.

**Proof of Theorem A.** At depth zero, every body is a simplex with \(Q=1\), so \(q_0=0\), attained by an interval. Suppose inductively \(q_k\) is attained by a positive-dimensional body \(K_k\). Since the class also contains simplices, \(q_k\ge0\) and therefore \(\lambda(K_k)=e^{q_k}\ge1\). Lemma 4.1 constructs a depth-\((k+1)\) body \(L\) with strictly larger spectral value, giving \(q_{k+1}>q_k\). Lemma 3.2 then gives **finite attainment** of \(q_{k+1}\). Since \(q_{k+1}>q_k\), an optimizer cannot have depth \(\le k\), so some finite maximizing tree has *exactly* product depth \(k+1\). This proves strictness and attainment for all \(k\).

For the asymptotic statement, any join-closed family containing the formal point satisfies the spectral reduction identity
\[
 \lim_{d\to\infty}\sup_{K\in\mathcal A_d}R(K)^{1/d}
 =e\sup_{K\in\mathcal A}Q(K)^{1/D(K)},
 \tag{4.5}
\]
proved in the [005 v2 spectral supplement](../../preprints/005-simplex-product-optimum/v2/ASYMPTOTIC_SPECTRAL_REDUCTION.md). For completeness, the upper bound follows from \(R(K)=g(d)H(K)Q(K)\), \(H(K)\le d+1\), and \(g(d)^{1/d}\to e\). The lower bound follows by joining copies of any fixed body \(K\), adding at most \(D(K)-1\) point factors to fill every dimension, and taking the root limit; joining preserves its per-\(D\) logarithmic \(Q\)-rate. Apply (4.5) to \(\mathcal A=\mathcal C^{[k]}\) to get \(\Gamma_k=e\lambda_k\). The full class is \(\bigcup_k\mathcal C^{[k]}\), hence \(q_*=\sup_k q_k\). The independently certified full-class Bellman ceiling shows \(q_*<\infty\), so \(q_k\nearrow q_*\) strictly and (2.2) follows. \(\square\)

### 4.2. Effective finite cutoffs: exact computability at every fixed depth

The preceding proof gives more than abstract finite attainment. Given an exact maximizing state \((D,H,Q)\) at product depth \(k-1\), it **constructs** a finite exact search bound for the next depth level, using only exact fractions and certified real-logarithm intervals.

First form the explicit amplifier \(L=(K^{*D})\times(K^{*D})\) from Lemma 4.1. Its state is a rational triple and its spectral value strictly exceeds \(\lambda(K)=Q^{1/D}\). The quantitative estimate (4.4a) lets us choose an **explicit rational cutoff gap without approximating any algebraic root**:
\[
 \boxed{\delta=\frac{1}{8D^2(2D^2-1)}>0,\qquad
  2\delta<\frac{\log Q(L)}{D(L)}-\frac{\log Q}{D}.}
 \tag{4.6}
\]
This choice depends **only on the known integer dimension \(D\)** of the previously certified optimizer. It eliminates a potentially delicate numerical gap-detection step and supplies a rational quantitative certificate for strict depth ascent.

Next find a positive integer \(N\) such that
\[
 \delta>\frac1{2N},\qquad
 \delta(N+1)>q_{k-1}+\log U(N).
 \tag{4.7}
\]
Both comparisons can again be certified by rational logarithm intervals. The search is guaranteed to terminate, since \(\log U(N)=O(\log N)\) whereas \(\delta N\) grows linearly. In fact, for real \(x\ge N\), direct differentiation of \(U\) gives
\[
 \frac{d}{dx}\log U(x)
 =\frac1{x+2}-\frac1{2x}-\frac1{x(12x-1)}
 <\frac1{2x}\le\frac1{2N}<\delta.
\]
Thus the function \(\delta(x+1)-q_{k-1}-\log U(x)\) is increasing on \([N,\infty)\), so (4.7) implies
\[
 \frac{q_{k-1}+\log U(n)}{n+1}<\delta
 \qquad\text{for all integers }n\ge N.
\]
By Lemma 3.2, **every** depth-\(k\) primitive product of dimension \(n\ge N\) has logarithmic spectral rate less than \(q_{k-1}+\delta\). But the explicit amplifier already has rate greater than \(q_{k-1}+2\delta\). Therefore no such large product can maximize \(q_k\).

It suffices to enumerate all nontrivial finite operation trees of **dimension less than \(N\)** and depth at most \(k\), reduce their \((D,H,Q)\) states by exact rational arithmetic, and compare their algebraic roots \(Q^{1/D}\) using only cross-powers of rationals. Every ambient dimension has finitely many reduced tree types by Lemma 3.2, so this final search is finite. The resulting winner \(K_k\) and its exact algebraic rate form the input for the next induction stage.

**Corollary 4.2 (recursive exact optimization).** For every fixed finite depth \(k\), \(\lambda_k\) is an **attained, exactly computable algebraic number**. A certificate of its exact value consists of rational \((D,H,Q)\) states for all needed finite trees, exact integer-power comparisons, the small-depth predecessor certificate, and a rigorous logarithmic-tail cutoff (4.7). No quantitative runtime bound is asserted; the worst-case finite cutoff may be extremely large. This algorithm does **not** compute the unknown infinite-depth limit \(\lambda_*\).

Since \(q_k\) is strictly increasing and all \(Q\)-states at any bounded dimension belong to a finite set, the dimension of *any* sequence of exact depth-\(k\) maximizing bodies necessarily tends to infinity as \(k\to\infty\). More specifically, the join-count argument in Lemma 3.2 bounds the number of product nodes in a dimension-\(d\) normalized tree by \(d-1\). Hence every optimizer of exact product depth \(k\) has the explicit ambient dimension lower bound \(d\ge k+1\).

## 5. Exact spectral result at product depth one and two

The [sharp two-layer block-spectrum theorem](../two-layer-projection-depth-separation/paper.md) proves, for every \(K\in\mathcal C^{[1]}\),
\[
 \boxed{\log Q(K)\le A D(K),\qquad
 \log Q(K)\le B(D(K)-H(K)),}
 \tag{5.1}
\]
where
\[
 Q_5=189/128,\quad Q_4=175/128,\qquad
 A=\frac1{11}\log Q_5,\quad B=\frac14\log Q_4.
 \tag{5.2}
\]
Both constants are sharp for **different** blocks: the first at \(T_5\times T_5\), the second at \(T_4\times T_4\). In particular
\[
 \boxed{q_1=A,\qquad \lambda_1=Q_5^{1/11}.}
 \tag{5.3}
\]
These are **imported**, fully stated results, not new claims of this paper.

Let
\[
 X=(T_5\times T_5)*(T_5\times T_5),\qquad P=X\times X.
 \tag{5.4}
\]
The state of \(X\) is \((D,H,Q)=(22,12,Q_5^2)\); the state of its Cartesian square \(P\) is
\[
 D(P)=43,\quad d(P)=42,\quad H(P)=12,\qquad
 Q(P)=12Q_5^4\frac{g(21)^2}{g(42)}
 =\boxed{\frac{257554342358885086515}{36893488147419103232}}.
 \tag{5.5}
\]

**Theorem B (unique optimal product state at depth two).** For **every** finite point-generated product/join expression of product depth at most two, in **any positive dimension**, one has
\[
 \boxed{\frac{\log Q(K)}{D(K)}\le\frac1{43}\log Q(P).}
 \tag{5.6}
\]
The inequality is sharp for \(K=P\), and any affine join of copies of \(P\) preserves the same per-\(D\) spectral rate. Within the complete, rational-state product search underlying the theorem, the **only primitive product** realizing equality has factor dimensions \(r=s=21\), each factor carrying the state \((H,Q)=(12,Q_5^2)\). This is an invariant-state equality description, *not* a classification of all possible geometric or affine equality representatives.

Consequently, for the entire depth-two class and **all dimensions simultaneously**,
\[
 \boxed{q_2=\frac1{43}\log\frac{257554342358885086515}{36893488147419103232},\quad
 \Gamma_2=e\left(\frac{257554342358885086515}{36893488147419103232}\right)^{1/43}.}
 \tag{5.7}
\]
The exact rational checker also verifies \(Q(P)^{11}>Q_5^{43}\), exhibiting the strict depth-one/two gap without floating-point evidence.

The proof of the **unbounded** second-level classification occupies Sections 6–8. The certificate's finite check is only one of three exhaustive parameter regimes; neither a large finite window nor numerical optimization is identified with the full theorem.

## 6. Two analytic infinite tails for Theorem B

Put
\[
 q^\dagger=\frac1{43}\log Q(P)>A,
 \qquad t_*=1-\frac AB.
 \tag{6.1}
\]
The exact checker verifies
\[
 \boxed{\frac{27}{50}<t_*<\frac{11}{20},\qquad
 B>\frac{31}{400},\qquad
 q^\dagger-A>\frac1{126}.}
 \tag{6.2}
\]
The first bound is exactly equivalent to the integer inequalities \(Q_5^{200}<Q_4^{253}\) and \(Q_5^{80}>Q_4^{99}\); the last two use rational lower/upper intervals for natural logarithms. All these checked inequalities are *strict*.

For an input at depth one with \(D=r+1\), \(H=h\), (5.1) is equivalent to
\[
 \boxed{\log Q\le A(r+1)-B(h-t_*(r+1))_+,}
 \qquad x_+=\max\{x,0\}.
 \tag{6.3}
\]
This simple piecewise-linear envelope is the key to treating arbitrarily large parents, including unequal dimensions.

### Lemma 6.1 (both parents moderately large)

For \(12\le r\le s\) and \(n=r+s\ge63\), every product \(A_1\times A_2\) of two depth-one inputs of respective dimensions \(r,s\) satisfies
\[
 \boxed{\frac{\log Q(A_1\times A_2)}{n+1}<q^\dagger.}
 \tag{6.4}
\]

**Proof.** Write \(h=H(A_1)\), \(j=H(A_2)\), and \(h_0=t_*(r+1)\), \(j_0=t_*(s+1)\). These hinge values are at least two by (6.2). Apply (6.3) to both inputs and (1.4) to the product. Apart from the dimension-only factor \(g(r)g(s)/g(n)\), it remains to maximize
\[
 \log(sh+rj)-B(h-h_0)_+-B(j-j_0)_+
 \tag{6.5}
\]
over the positive state rectangle. If either \(h<h_0\) or \(j<j_0\), increasing that coordinate raises the expression with no penalty. Hence a maximum has \(h\ge h_0,j\ge j_0\). On this latter region, the partial derivatives are bounded by
\[
 \frac{s}{sh+rj}-B
 \le\frac1{t_*(2r+1)}-B
 \le\frac{2}{27}-B<0,
\]
and analogously \(r/(sh+rj)-B<0\), because \(r\ge12\). Therefore the global upper maximum occurs exactly at \(h=h_0,j=j_0\). This proves
\[
 \log Q(A_1\times A_2)
 \le A(n+2)+\log t_*+
 \log\left[\frac{g(r)g(s)}{g(n)}\left(1+\frac{2rs}{n}\right)\right]
 <A(n+2)+\log\left[\frac{11}{20}U(n)\right],
 \tag{6.6}
\]
where the last inequality uses Lemma 3.1 applied to simplex inputs.

Define for real \(x\ge63\)
\[
 F(x)=(q^\dagger-A)(x+1)-A-\log\left[\frac{11}{20}U(x)\right].
\]
Direct differentiation of the elementary function (3.1) gives
\[
 \frac{d}{dx}\log U(x)
 =\frac1{x+2}-\frac1{2x}-\frac1{x(12x-1)}<\frac1{2x}.
\]
By (6.2), \(F'(x)>q^\dagger-A-1/(2x)>0\) for every \(x\ge63\). The exact rational logarithm-interval checker verifies the remaining base inequality
\[
 \boxed{F(63)>0.}
 \tag{6.7}
\]
Thus (6.6) is strictly smaller than \(q^\dagger(n+1)\) for every integer \(n\ge63\), proving the lemma. \(\square\)

### Lemma 6.2 (one parent small, the other arbitrarily large)

For \(1\le r\le11\) and **every** \(s\ge80\), every product of depth-one inputs of dimensions \(r,s\) satisfies
\[
 \boxed{\frac{\log Q(A_1\times A_2)}{r+s+1}<q^\dagger.}
 \tag{6.8}
\]

**Proof.** Keep \(h=H(A_1)\in[2,r+1]\), \(j=H(A_2)\in[2,s+1]\). Let \(j_0=t_*(s+1)\). Below the hinge, the second input's logarithmic \(Q\)-bound (6.3) is constant while \(\log(sh+rj)\) increases with \(j\). Above the hinge, its derivative is at most
\[
 \frac{r}{sh+rj}-B\le\frac r{2s}-B
 \le\frac{11}{160}-\frac{31}{400}<0.
\]
Thus a valid upper bound is obtained by taking \(j=j_0\) and \(\log Q(A_2)=A(s+1)\). The first factor obeys \(\log Q(A_1)\le A(r+1)\) and \(h\le r+1\).

Robbins's two-sided estimates give, for \(n=r+s\),
\[
 \log\frac{g(s)}{g(n)}<-r+\frac12\log\left(1+\frac rs\right)+\frac1{12n}.
\]
Moreover,
\[
 \frac{sh+rj_0}{n}\le h+r t_*\left(1+\frac1s\right)
 \le r+1+\frac{11r}{20}\frac{81}{80}.
\]
For every \(s\ge80\), these inequalities imply the **uniform in \(s\)** estimate
\[
 \boxed{\begin{aligned}
 \log Q(A_1\times A_2)&<A(r+s+2)+E_r,\\
 E_r&=\log g(r)-r+\frac12\log(1+r/80)
     +\frac1{12(r+80)}
     +\log\left(r+1+\frac{11r}{20}\frac{81}{80}\right).
 \end{aligned}}
 \tag{6.9}
\]
Since \(q^\dagger>A\), it suffices to prove the inequality at the **smallest** permitted \(s=80\). The exact checker verifies all eleven strict comparisons
\[
 \boxed{A(r+82)+E_r<q^\dagger(r+81),\qquad r=1,\ldots,11.}
 \tag{6.10}
\]
All logarithms in this finite validation are enclosed by proved rational intervals, with no floating-point cutoff or unverifiable optimizer. The inequality for every larger \(s\) follows algebraically from the positive slope \(q^\dagger-A\). \(\square\)

## 7. The remaining complete finite parameter core

Every integer pair of positive parent dimensions \(1\le r\le s\) belongs to **exactly one** of the following covered regimes:
\[
\begin{array}{ll}
 \text{(I)}&r\ge12,\quad r+s\ge63;\\
 \text{(II)}&r\le11,\quad s\ge80;\\
 \text{(III)}&r\le11,\ s\le79,\quad\text{or}\quad 12\le r\le s,\ r+s\le62.
\end{array}
 \tag{7.1}
\]
Lemmas 6.1 and 6.2 exclude regimes (I)–(II). Regime (III) is a **genuinely finite** set of exactly **1,214 dimension splits**, all with \(r,s\le79\).

The [published exact two-layer dynamic programming certificates](../projection-persistent-nesting-gap/README.md) determine the complete Pareto frontiers of rational states \((H,Q)\) at every dimension through 84, with independent antecedent proof checkers. Their source JSON files, including the original \(D\le56\) and additional \(57\le D\le85\) states, are pinned by exact SHA-256 in [`code/check_depth2.py`](code/check_depth2.py). Coordinatewise dominance is preserved under products (1.4), so it is **logically sufficient** to check every pair of front elements instead of exponentially many expression trees. The incumbent best finite product is computed by the **exact** rational maximum
\[
 \max_{(h,u)\in E_{r+1},(j,v)\in E_{s+1}}
 \underbrace{uv\,\frac{g(r)g(s)}{g(r+s)}\frac{sh+rj}{r+s}}_{\displaystyle Q(A\times B)}.
 \tag{7.2}
\]
The new standalone checker independently evaluates **2,770,504 such candidate pairs**, takes an exact maximum for each dimension split, and verifies the **strict integer-power inequality**
\[
 \boxed{Q(A\times B)^{43}\le Q(P)^{r+s+1}.}
 \tag{7.3}
\]
The exponent 43 clears the known winning spectrum's denominator; no roots or logarithms are numerically approximated in the finite core. Of the 1,214 maxima, **one** attains equality: \(r=s=21\), both parents with exactly \((H,Q)=(12,Q_5^2)\), namely two joins of two copies of \(T_5\times T_5\). Every other verified product is strict. The checker uses the complete predecessor Pareto frontiers and rejects any change in their pinned hashes.

By (7.1) this excludes **all other** primitive product nodes at depth two in **all dimensions**. Since a join takes a \(D\)-weighted arithmetic mean of logarithmic spectral rates, and depth-one expressions satisfy the strict smaller rate \(A<q^\dagger\), the product optimum proves Theorem B. \(\square\)

## 8. A third-level witness and quantitative perspective

The exact classification distinguishes the first two nontrivial product depths:
\[
 \Gamma_1=e\left(\frac{189}{128}\right)^{1/11},\qquad
 \Gamma_2=e\left(\frac{257554342358885086515}{36893488147419103232}\right)^{1/43}.
\]
For numerical orientation only, these evaluate to approximately \(2.81631360\) and \(2.84394052\). Their strict ordering was proved by exact integer powers and does not depend on these decimals.

A completely explicit **third-level** competitor is obtained by joining two copies of \(P\) from (5.4), then forming their Cartesian square:
\[
 Y=(P*P)\times(P*P).
\]
It has dimension 170 and state
\[
 D(Y)=171,\quad H(Y)=24,\quad
 Q(Y)=Q(P)^4\,24\frac{g(85)^2}{g(170)}.
 \tag{8.1}
\]
The same exact checker proves
\[
 \boxed{Q(Y)^{43}>Q(P)^{171},}
 \tag{8.2}
\]
so \(\lambda(Y)>\lambda_2\). This is an explicit illustration of the general strict-depth hierarchy. It is **not** a claim that \(Y\) is the best depth-three body.

The point-generated class's full growth constant remains in the separately published Bellman interval. The strict-hierarchy theorem shows that no finite product depth can capture its exact supremum and that the intermediate spectral levels form a genuinely increasing infinite sequence of **attained** optimization problems. The exact depth-two theorem closes an entire infinite class rather than only a new finite-dimensional record.

## 9. Proof certificate, trust boundary, and reproduction

The [replayable exact checker](code/check_depth2.py) uses only the Python standard library's `int` and `fractions.Fraction`. The finite core performs all \(2,770,504\) candidate comparisons, retaining rational maxima within each dimension split and comparing 43rd powers exactly. The two **infinite** parameter regimes are reduced by the derivative proofs of Lemmas 6.1 and 6.2 to twelve rational-logarithmic checks: the base at \(n=63\) and the eleven small-r anchors at \(s=80\), together with the integer-power constant checks. This is not a finite extrapolation; the infinite tails are theorems proved analytically above.

To bound \(\log x\) for positive rational \(x\), the verifier factors out an **exact integer power of two** and uses \(\log y=2\operatorname{artanh}((y-1)/(y+1))\) for \(1\le y<2\). Its eighteen-term rational sum is a lower bound; the omitted upper tail is bounded by the exact fraction \(2z^{37}/(37(1-z^2))\) with \(0\le z\le1/3\). It also checks \(333/106<\pi<355/113\) from the elementary identity \(\pi=16\arctan(1/5)-4\arctan(1/239)\) using alternating rational Taylor series. No external interval package or numerical optimizer is used as proof evidence.

The **inputs** of the finite check are not guessed: the published two-layer frontier producers/checkers verify their exact construction pointers, Pareto completeness and all block/point closures. This new checker pins and reads their two frozen data files; the reproduction instructions replay their prior checker separately. The arguments of Theorem A, including strict finite-depth attainment for every \(k\), are conventional written proofs and do not claim a full proof-assistant formalization. The inherited affine geometry and two sharp one-level block inequalities are cited, not silently passed off as newly proved here.

Run from repository root:

```sh
# Replay the previous exact depth-one state space:
python3 notes/projection-persistent-nesting-gap/code/check.py

# Exact all-dimensional depth-two classification:
python3 notes/projection-product-depth-hierarchy/code/check_depth2.py
python3 -O notes/projection-product-depth-hierarchy/code/check_depth2.py
python3 notes/projection-product-depth-hierarchy/code/negative_controls.py
(cd notes/projection-product-depth-hierarchy && sha256sum -c SHA256SUMS)
```

The two depth-two checker modes are required to produce byte-identical outputs, and the negative controls test rejection of altered constants and parent-source identities. `SHA256SUMS` fixes the publication file bytes. The trust boundary is the published mathematical reduction, standard integer/Fraction arithmetic and the previously established geometric inputs, **not** merely the script returning a boolean.

## 10. Scope and further research

The new structural hierarchy covers the *entire* point-generated product/join class, not just balanced homogeneous recursions. However it neither identifies the unknown \(\lambda_*\) nor gives a closed formula for \(q_k\) for all \(k\). Each fixed-depth spectral maximum is **finite and attained**, whereas the unrestricted supremum is approached only by increasing depth. The classification of the full depth-two spectrum is exact; the depth-three example is a strict lower witness, not a full classification. The earlier 55-dimensional first mandatory nesting theorem and its permanence describe a different fixed-dimensional comparison between depths one and unrestricted depth, and remain unchanged.

The natural high-value next problem is a quantitative theory of the convergence \(q_k\nearrow q_*\), including certified upper/lower estimates that shrink with \(k\), or a universal Bellman supersolution attaining the limit. Neither is claimed here. Literature overlap, priority and geometric equality classifications beyond the stated invariant descriptions require subsequent study.
