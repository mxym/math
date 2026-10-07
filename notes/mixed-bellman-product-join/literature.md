# Primary projection-body comparison for the asymptotic problem

Checked 7 October 2026. This is a focused source comparison, not a priority certificate. No source was sent a message, no repository was modified, and nothing was pushed or published.

## Current public work and duplicate guard

The initial clean checkout was `8ad38152eac75993659c1f128a382bbc1a19ceab`. During the investigation the parent fetched public head `31e3d8a37e4a3051a7f5a2535be1c75642e15bcc`; its README, version-5 complete manuscript, and comparison were inspected using `git show FETCH_HEAD:...` without changing the checkout. A later recheck found public head `948ae3ba46a4b23f6ed8a575bb509da58b0b7152`, and its `v2/BELLMAN_UPPER_BOUND.md` was read completely. The final fetched head is **`80b3317de497dffdaa6b6398d7ba908c29cb252a`**; its README was re-read and the Bellman mathematical supplement is unchanged (the intervening commit repairs serialization of large rational certificate integers). Both the balanced-recursion theorem and the global quadratic Bellman bound are now completed work.

Version 5 already proves the unique optimum `(t,p)=(2,5)` among every balanced homogeneous simplex recursion `K_{j+1}=(K_j^t)^{*t}`, `t>=2`, `p>=1`. All competitors are below `exp(131/125)<2.8534`; the winning orbit has `2.8534<Lambda<2.8535`. Unequal arities and varying or nonhomogeneous trees remain outside that classification.

The subsequently published quadratic Bellman supplement proves, for every body in the entire point-generated product/join class,

\[
\log Q(K)\le\alpha_*\left(D-\frac{H(K)^2}{D}\right),\qquad
\alpha_*=\frac{11}{85}\log\frac{189}{128},\quad D=d+1,\ H=1/a.
\]

Consequently `2.8534<Gamma_C<=e*(189/128)^(11/85)<2.8589` is already public. A weaker bound such as `Gamma_C<3`, a quadratic bound reproducing this potential, or the rank-probability lead below does **not** advance the current upper bound. The supplement itself already records mixed quadratic/quartic discovery evidence near `2.8542`, explicitly reserving its rigorous certification. The current target is a sharper global inequality with exact certification, not rediscovery of that numerical evidence.

Version 2's exact product/join formulas and spectral supplement, version 3's explicit finite spectral amplification and rigidity, and version 4's complete symmetric equality class were read. None determines the entire recursive-class spectral supremum. A finite improvement must be compared with `Lambda/e`, not merely with an earlier finite seed.

[Current README](https://github.com/mxym/math/blob/80b3317de497dffdaa6b6398d7ba908c29cb252a/preprints/005-simplex-product-optimum/README.md), [v5 manuscript](https://github.com/mxym/math/blob/80b3317de497dffdaa6b6398d7ba908c29cb252a/preprints/005-simplex-product-optimum/v5/paper.md), [completed quadratic Bellman bound](https://github.com/mxym/math/blob/80b3317de497dffdaa6b6398d7ba908c29cb252a/preprints/005-simplex-product-optimum/v2/BELLMAN_UPPER_BOUND.md).

## Lutwak–Yang–Zhang (2001): verified full text

E. Lutwak, D. Yang and G. Zhang, *A new affine invariant for polytopes and Schneider's projection problem*, Transactions AMS **353** (2001), 1767–1779, DOI `10.1090/S0002-9947-01-02726-X`.

For every full-dimensional convex body in `R^n`, their Corollary 4.12 gives

\[
R_n(K)\le B_n:=\frac{n^n(n+1)^{(n+1)/2}}{(n!)^{3/2}}.
\]

The full statement and continuity argument appear on PDF page 11 (zero-based page 10). Stirling gives `lim B_n^(1/n)=e^(3/2)`. Their use of “asymptotically optimal” is coarse comparison up to an absolute multiplicative constant for the root functional; it does not identify the sharp limiting root.

Definition 3.1 introduces a centro-affine functional `U`. Theorem 4.11, for a polytope whose John point is the origin, strengthens the same upper bound to

\[
R_n(K)\le B_n\left(\frac{U(K)}{|K|}\right)^{n/2}.
\]

The equality case of that strengthened inequality is a simplex. This extra factor is a possible mathematical input for a recursive-class upper bound, not a result supplied by the public 005 cone invariant.

[Author PDF](https://cims.nyu.edu/~yangd/papers/trans.pdf). Local verified files: `lyz2001.pdf`, `lyz2001.txt`.

## A smaller classical unrestricted upper root already exists

Saroglou's *On the shape of a convex body with respect to its second projection body*, Advances in Applied Mathematics **67** (2015), 55–74, gives in introduction equation (3)

\[
R_n(K)\le A_n:=\omega_n^2\frac{n^n(n!)^2}{(2n)!}
\qquad (K\text{ any full-dimensional convex body}).
\]

It follows by combining Zhang's lower inequality

\[
|\Pi^\circ K|\,|K|^{n-1}\ge\frac{(2n)!}{n^n(n!)^2}
\]

with Blaschke–Santaló for the origin-symmetric body `Pi K`:

\[
|\Pi K|\,|\Pi^\circ K|\le\omega_n^2.
\]

Division gives the displayed upper bound. Since `omega_n=pi^(n/2)/Gamma(n/2+1)`, Stirling implies

\[
\omega_n^{2/n}\sim\frac{2\pi e}{n},\qquad
\left(\frac{(n!)^2}{(2n)!}\right)^{1/n}\longrightarrow\frac14,
\]

and therefore

\[
\boxed{\lim A_n^{1/n}=\frac{\pi e}{2}<e^{3/2}.}
\]

Thus `pi e/2`, rather than `e^(3/2)`, is an available classical comparison upper root. This deduction is **prior work**, not a new unrestricted theorem.

[Primary HTML, equations (2)–(3)](https://arxiv.org/html/1409.4347v2#S1), [primary PDF, page 3](https://arxiv.org/pdf/1409.4347v2). Local verified files: `saroglou2015.pdf`, `saroglou2015.txt`.

`check_classical_upper.py` rigorously encloses the numerical value using rational Machin arctangent intervals and exponential Taylor intervals:

\[
4.269867111336<\pi e/2<4.269867111337.
\]

It also proves the strict comparison with the LYZ root by checking `pi_upper^2 < 4 e_lower`, with explicit exceptions active under `python -O`. The result is stored in `classical_upper_exact.json`. This arithmetic supports an existing analytic bound; it does not prove sharpness.

## Saroglou (2011): verified scope; full-text gap persists

C. Saroglou, *Volumes of projection bodies of some classes of convex bodies*, Mathematika **57** (2011), 329–353, DOI `10.1112/S0025579311001860`.

The publisher's primary abstract confirms sharp three-dimensional maxima for zonoids, cones and double cones, with equality analysis. The author-hosted URL currently returns an institutional shutdown HTML page; the replacement host returns HTTP 503. Wiley's full-text/PDF endpoints were unavailable. Cambridge's declared citation PDF endpoint returned the abstract page as HTML. No full-text verification of its general cone identities was achieved, and no claim of disjointness from them is justified.

The same author's full 2015 primary text restates the 2011 zonoid maximum `R_3<=8`, with broader equality cases than just cylinders. It also identifies products of symmetric one- and two-dimensional bodies as “Weil bodies” in the classical second-projection-body context. This is relevant background for v4; equality for a different invariant must not be conflated with equality for `R`.

[Publisher abstract](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/S0025579311001860), [author's 2015 restatement](https://arxiv.org/html/1409.4347v2#S1).

## Feng–Hu–Liu–Xu (2026): verified full text

Y. Feng, S. Hu, W. Liu and L. Xu, *On the Reverse Projection Inequality*, MathSciDoc `2608.23002`, uploaded 21 August 2026, PDF dated 26 August 2026.

Theorem 1.3 constructs full-dimensional counterexample polytopes with at most `n+2` facets in every dimension `n>=9`. Section 4 gives the simplex-section/cube-projection mechanism and a pyramidal lifting. Theorem 1.2 completes tetrahedron equality for the already established all-body `R_3<=18` theorem. The introduction explicitly reserves dimensions `4<=n<=8`.

These counterexamples do not determine the optimal high-dimensional exponential growth root. Their section construction is inherited prior work, including the conservative dimension-13 specialization already in the public repository. Their claims do not turn the old simplex-product optimum into an unrestricted optimum. The paper credits existing LYZ estimates and Henk's symmetric repeated-block lower bound.

[Author-uploaded archive record](https://archive.ymsc.tsinghua.edu.cn/pacm_paperurl/20260821091122099811781), [full primary PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/743/12781--2026.8.26.pdf). Local verified files: `fhlx2026.pdf`, `fhlx2026.txt`.

## Henk (2025) and recent related work

M. Henk, *Note on projection bodies of zonotopes with n+1 generators*, Acta Mathematica Scientia **45** (2025), 96–103, DOI `10.1007/s10473-025-0107-9`. The primary publisher abstract states `R_n(Z)=2^n` for every `n`-dimensional zonotope with `n+1` generators and supplies centrally symmetric examples with `R_n>=2^n(9/8)^floor(n/3)`. Their root approaches `2(9/8)^(1/3)`, below the present 005 lower root. The full text was not acquired; the author's publication page contains a bibliographic entry without a preprint link.

[Publisher abstract](https://link.springer.com/article/10.1007/s10473-025-0107-9), [author publication page](https://page.math.tu-berlin.de/~henk/publications.html).

Saroglou–Zvavitch's 2015 paper studies local convergence of iterated projection bodies and ellipsoid local minimality, rather than the global maximum-growth root. Langharst's revised 2025 paper studies mixed and higher-order **polar** projection bodies and stability, rather than the ordinary projection-body asymptotic maximum. Neither source inspected supplies a matching sharp bound for the product/join closure.

[Saroglou–Zvavitch primary text](https://arxiv.org/html/1511.03381), [Langharst primary text](https://arxiv.org/html/2504.18933v2). Local Saroglou–Zvavitch PDF and text were saved. Bourgain–Lindenstrauss's author-institutional 1988 primary PDF was also saved for background.

## Bellman-method precedent and the mixed-potential claim

The use of a homogeneous concave potential and a local inequality that telescopes over an operation tree has substantial precedent. Arcozzi–Holmes–Mozolyako–Volberg, *Bellman Function Sitting on a Tree*, IMRN **2021**, 12037–12053, DOI `10.1093/imrn/rnz224`, explicitly use

\[
\mathcal B(F,f,A,v)=4\left(F-\frac{f^2}{v+A}\right)
\]

as a Bellman **supersolution**, distinct from the actual extremal Bellman function. Section 1 states its domain, boundedness and local main inequality; Lemma 1.5 verifies the tree inequality, and the proof of Theorem 1.3 telescopes it. The state variables and child laws concern Carleson embedding, not projection bodies, but the quadratic perspective and local-to-tree proof structure are close methodological analogues. The paper attributes that supersolution to Nazarov–Treil–Volberg (JAMS 1999).

[Full primary text, Section 1 and Lemma 1.5](https://arxiv.org/html/1809.03397), [publisher record](https://academic.oup.com/imrn/article/2021/16/12037/5610523). Local verified PDF/text: `bellman_tree2018`.

Ivanisvili–Volberg's *Hessian of Bellman functions and uniqueness of Brascamp–Lieb inequality* explicitly studies homogeneous concave Bellman functions. Its Lemma 2 gives the degree-one perspective representation; Lemma 6 characterizes the jointly concave degree-one case under its stated assumptions. Their later *Bellman partial differential equation and the hill property for classical isoperimetric problems* develops modified-Hessian conditions for generating inequalities, including Brascamp–Lieb, Prékopa–Leindler and Ehrhard inequalities. These papers establish the broader method, not the 005 product/join state laws or constants.

[Primary Hessian paper](https://arxiv.org/html/1411.5349), [primary isoperimetric paper](https://arxiv.org/html/1506.03409). Local verified PDF/text: `bellman_hessian2014`, `bellman_isoperimetric2015`.

For a proposed 005 potential of the form

\[
\Phi(D,H)=D\left[c_2\left(1-(H/D)^2\right)+c_4\left(1-(H/D)^4\right)\right],
\]

the quadratic and quartic terms both have degree one in `(D,H)`. When `c_2,c_4>=0`, the normalized profile is concave on `0<=H/D<=1`; its perspective is concave, which handles additive join states. These elementary observations are analytic structural facts, not a new theorem or a proof of the product inequality. The product step still requires the exact transition law, complete state range, and global certification over all dimensions.

A focused search for primary work combining Bellman functions, ordinary projection-body volume and products/joins did not locate a matching mixed quadratic/quartic inequality. This is a limited search result, not an absence or priority certificate. The proposed contribution should be stated as a **specific stronger certified projection-body bound for this class**, with the Bellman method credited as established. The mixed-potential numerical discovery already recorded in the public supplement is prior 005 work; only its stronger rigorous certification would advance the current head.

## Exploratory rank-probability lead: not yet an upper-envelope theorem

For a polytope at its John point, normalize cone volumes to a probability law on radial polar facet points `u_i/h_i`. Put

\[
P(K)=\Pr(X_1,\ldots,X_d\text{ linearly independent}),\qquad
S(K)=\Pr(X_1,\ldots,X_{d+1}\text{ affinely independent}).
\]

LYZ Definition 3.1 implies `(U(K)/|K|)^d=P(K)`, so its strengthened upper inequality is `R(K)<=B_d sqrt(P(K))`. The rank probabilities depend on zero/nonzero minors rather than determinant magnitudes and differ from the 005 invariant `a`.

An independently derived candidate recursive calculus has these formulas. For a product, `w_A=r/(r+s)`, `w_B=s/(r+s)`, and

\[
P(A\times B)=\binom{r+s}{r}w_A^rw_B^sP(A)P(B),
\]

\[
S(A\times B)=
\binom{r+s+1}{r}w_A^rw_B^{s+1}P(A)S(B)
+\binom{r+s+1}{r+1}w_A^{r+1}w_B^sS(A)P(B).
\]

For a join, write `d=r+s+1`, `D=d+1`, `w_A=(r+1)/D`, `w_B=(s+1)/D`. Then the candidate formulas are

\[
P(A*B)=
\binom d r w_A^rw_B^{s+1}P(A)S(B)
+\binom d{r+1}w_A^{r+1}w_B^sS(A)P(B),
\]

\[
S(A*B)=\binom D{r+1}w_A^{r+1}w_B^{s+1}S(A)S(B).
\]

The John-origin choice is essential. In factor coordinates with John balls, the proposed join John ellipsoid has center height `(s+1)/D` and squared horizontal/vertical radii

\[
\alpha^2=\frac{r(r+1)}{Dd},\qquad
\beta^2=\frac{s(s+1)}{Dd},\qquad
\gamma^2=\frac{(r+1)(s+1)}{D^2d}.
\]

John's contact identities appear to verify this ellipsoid; facet cone-volume groups have the displayed weights. Rank allocation then gives the formulas. These are leads requiring a complete independent proof and appropriate zero-dimensional guards before inclusion as a theorem. In particular, no dimension-uniform envelope `P(K)<=c^d` with a useful certified `c` has been proved here. The lead is not a new asymptotic upper bound.

## Assessment

A rigorously sharper upper envelope over every operation tree would advance beyond the now-public quadratic Bellman bound `Gamma_C<2.8589`. A larger exactly certified lower rate would also advance the current collection, provided the comparison is against the actual limiting threshold. The inspected external primary literature does not supply either sharper result, but this finite search cannot certify absence or first discovery. Unavailable 2011 cone full text, subscription sources, comprehensive citation databases, and all later citing papers remain limitations.

中文状态：已更新至公共提交 `80b3317`；v5 均衡递归分类与全产品／join 类的二次 Bellman 上界 \(\Gamma_{\mathcal C}<2.8589\) 均已完成，不能重复报作新成果。应继续精确认证更强的混合二次／四次势函数。经典全体上界 \(\pi e/2\) 与 LYZ 秩概率因子只作已有背景及研究线索。

Final source reconciliation: public head `3360e7191cf564a46d09edcbfbd107c9178bd98f` was fetched and its 005 README and Bellman diff read. The high-boundary quadratic label and tail derivative guards were clarified; the quadratic ceiling is unchanged. The new certified mixed envelope in `proof.md` strictly lowers that ceiling.
