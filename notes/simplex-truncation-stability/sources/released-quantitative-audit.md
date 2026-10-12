# Independent audit of the quantitative projection simplex supplement

Date: 7 October 2026.

Audited manuscript: `paper.md`, titled *Effective simplex rigidity for the projection cone invariant*, with date line “Supplement to entry 005, 7 October 2026.” Its final audited SHA-256 is `33651147ae32773add33066c3b60dd099209dcadd6b3b7079e3e08eeaba976d2`.

## Verdict and scope

**No substantive mathematical defect found.** Conditional on the cone-law representation and affine invariance explicitly imported from entries 005 v2–v3, Sections 2–7 prove Theorem 1 with the displayed constants, for arbitrary full-dimensional convex bodies and every maximum-volume inscribed simplex. The proof correctly handles nonatomic and mixed cone-volume laws. Proposition 2 and the planar conversion to the attributed bound $576e/(1+3e)$ are correct.

The optional orientation clarification identified during the audit has been incorporated: Proposition 2 now specifies counterclockwise edges and polar vertices, matching its positive-determinant statement. The final manuscript also explicitly requires both point tuples in the perturbation estimate to lie in the unit ball. These clarifications require no change to any theorem, bound, or constant. No outstanding mathematical correction is requested.

The public manuscript was audited mathematically before consulting the earlier working proof, earlier independent audit, or companion test scripts. The earlier documents were then checked for omissions introduced by compression; none was found. This auditor did not modify any theorem file. The final orientation, perturbation, abstract, bibliography-title, and page-break edits were inspected before recording the final hash. This is an independent model audit, not human peer review, proof-assistant formalization, a complete audit of earlier versions, or an originality assessment.

## Normalization and the exact defect

Fixing an arbitrary maximum simplex at the start is legitimate: a maximum exists by compactness, and its volume is positive because the body has interior. Under the stated affine normalization, a regular simplex of inradius one has vertex norms $d$. The vertex-replacement determinant identity gives $|\alpha_i(x)|\le1$ for every $x\in K$, including replacements whose orientation reverses. Consequently

\[
|x|\le\sum_{i=0}^d|\alpha_i(x)|\,|v_i|\le d(d+1)=R_0.
\]

The cone-volume pushforward is a probability by the standard volume formula; its mean is zero because the factors $h_K$ cancel and $\int u\,dS_K(u)=0$. Its support is contained in the compact image $\partial K^\circ\subseteq B_2^d$, so $A\le1$ by Hadamard. The directional estimate also ensures $A>0$.

Cauchy's formula and centering give exactly

\[
\int(-\langle u,x\rangle)_+\,d\nu
=\frac{|K\mid u^\perp|}{d|K|}
\ge\frac{(2/d)^{d-1}}{d(2R_0)^d}
=\frac1{2(dR_0)^d}=2b.
\]

The chosen projection cube is contained in the unit ball: its corner norm is $\sqrt{d-1}/d\le1$. No density or atomicity assumption is used.

For every base tuple, including horizontally singular ones, $F_{\mathbf x}$ is affine and centering gives $\int F_{\mathbf x}\,d\nu=\det(x_1,\ldots,x_d)$. Therefore

\[
\int|F_{\mathbf x}|\,d\nu-
\left|\int F_{\mathbf x}\,d\nu\right|
=2\min(P(\mathbf x),N(\mathbf x)).
\]

Integrating proves (2.4) without discarding any base tuples. Equation (2.2), including its factor $d+1$, follows from the imported representation.

The determinant perturbation constant is correct. A telescoping replacement of the $d$ difference columns has $d$ terms, each bounded by $(2r)2^{d-1}$, giving $Lr=d2^dr$. All actual support points and representatives lie in the unit ball.

## Heavy cells and the nonatomic step

The specified grid has diameter at most $r$ and at most $(3d/r)^d$ cells. Since light cells have mass below $\tau$, their total mass is at most $\eta$. A positive-mass measurable cell meets the support; its chosen representative need not be an atom.

The directional replacement error is at most $\eta+r$. Since $r\le\eta\le b/(4d)$, the displayed lower bound $2b-\eta-r\ge b$ is valid. Taking all unit directions gives $bB_2^d\subseteq\operatorname{conv}X$.

The determinant lower bound $V\ge b^d$ follows from separate convexity of the absolute affine determinant, starting with $0,be_1,\ldots,be_d\in\operatorname{conv}X$. Replacing one vertex at a time by an element of $X$ cannot lower the maximum. This does not assume $0\in T$.

Both witness configurations have the stated opposite signs. In the first case, the extra representative with a negative barycentric coordinate cannot equal any vertex of $T$. In the second case, a representative with two coefficients at least $\eta>0$ also cannot equal a vertex. Thus in both cases the $d$ base representatives and two tested representatives occupy $d+2$ distinct cells.

The representative margins are at least $\eta V\ge\gamma$. Moving all $d+1$ points in either tested determinant costs at most $Lr=\gamma/4$; the retained margin $\gamma/2$ is conservative. For every actual support base tuple in the selected base cells, both sign integrals are at least $\tau\gamma/2$. Integrating over just that ordered product of base cells yields

\[
D\ge2\tau^d(\tau\gamma/2)=\tau^{d+1}\gamma.
\]

There is no missing factorial or additional probability factor. Direct expansion gives

\[
\tau^{d+1}\gamma
=b^d\left(\frac{b^d}{12dL}\right)^{d(d+1)}
\eta^{(d+1)^2+1}
=\chi\eta^p.
\]

This is a full positive-measure product-cell argument. It works unchanged for nonatomic, atomic, or mixed laws; no mass at the selected representatives is used.

When neither witness exists, the coefficients sum to one and exactly one is at least $\eta$. The other $d$ coefficients lie between $-\eta$ and $\eta$, giving the $2d\eta$ distance bound. Comparing support functions then gives $(b/2)B_2^d\subseteq T$. This establishes interior containment before taking the polar. The light-cell contribution to the expected distance is at most $2\eta$, proving (3.6).

## Mixed volume and the cap estimate

Polarity gives $K\subseteq P=T^\circ\subseteq MB_2^d$, and $P$ is a bounded simplex. Each vertex $w_i$ of $T$ defines a genuine supporting facet of $P$, so $h_P(w_i)=1$. Also $h_K(x)=1$ on the support of $\nu$. The $M$-Lipschitz estimate proves (4.2).

The pushforward conversion has the correct normalization:

\[
\int(h_P(x)-1)\,d\nu(x)
=\frac1{d|K|}\int h_P(u)\,dS_K(u)-1
=\frac{V(K[d-1],P)}{|K|}-1.
\]

Minkowski's first inequality has the required direction, yielding $(|P|/|K|)^{1/d}\le1+Z\eta$. For $Z\eta\le1$, the elementary estimate $(1+x)^d-1\le d2^{d-1}x$, together with $|K|\le(2R_0)^d$, proves (4.3).

The cap construction is valid for an arbitrary convex body. At a farthest $q\in P$, metric projection onto $K$ gives a supporting gap exactly $s=d_H(K,P)$. Since $0\in K$, $s\le M$. With $t=s/[2(M+1)]$, the constructed ball lies in $P$, and its lowest coordinate in the chosen direction is at least

\[
\langle u,q\rangle-t(\langle u,q\rangle+1)
\ge h_K(u)+s/2.
\]

It is disjoint from $K$. The cube of side $2t/d$ is contained in that ball, so the stated volume lower bound follows. The enlargement to $C=4d^2R_0(M+1)$ is valid because $[d2^{d-1}]^{1/d}\le2d$.

## Why the conclusion applies to every maximum simplex

The smallness gate makes $s<1$. Since $h_P\ge1$, the support-function inequalities imply $(1-s)P\subseteq K$. This is an inscribed simplex, so maximality of the originally fixed $\Delta$ gives

\[
|\det W|=|\Delta|/|P|\ge(1-s)^d\ge1-ds.
\]

For $\delta=ds\le1/8$, each probability column of $W$ has norm at least $1-\delta$ by Hadamard. Its largest entry is therefore at least its squared norm, hence at least $1-2\delta$.

The dominant rows are distinct. If two coincided, independent categorical draws from those two columns would collide with probability at least $(1-2\delta)^2$. The permanent of the full matrix, which is the probability of all rows being distinct, would then be at most $4\delta<1-\delta\le|\det W|$, impossible.

The dominant rows thus give a matching of all vertices. Its distance bound is $2\delta\operatorname{diam}P\le4M\delta$, and convex combinations give the Hausdorff bound in Section 6. Because $B_2^d\subseteq\Delta$, the final Minkowski-sum inclusion indeed gives $P\subseteq(1+4Mds)\Delta$. No step replaces the original maximum simplex by a favorable newly chosen one. Undoing the affine map restores precisely its centroid as the homothety center.

## Constants and endpoint checks

Every smallness restriction used in the proof is supplied by a displayed term of $\eta_0$:

- $1/[2(d+1)]$ guarantees the unique large barycentric coefficient.
- $b/(4d)$ controls the retained directional mass and the inradius of $T$.
- $1/Z$ permits the linearized volume estimate.
- $1/[Z(8MdC)^d]$ yields $s\le1/(8Md)$ and $A_de_0^{\theta_d}\le1/2$.

The last assertion follows exactly from

\[
A_de_0^{\theta_d}=4MdC(Z\eta_0)^{1/d}.
\]

The parameter choice gives exponent $1/[d(d^2+2d+2)]$ and exactly the displayed $A_d$. At $e=0$, $D=0<\chi\eta^p$ for every positive admissible $\eta$; taking the infimum of the resulting bounds for the same $\Delta$ proves $E=0$. For $e>e_0$, $K\subseteq R_0B_2^d\subseteq R_0\Delta$ proves the global branch and the specified $G_d$. The stated tolerance function follows immediately.

An independent rational-arithmetic calculation verified the formulas and all gates for $d=2,\ldots,8$. The first exponents are $1/20,1/51,1/104$. In $d=2$, exact rational comparisons verify $10^{-279}\le e_0<10^{-278}$; its decimal logarithm is approximately $-278.38283862309212$. Rationality of $\chi,\eta_0,e_0$ follows in every dimension from their definitions.

After the independent mathematical audit, isolated copies of the supplied scripts were rerun. They passed 7 dimensions of exact constant checks, 400 determinant perturbations, 400 barycentric matrices, 8,320 nonatomic box-corner sign tests, and 200 exact polygon identities and deficit conversions. Their output counts agree with the manuscript. These finite regressions are corroboration, not a substitute for the preceding all-dimension reasoning.

## Planar identity and the prior bound

With counterclockwise indexing, the polar vertices have positive lifted determinants. The coefficient of $b_k$ in the triple-determinant sum equals $T_0$: if $U=\sum_{i<k}u_i$, $W=\sum_{j>k}u_j$, and $U+u_k+W=0$, then the difference between the two coefficients is

\[
2\det(U,W)+\det(U,u_k)+\det(u_k,W)=0.
\]

The closed-edge signed-area formula gives $T_0=2|K|$, and the support-number formula gives $\sum b_i=2|K|$. Thus $\Sigma=4|K|^2$. The denominator $2|K|\,|\Pi K|$ is consistent both with the imported polytope formula and with directly evaluating $B/(3A)$ for the atomic polygonal cone law. In the plane, $\Pi K$ is a quarter-turn of $K-K$, proving $aR=2$. Polygonal approximation and continuity extend the result to every planar convex body.

The [author-hosted Böröczky text](https://www.renyi.hu/~carlos/rogerstab.pdf) was independently opened. Its definition of multiplicative simplex Banach–Mazur distance matches the manuscript. Section 8, printed page 20 (PDF page index 19), explicitly states $V(K-K)\le(6-t/32)V(K)$ when $d_{BM}(K,T)=1+t$. The hosted file carries a 16 April 2010 submission timestamp, as the manuscript warns. This audit verifies that hosted source, rather than asserting identity with a separately inspected journal typesetting.

The exact conversion is

\[
R=\frac6{1+3e},\qquad
\rho=1-\frac R6=\frac{3e}{1+3e},\qquad
t\le32(6-R)=192\rho=\frac{576e}{1+3e}\le576e.
\]

The coefficient 576 and inequality directions are correct. This is an inherited Banach–Mazur result; it does not by itself assert the supplement's centered containment for every prescribed maximum simplex. The manuscript correctly compares it with Theorem 1's planar Banach–Mazur consequence and makes no novelty or optimality claim.
