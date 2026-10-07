# A certified mixed quadratic/quartic envelope for projection-body growth

**Research continuation of entry 005. Complete English proof, 7 October 2026.**

The public repository was initially read at `8ad38152eac75993659c1f128a382bbc1a19ceab` and rechecked during the work through `3360e7191cf564a46d09edcbfbd107c9178bd98f`. Its v5 balanced-recursion classification and its newly published quadratic Bellman bound are completed prior work. The mixed-potential discovery mentioned in that supplement is also acknowledged. The contribution below is exact certification of a strictly smaller upper ceiling over every finite product/join tree. It is not a new lower construction or an unrestricted extremal theorem.

The finite certificate, imbalanced-tail certificate, and analytic large-factor proof have passed exact replay and a separate mathematical audit. Ordinary and optimized Python checks remain active and pass. This is model-assisted research and exact arithmetic verification, not human peer review or proof-assistant formalization.

## The theorem and its hypotheses

Let \(\mathcal C\) be the class generated from a formal zero-dimensional point by finitely many joins, Cartesian products, and invertible affine maps on affine hulls. Thus affine images here mean affine equivalences; rank-dropping maps are outside this class. A product with a point is redundant. For a positive-dimensional convex body in this class, put
\[
d=\dim K,\qquad D=d+1,\qquad H=\frac1{a(K)},\qquad
g(d)=\frac{d^d}{d!},\qquad
Q=\frac{a(K)R(K)}{g(d)},\qquad
R(K)=\frac{|\Pi K|}{|K|^{d-1}}.
\]
The projection-body normalization, the invariant \(a\), and the exact calculus are those of entry 005 v2. For a point set \((D,H,Q)=(1,1,1)\). Define
\[
\alpha=\frac{87}{2000},\qquad
\beta=\frac{11}{2000},\qquad
T=\alpha+\beta=\frac{49}{1000}.
\]
The new inequality is
\[
\boxed{\log Q(K)\le
\alpha\left(D-\frac{H^2}{D}\right)
+\beta\left(D-\frac{H^4}{D^3}\right).}
\tag{1}
\]
Consequently the optimal asymptotic rate of the entire class satisfies
\[
\boxed{2.8534<\Gamma_{\mathcal C}\le e^{1049/1000}<2.855.}
\tag{2}
\]
Here \(\Gamma_{\mathcal C}=\lim_{d\to\infty}\sup_{K\in\mathcal C_d}R(K)^{1/d}\). Its existence and its equality to \(e\sup Q(K)^{1/(d+1)}\) are the spectral reduction already proved in entry 005. The lower endpoint is the already certified self-similar family, not a new lower-bound claim.

All proof decisions in the certificates below use integers, fractions, and rational logarithm intervals. Floating optimization is used only to propose rational supporting points. Acceptance of such a point is governed entirely by the exact inequalities below.

## 1. Structural induction and join closure

The exact v2 calculus is
\[
(D,H,Q)(A*B)=(D_A+D_B,H_A+H_B,Q_AQ_B).
\tag{3}
\]
For a product of positive-dimensional factors, let \(r=\dim A\), \(s=\dim B\), \(n=r+s\), \(h=H_A\), and \(j=H_B\). Then
\[
H'=\frac{n}{r/h+s/j},\qquad
D'=n+1,\qquad
Q'=Q_AQ_B Cx,
\tag{4}
\]
where
\[
C=\frac{g(r)g(s)}{g(n)},\qquad
x=\frac{sh+rj}{n}.
\tag{5}
\]
Every positive-dimensional state in \(\mathcal C\) obeys
\[
2\le H\le d+1.
\tag{6}
\]
The upper bound follows from the inherited inequality \(a\ge1/(d+1)\). For the lower bound, the first positive-dimensional body is the join of two points, with \(H=2\). Joins add \(H\); products make \(a\) a dimension-weighted arithmetic mean, and therefore preserve \(a\le1/2\). This argument concerns this class, and does not assume symmetry of all its bodies.

For \(p\ge1\), Hölder's inequality gives
\[
\frac{(H_1+H_2)^p}{(D_1+D_2)^{p-1}}
\le \frac{H_1^p}{D_1^{p-1}}+\frac{H_2^p}{D_2^{p-1}}.
\tag{7}
\]
For instance this is Jensen applied to \(u\mapsto u^p\), with weights \(D_i/(D_1+D_2)\). Applying (7) with \(p=2,4\) proves that (1) is preserved by joins. The point has equality. It remains to prove product closure.

## 2. A strictly concave product supersolution

Define
\[
\Delta_p=-1+\frac{h^p}{(r+1)^{p-1}}+
\frac{j^p}{(s+1)^{p-1}}-\frac{(H')^p}{(n+1)^{p-1}}.
\]
The difference between the product's potential in (1) and the sum of the two input potentials is \(\alpha\Delta_2+\beta\Delta_4\). Therefore product closure follows from
\[
\log(Cx)\le\alpha\Delta_2+\beta\Delta_4.
\tag{8}
\]
Weighted harmonic mean is at most weighted arithmetic mean and at most weighted fourth-power mean. Thus (8) follows from strict negativity of
\[
f_{r,s}(h,j)=\log(Cx)-\alpha G_2(h,j)-\beta G_4(h,j)+T,
\tag{9}
\]
where
\[
G_2=\frac{h^2}{r+1}+\frac{j^2}{s+1}
-\frac{(rh+sj)^2}{n^2(n+1)},
\tag{10}
\]
\[
G_4=A_4h^4+B_4j^4,
\quad A_4=\frac1{(r+1)^3}-\frac r{n(n+1)^3},
\quad B_4=\frac1{(s+1)^3}-\frac s{n(n+1)^3}.
\tag{11}
\]
Both quartic coefficients are positive. For example \(r(r+1)^3<n(n+1)^3\).

The quadratic form \(G_2\) is positive definite. Its first diagonal coefficient is positive, and its determinant is
\[
\frac{rs(3n+2)}{(r+1)n^2(s+1)(n+1)}>0.
\tag{12}
\]
Hence \(f_{r,s}\) is strictly concave throughout the positive quadrant: its logarithm is concave, and the subtracted quadratic and quartic terms are convex. In particular every supporting plane gives a global upper bound on its entire state rectangle. No untested sampling of states is used below.

By symmetry assume \(r\le s\). We prove (9) is negative in three exhaustive ranges: both dimensions below 200; \(r<200\le s\); and both dimensions at least 200.

## 3. Both dimensions large: an analytic proof

The proof in `mixed_large_dimensions.md` actually handles \(r,s\ge160\). Its main estimates are included here to make the all-dimension argument explicit. Put
\[
\delta=4rs+3n+2,\qquad k=\frac{3n+2}{\delta}.
\]
Direct expansion gives
\[
G_2-kx^2=
\frac{rs}{(r+1)n^2(s+1)(n+1)\delta}
\big[(s+1)(3r+s+2)h-(r+1)(r+3s+2)j\big]^2\ge0.
\tag{13}
\]
Since \(G_4\ge0\),
\[
f_{r,s}\le\log(Cx)-\alpha kx^2+T
\le\frac12\log\frac{C^2}{2\alpha k}-\frac12+T.
\tag{14}
\]
The last inequality maximizes the elementary function over every \(x>0\). It is enough that
\[
\frac{C^2}{k}<2\alpha e^{1-2T}.
\tag{15}
\]
The normalized factorial sequence \(v_m=m!e^m/(m^m\sqrt m)\) strictly decreases by the proof in Section 5, and has limit \(\sqrt{2\pi}\) by ordinary Stirling asymptotics. Thus
\(C=(v_n/(v_rv_s))\sqrt{n/(rs)}<\sqrt{n/(2\pi rs)}\).
For \(r,s\ge160\), this gives
\[
\frac{C^2}{k}
<\frac2\pi\left(\frac{n}{3n+2}+\frac{n}{4rs}\right)
<\frac{2/3+1/160}{\pi}
<\frac{1615}{7536}.
\tag{16}
\]
The final inequality uses \(\pi>157/50\). Exact rational arithmetic verifies
\[
\frac{1615}{7536}
<\frac{87}{1000}\sum_{m=0}^{10}\frac{(451/500)^m}{m!}
<\frac{87}{1000}e^{451/500}=2\alpha e^{1-2T}.
\tag{17}
\]
For completeness, Machin's identity and alternating-series bounds give
\[
\pi=16\arctan(1/5)-4\arctan(1/239)
>16\left(\frac15-\frac{1}{3\cdot5^3}+\frac{1}{5\cdot5^5}-\frac{1}{7\cdot5^7}\right)-\frac4{239}
>\frac{157}{50}.
\]
The last comparison is rational. The identity follows from the double-angle tangent formula: \(\tan(4\arctan(1/5))=120/119\) and \(\tan(4\arctan(1/5)-\arctan(1/239))=1\); the latter angle lies in \((0,\pi/2)\). Equations (14)–(17) prove strict product closure in this range. `check_mixed_large_dimensions.py` checks these rational constants and the positive Taylor comparison.

## 4. Both dimensions below 200: exact supporting planes

There are 19,900 pairs \(1\le r\le s\le199\). `mixed_finite_points.json` supplies one rational point \(p=(h_0,j_0)\) in each rectangle
\[
\mathcal B_{r,s}=[2,r+1]\times[2,s+1].
\]
For every such pair, `check_finite.py` recomputes \(G_2,G_4\) and the gradient of (9) exactly, encloses its one logarithm rationally, and proves
\[
f_{r,s}(p)+
\max_{(h,j)\in\mathcal B_{r,s}}
\nabla f_{r,s}(p)\cdot((h,j)-p)<0.
\tag{18}
\]
The maximum in (18) is the sum of two elementary endpoint choices: use the upper coordinate bound when the corresponding gradient is nonnegative, and the lower bound otherwise. Concavity gives \(f_{r,s}(h,j)\) at most (18) for every real state in the rectangle.

The certificate checks ordered coverage of every dimension pair, and checks that every point lies inside its rectangle. Its largest upper bound occurs at \((r,s)=(5,5)\), with
\[
p=\left(\frac{5995534181}{10^9},\frac{5995534181}{10^9}\right),
\]
and is strictly less than \(-3/2000\). The exact rational value appears in `finite_report.json`. This proves every finite rectangle, not merely its proposed point.

## 5. One small factor and an arbitrarily large factor

Fix \(1\le r<200\) and let \(s\ge200\). Set
\[
z=1/s\in(0,1/200],\qquad h=H_A,\qquad
u=H_B/(s+1)\in[0,1].
\]
The enlarged rectangle \([2,r+1]\times[0,1]\) contains every actual state. Write
\[
P_2=(1+rz)^2(1+(r+1)z),
\quad S_2=3+(3r+2)z+r(r+1)z^2,
\]
\[
P_4=(1+rz)(1+(r+1)z)^3,
\quad S_4=4+(6r+9)z+(4r^2+9r+6)z^2+(r+1)^3z^3.
\]
Exact cancellation of the apparent singularity at \(z=0\) gives
\[
G_2=a h^2+bhu+c u^2,
\quad a=\frac1{r+1}-\frac{r^2z^3}{P_2},
\quad b=-\frac{2rz(1+z)}{P_2},
\quad c=\frac{r(1+z)S_2}{P_2},
\tag{19}
\]
\[
G_4=a_4h^4+d_4u^4,
\quad a_4=\frac1{(r+1)^3}-\frac{rz^4}{P_4},
\quad d_4=\frac{r(1+z)S_4}{P_4}.
\tag{20}
\]
These are regular throughout the closed interval \([0,1/200]\).

The factorial ratio has the useful upper bound
\[
C\le g(r)e^{-r}\sqrt{1+rz}.
\tag{21}
\]
To prove it, define \(v_m=m!e^m/(m^m\sqrt m)\). Then
\[
\log(v_{m+1}/v_m)=1-(m+1/2)\log(1+1/m)<0,
\]
using \(\log t>2(t-1)/(t+1)\) for \(t>1\), whose derivative proof is elementary. Exact substitution gives
\(C=g(r)e^{-r}(v_{r+s}/v_s)\sqrt{(r+s)/s}\), proving (21).

Consequently (9), after normalization, is bounded above by the strictly concave function
\[
F_{r,z}(h,u)=\log g(r)-r+
\log(h+r(1+z)u)-\tfrac12\log(1+rz)
-\alpha G_2-\beta G_4+T.
\tag{22}
\]
Its state gradient is the same as that of the actual normalized function (9). The added constant in (21) depends only on dimensions.

The tail certificate partitions \([0,1/200]\) into finitely many rational dyadic intervals, separately for each of the 199 values of \(r\). On each cell it supplies a rational point \(p=(h_0,u_0)\). Standard rational interval arithmetic encloses (19)–(22) and the two state derivatives on the entire cell. All divisions are checked to have denominators separated from zero.

For additional strength, let \(a_-\) and \(c_-\) be the lower interval endpoints for \(a,c\), and \(b_*^2\) the larger squared endpoint for \(b\). The checker verifies
\[
m_h=a_-/2>0,\qquad
m_u=c_- -b_*^2/(2a_-)>0.
\]
Young's inequality then gives, uniformly in the whole cell,
\[
a\eta_h^2+b\eta_h\eta_u+c\eta_u^2
\ge m_h\eta_h^2+m_u\eta_u^2.
\tag{23}
\]
The logarithm and quartic terms are concave with favorable Taylor remainders. Hence
\[
F_{r,z}(p+\eta)
\le F_{r,z}(p)+\nabla F_{r,z}(p)\cdot\eta
-\alpha(m_h\eta_h^2+m_u\eta_u^2).
\tag{24}
\]
Each separated scalar maximum on the coordinate displacement interval is exact: maximize \(g\eta-\alpha m\eta^2\) at its clipped vertex \(g/(2\alpha m)\). When the gradient is an interval, use its lower endpoint on negative displacements and its upper endpoint on positive displacements. This encloses every possible gradient, rather than using a point approximation to it.

`check_mixed_tail.py` recomputes these upper bounds on all 15,568 cells, of dyadic depth at most seven, and verifies that every bound is less than \(-1/10^8\). It also verifies exact coverage, with no gap or overlap, of \([0,1/200]\) for every \(r\). Thus the certificate covers all real \(z\) in that interval and therefore every integer \(s\ge200\). The endpoint \(z=0\) is used only as a regular limiting parameter; it does not assert existence of an infinite-dimensional body.

## 6. Exact logarithms, completion, and the rate

For a positive rational argument, power-of-two reduction writes \(x=2^k y\), \(1\le y\le2\). With \(w=(y-1)/(y+1)\in[0,1/3]\),
\[
\log y=2\sum_{m=0}^{N-1}\frac{w^{2m+1}}{2m+1}+E_N,
\quad 0\le E_N\le
\frac{2w^{2N+1}}{(2N+1)(1-w^2)}.
\tag{25}
\]
The same expansion encloses \(\log2\). Both checkers preserve the correct endpoints when multiplying by a negative integer \(k\). Their optional rational outward rounding enlarges intervals and therefore preserves correctness. Every check remains active under `python -O`.

Sections 3–5 exhaust all positive integer dimension splits. They prove (8), so products preserve (1). Joins preserve (1) by (7), and the point satisfies it. Structural induction over finite expressions and affine invariance complete the theorem.

Dividing (1) by \(D\) gives
\[
\log\lambda(K)\le
T-\alpha(H/D)^2-\beta(H/D)^4<T.
\]
Taking the all-dimensional supremum and applying the inherited spectral identity gives \(\Gamma_{\mathcal C}\le e^{1+T}\). With \(x=1049/1000\), the positive exponential series gives
\[
e^x<\sum_{m=0}^{12}\frac{x^m}{m!}+
\frac{x^{13}/13!}{1-x/14}<\frac{571}{200}=2.855.
\]
Every subsequent ratio after the first omitted term is at most \(x/14<1\), proving the tail bound. The last rational comparison is replayed by the large-dimension checker. The v2 exact checker was also rerun successfully, preserving the strict lower endpoint \(2.8534\).

## Scope and comparison

The current public quadratic Bellman theorem gives the ceiling \(e^{1+\alpha_*}\), where \(\alpha_*=(11/85)\log(189/128)\), and reports \(\Gamma_{\mathcal C}<2.8589\). The strict improvement here compares the actual constants, not just their rounded decimals:
\[
\alpha_*>\frac{11}{85}\frac{2(189-128)}{189+128}
=\frac{1342}{26945}>\frac{49}{1000}=T.
\]
The logarithm bound is the one proved in Section 5, and the final rational gap is \(21695/26945000>0\). Therefore \(e^{1+T}<e^{1+\alpha_*}\). The numerical mixed-potential direction was already recorded in that public supplement. This report claims exact certification of the displayed parameters, not discovery of the Bellman method or of the numerical direction.

The optimum and the known lower orbit remain distinct: no proof here identifies their values, and no finite spectral improvement is advertised as an improvement of the actual limiting rate. The theorem is confined to \(\mathcal C\). For unrestricted convex bodies, the classical Zhang–Blaschke–Santaló bound recorded in Saroglou's 2015 primary text gives asymptotic upper root \(\pi e/2\), sharper than the older Lutwak–Yang–Zhang root \(e^{3/2}\). The focused primary comparison and its limitations, including unavailable Saroglou 2011 full text, are in `literature.md`. No priority or unrestricted optimality claim is made.

All work is in a separate temporary math directory. The saved old project was neither inspected nor resumed. No publication or push was performed.
