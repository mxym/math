# Independent internal mathematical review: true-area ellipsoid triangles

**Verdict: PASS on the frozen local statements (2026-11-19).** I independently derived the higher-dimensional quadratic variation, checked the uniform remainder also at pole contacts, and recovered the planar fourth-order term by a different angular decomposition. This is an AI-assisted internal review, not external peer review, proof formalization, or a priority determination.

Exact documents reviewed:

- `PROOF-ALL.md`, SHA-256 `daf04d6e8efd8619b7a3b0b2cecb57631310437a24289866da82169cbeec65d8`;
- `PROOF-PLANAR.md`, SHA-256 `cd4679ee29b2aa180fecdc12548ecc077614ed63110affbc7bc152fa1248f4e3`.

## True surface measure and dimension at least three

For the stretched sphere \(A S^{d-1}\), \(A=e^{tH/2}\) and \({\rm tr} H=0\), the normal-cofactor surface Jacobian is \(\det(A)\|A^{-T}x\|\), giving first density variation \(g=-x^THx/2\); the second density coefficient has mean zero. This effect is absent for homeoid sampling. In the frame \(X=cu+se,\ Y=-cu+se\) with \(s^2=1-c^2\), the metric cap axis moves as \(n'(0)=v=Hu-(u^THu)u\). At the first endpoint the nondisjointness issue does not arise: there can be at most one obtuse angle, and right angles have zero probability. The cap uses CDF, not survival, in the nonobtuse event. For the linear and quadratic terms in its latitude parameter, the averaged linear shift is zero, the mean of its second-order shift is \(-c\|v\|^2/2\), and the mean square first-order shift is \((1-c^2)\|v\|^2/(d-1)\). Thus, with \(A_0=3{\rm tr}(H^2)/[(d+2)(d-1)]\), the acute metric term is \(-A_0(d-2)E[cf(c)]\).

For the mixed term, the product \(g(X)+g(Y)\) is even in transverse \(e\), annihilating the odd moving-endpoint cross terms. Latitude integration of \(-h(n)(dr^2-1)f(r)/[2(d-1)]\) up to \(z\) gives \(h(n)z(1-z^2)f(z)/[2(d-1)]\), zero at the lower endpoint. One has \((h(n))'=2\|v\|^2\), resulting in \(+A_0 E[c(1-c^2)f(c)]\). The combined scalar is strictly negative: for \(d=3\) only the strictly signed residual \(-A_0 E[c^3 f(c)]\) remains; for \(d>3\) there is additionally \(-(d-3)A_0 E[c f(c)]\). The pure second-order weights at fixed metric comprise only three identical pair covariances: condition on \(a=X\cdot Y\) and use the centered quadratic \(P_2(a)=(da^2-1)/(d-1)\). In the third-point acute test, the endpoint obtuse caps have probabilities \(1-F(c)\) each; the third-vertex cap has probability \(1-F(s)\), as \((X-Z)\cdot(Y-Z)=1+a-(X+Y)\cdot Z\). Disjointness and symmetry \(a\leftrightarrow-a\) yield a covariance with \(F(c)+F(s)\), decreasing in \(|a|\) since \(f(x)/x\) is strictly decreasing. Its sign is nonpositive.

At a pole in \(d>3\), \(|z'|\le C\sqrt{1-z^2}\). Consequently \(f'(z)(z')^2\) and \(f(z)z''\) tend uniformly to zero, also in dimension four. At exact contact, \(1-z^2=O((t-t_0)^2)\) and \(|f(z)z'|=O(|t-t_0|^{d-2})\), proving that the second derivative exists there and is zero. For \(d=3\) the CDF restricted to \([-1,1]\) is linear. The normalized unit traceless matrices, frames and heights form a compact parameter set, hence the continuous second derivative supplies a uniform remainder. The cap weighted by the second density variation varies by a bounded multiple of the maximal projection density times the strip width. Orthogonal averaging gives \(E\|v\|^2={\rm tr}(H^2)/(d+2)\), so the strictly negative margin is uniform in a normalized direction. Every near-sphere ellipsoid is represented modulo similarity.

As an independent arithmetic check, `check_odd.py` uses \(c^2\sim {\rm Beta}(m,m)\), \(d=2m+1\), rather than quadrature. In \(d=3\) the metric, mixed, and pair coefficients divided by \({\rm tr}(H^2)\) are respectively \(-1/10,1/25,-1/350\), giving \(-11/175\). Exact signs were also reproduced for odd \(d=5,\ldots,23\); the proof, not those checks, covers all \(d\ge3\).

## A different planar calculation without a clipped cap endpoint

Let \(a=e^{t/2}, b=e^{-t/2},\rho=\tanh t\). Let \(\alpha\) be the circle parameter of the designated vertex, and write the other two as \(\alpha+2u,\alpha+2v\) modulo \(2\pi\), ordered \(0<u<v<\pi\). The chord out of \(\alpha\) to \(\alpha+2u\) is exactly \(2\sin u\,(-a\sin m,b\cos m)\), \(m=\alpha+u\). Tangent direction is strictly increasing in its parameter, advancing by \(\pi\) in any interval of parameter length \(\pi\). Its next perpendicular at parameter \(m+h\) has \(h=\pi/2+\beta(m)\), where direct dot product gives
\[
 \tan\beta=\rho\sin(2m)/(1-\rho\cos(2m)),\qquad
 \beta=-\arg(1-\rho e^{2im})=\sum_{k\ge1}\rho^k\sin(2km)/k .
\]
Thus the angle at the anchor is obtuse precisely for \(v>u+h\). Write \(r=v-u-h,\ L=\pi/2-\beta\), and let \(w(x)=\sqrt{1-\rho\cos 2x}/\operatorname{avg}\sqrt{1-\rho\cos 2x}\). After replacing \(\alpha\) by \(m-u\), the integral is over the *single* triangle \(u,r\ge0,\ u+r\le L\):
\[
 J(\rho)=E_m\int_{u+r\le L}w(m-u)w(m+u)w(m+u+2\beta+2r)\,du\,dr ,
 \qquad p=1-6J/\pi^2 .
\]
Here \(m\) is circle-uniform and the two coordinates inside the integral are nonnegative. The factor accounts for both orderings, both doubled angles, and the three mutually exclusive obtuse-vertex events. Rescale by \(L\) to a fixed triangle; all factors and \(L\) are real analytic near \(\rho=0\), uniformly on this compact domain.

For Fourier indices \(j,k,l\) of the three weights put \(M=j+k+l,A=-j+k+l,B=2l\). In the integral the factor is \(e^{2iMm}e^{2iB\beta}I_{A,B}(L)\), where
\(I_{A,B}(L)=\int_{u+r\le L}e^{2iAu+2iBr}\,du\,dr\). Integrate the exponentials directly (including \(A=B, A=0, B=0\)); Taylor-expand at \(L=\pi/2\) and select zero Fourier frequency in \(m\). This gives through degree four exactly
\[
 J(\rho)=\pi^2/8+(37/96)\rho^4+O(|\rho|^5).
\]
The included `check_planar.py` computes this finite arithmetic by normalized binomial Fourier coefficients and exact symbolic arithmetic (SymPy); its validation uses explicit exceptions, not removable assertions. Consequently \(p=1/4-37t^4/(16\pi^2)+O(|t|^5)\). Independently, in the frozen cap proof I checked the extension as an odd function and the sign restoration for \(0\le\theta<|\alpha|\): the unclipped fourth-order coefficient \(97/192\) and the boundary coefficient \(17/64\) sum to \(37/48\); the quadratic contributions cancel. These two derivations agree while treating the moving domain differently.

## Scope and closest primary sources

- The exact planar sampling model was already asked about [in December 2024](https://math.stackexchange.com/questions/5014676/probability-that-triangle-on-ellipse-is-acute); Christophe Boilley's January 2025 answer gives an explicit conditional orthogonal-chord/arc integral, not just a simulation. Credit this integral precedent. No quartic expansion, local comparison proof or solution at every axis ratio was identified there.
- [Hall (1982)](https://doi.org/10.2307/3213533) uses Lebesgue measure on the *solid* ball; [Khan](https://arxiv.org/abs/1704.05913) studies related interior-volume maximization. Neither states these surface-law assertions. Existing [ProofAtlas work](https://www.proofatlas.ai/collaboration/halls-random-triangle-conjecture/) on ellipse comparisons must likewise be read with its sampling convention.
- [Akopyan, Edelsbrunner and Nikitenko](https://doi.org/10.1080/10586458.2021.1980459), Lemma 4, gives the exact spherical \(d=3\) baseline; their ellipsoid treatment explicitly uses homeoid density, the affine pushforward of uniform spherical measure, not true area. The circle baseline \(1/4\) is classical.
- The owner's PRs [#179](https://github.com/mxym/math/pull/179) (radial laws) and [#201](https://github.com/mxym/math/pull/201) (log-stretch under an affine pushforward) should be cited as related, not treated as the true-area theorem. The surface law's Jacobian produces a genuine mixed variation; in dimension two it cancels the quadratic metric response. Keyword and bibliographic searches including ellipse perimeter, boundary/arclength law, higher-dimensional ellipsoidal surface, Hall, and stretch/aspect-ratio variations did not identify matching strict local theorems or coefficients; this is not a priority guarantee.

The two frozen results are **local within the family of ellipsoids**. They do not imply global ellipsoidal extremality or address all convex hypersurfaces, and they do not settle Hall's volume-sampling conjecture. No publication or external review is represented by this report.
