# Smooth positive laws with the same halfspace depth and any prescribed finite number of moments

For a Borel probability \(M\) on \(\mathbb R^d\), let
\[
D_M(x)=\inf_{u\in S^{d-1}}M(H(u,u\cdot x)),\qquad H(u,t)=\{y:u\cdot y\ge t\}.
\]

**Theorem.** For every \(d\ge2\) and integer \(k\ge1\), there are two distinct probabilities on \(\mathbb R^d\) with everywhere strictly positive \(C^\infty\) densities and finite absolute \(k\)-th moments such that their mixed moments up to total degree \(k\) agree, and their halfspace depth functions agree at every point.

Thus the existence of the first moment does not ensure characterization by Tukey depth. This answers the expectation subquestion of [Nagy–Schütt–Werner, *Data depth and floating body*, Problem 12 in the arXiv version](https://arxiv.org/pdf/1809.10925#page=43), also posed in [Nagy, GeMS, Problem 1](https://gems.karlin.mff.cuni.cz/pdf/Depth_problems_update.pdf). The pair can depend on \(k\): no single all-orders pair, compactly supported example, or complete classification of laws determined by depth is asserted.

## 1. A neighborhood of halfspaces irrelevant to all depth infima

Let \(T\) be normalized volume on the simplex with vertices \(0,e_1,\ldots,e_d\), translated so the plane \(y_d=0\) bisects it. For example translate by \(-(1-2^{-1/d})e_d\), since the unshifted upper coordinate tail on \([0,1]\) is \((1-t)^d\). Then
\[
\sup_x D_T(x)\le (d/(d+1))^d\le 4/9.
\]
Indeed depth is zero outside the simplex; inside it some barycentric coordinate \(a_i(x)\) is at least \(1/(d+1)\), and the cap \(a_i(y)\ge a_i(x)\) has mass \((1-a_i(x))^d\). The second inequality follows by retaining just the first three terms of \((1+1/d)^d\), which sum to \(2+(d-1)/(2d)\ge9/4\).

Choose integers \(A>d+k\) and \(N>A\). Let \(R\) have density \(c_A(1+|y|^2)^{-A/2}\) where \(c_A\) normalizes the integral. Convolve \(T\) with a nonnegative, compactly supported smooth approximate identity; then mix with \(R\) with a sufficiently small positive weight \(\lambda\). One can choose the smoothing scale and \(\lambda\) so the resulting probability \(P\) satisfies \(\|P-T\|_{\rm TV}<1/100\) (here TV is the supremum of the probability differences on events), since the simplex density is in \(L^1\). Its density \(p\) is \(C^\infty\), has finite absolute \(k\)-th moment, and is bounded below everywhere by \(\lambda c_A(1+|y|^2)^{-A/2}\). By applying the TV bound to all halfspaces,
\[
\sup_x D_P(x)\le4/9+1/100<46/100.
\tag{1}
\]
For \(u=\pm e_d\), \(P(H(u,0))>49/100\). The map \((u,t)\mapsto P(H(u,t))\) is continuous: indicators converge pointwise away from the limiting boundary hyperplane, which has \(P\)-mass zero. Thus there are an antipodally symmetric open set \(U\) containing \(\pm e_d\), and \(b>0\), such that
\[
P(H(u,t))>48/100\qquad (u\in U,\ |t|<b).
\tag{2}
\]
The set \(U\) may be chosen as two small opposite spherical neighborhoods.

## 2. A signed perturbation whose projected tails change only there

Choose a nonzero, real, even \(C^\infty\) angular function \(h\) on \(S^{d-1}\), supported in \(U\); even means \(h(-u)=h(u)\). Choose a nonzero, nonnegative, even \(\psi\in C_c^\infty((-b,b))\). Choose an even integer \(m>N\), and set \(g=\psi^{(m)}\). It is nonzero and even and \(\int g=0\). Use the Fourier transform \(\widehat f(\xi)=\int e^{-i x\cdot\xi} f(x)\,dx\). Set \(F(0)=0\) and
\[
F(\xi)=h(\xi/|\xi|)\widehat g(|\xi|)\quad(\xi\ne0).
\]
This is a nonzero, real, even function. Its derivatives of order \(j\le N\) away from \(0\) are \(O(|\xi|^{m-j})\) near zero: use \(\widehat g(r)=(ir)^m\widehat\psi(r)\), bounded derivatives of \(\widehat\psi\) near zero, and homogeneity for derivatives of \(h(\xi/|\xi|)\) and \(|\xi|\). Since \(m>N\), the extension is \(C^N\) with all derivatives through order \(N\) zero at the origin (induct on derivatives by difference quotients). At infinity, all these derivatives decrease faster than every power because \(\widehat g\) is Schwartz.

Let \(f(x)=(2\pi)^{-d}\int e^{ix\cdot\xi}F(\xi)\,d\xi\). It is real and \(C^\infty\) because \(F\) times any polynomial is integrable. Integration by parts \(N\) times in any coordinate \(\xi_j\), using \(\partial_{\xi_j}^N F\in L^1\) and the decay at infinity, gives \(|x_j|^N|f(x)|\le (2\pi)^{-d}\|\partial_{\xi_j}^N F\|_1\). Together with boundedness of \(f\), this yields
\[
|f(x)|\le C(1+|x|)^{-N}.
\tag{3}
\]
In particular \(f\) is integrable with finite absolute \(k\)-th moment, and \(\widehat f=F\) everywhere by Fourier inversion and continuity. Since \(F\not\equiv0\), \(f\ne0\). All signed mixed moments of \(f(x)\,dx\) of order at most \(k\), including the integral, are zero: they are constant multiples of the corresponding derivatives of \(F\) at \(0\).

For every unit \(u\), the pushforward of \(f(x)\,dx\) by \(x\mapsto u\cdot x\) is exactly \(h(u)g(t)\,dt\): its one-dimensional Fourier transform is \(F(su)=h(u)\widehat g(s)\) for every real \(s\), by the two evenness conditions and the value at zero. Use uniqueness of the Fourier transform of finite signed measures on \(\mathbb R\). Consequently the signed halfspace mass is
\[
\int_{H(u,t)} f(x)\,dx=h(u)\int_t^\infty g(v)\,dv.
\tag{4}
\]
It is exactly zero if \(u\notin U\) or \(|t|\ge b\), including \(t\le-b\) because \(\int g=0\).

## 3. Positivity and preservation of every infimum

By (3), \(N>A\), and the lower bound for \(p\), the ratio \(|f|/p\) is bounded. Choose \(\varepsilon>0\) small enough that \(\varepsilon|f|\le p/2\) pointwise and \(\varepsilon\|f\|_1<1/100\). The two densities \(p\pm\varepsilon f\) are smooth and strictly positive, integrate to one, are distinct, and have the finite, matching moments asserted. Denote their laws by \(P_\pm\).

At any \(x\), partition the halfspaces \(H(u,u\cdot x)\) into those with \((u,u\cdot x)\) in the wedge \(U\times(-b,b)\) and the rest. All halfspaces in the wedge have mass strictly greater than \(47/100\) for both perturbed laws, by (2). Their original masses exceed \(48/100\). All halfspaces outside the wedge have exactly unchanged mass, by (4). Since \(D_P(x)<46/100\) by (1), the complement of the wedge must contain a sequence with masses approaching \(D_P(x)\); in particular it is nonempty. Its infimum is \(D_P(x)\) also for \(P_\pm\), and no wedge halfspace lowers this infimum. Thus \(D_{P_+}(x)=D_P(x)=D_{P_-}(x)\) for every \(x\), as required.
