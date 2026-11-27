# Exact wide-noise bifurcation of variance-maximizing shifts on the triangular lattice

Let \(L\) be a planar triangular lattice, and let \(X_{t,z}\) be the discrete Gaussian on \(L\) with masses proportional to \(e^{-t|x-z|^2}\). The precision \(t>0\) tends to zero in the wide limit. Write
\[
V_t(z,u)=\operatorname{Var}(u\cdot X_{t,z}),\qquad z\in\mathbb R^2/L.
\]
Let \(w_1,w_2,w_3\) select one direction from each opposite pair of shortest dual vectors, with \(w_1+w_2+w_3=0\), and let \(\ell=|w_i|\). For a nonzero \(u\), change its sign and permute the directions so that
\[
(w_1\cdot u,w_2\cdot u,w_3\cdot u)=r(1+\rho,-1,-\rho),\quad r>0,\quad 0\le\rho\le1.
\]
Indeed three numbers summing to zero have absolute values \(r(1+\rho),r,r\rho\). Write \(\eta=e^{-\pi^2\ell^2/t}\). In angle coordinates \(\theta_i=2\pi w_i\cdot z\), one has \(\sum_i\theta_i=0\bmod 2\pi\).

**Theorem.** There is an analytic threshold \(\rho_*(\eta)\), defined near \(\eta=0\), such that for all sufficiently small positive \(\eta\), uniformly for all directions \(u\):
- For \(\rho\le\rho_*(\eta)\), the unique maximizing shift (modulo \(L\)) is the half-lattice point \((\theta_1,\theta_2,\theta_3)=(\pi,\pi,0)\).
- For \(\rho>\rho_*(\eta)\), there are exactly two maximizing shifts, interchanged by inversion and neither a half-lattice point.
- At the threshold the maximum has one strictly negative transverse second derivative and a strictly negative reduced fourth-order coefficient in the other direction.

The limiting threshold \(\rho_0=\rho_*(0)\) is the unique root in \((0,1)\) of \(1/\rho^2=1+(1+\rho)^{-2}\), about \(0.8832035\). The first correction is positive:
\[
\rho_*(\eta)=\rho_0+\kappa\eta+O(\eta^2),\qquad \kappa\simeq2.3075054,
\]
with an explicit formula below. In particular the finite-width maximizer is still exactly the half-lattice point at the limiting critical direction \(\rho=\rho_0\).

If the direction is optimized as well, precisely the three nonzero half-lattice shifts realize the maximum on the torus for all sufficiently wide laws. At \((\pi,\pi,0)\) the maximizing line is perpendicular to \(w_3\), and correspondingly at its permutations. For unit \(u\) the resulting value is
\[
\max_{z,u:\ |u|=1}V_t(z,u)=\frac1{2t}+\frac{3\pi^2\ell^2}{t^2}
\bigl(\eta+2\eta^2+O(\eta^3)\bigr).
\]
Thus a fixed direction and the optimal direction need not have the same maximizing shift.

## 1. Theta Hessian and the leading phase optimization

Let \(p=(1+\rho,-1,-\rho)\), \(D=\sum_i p_i\partial_{\theta_i}\) (tangent to the phase constraint), and \(S=\sum_i\cos\theta_i\). Differentiating the log partition gives
\[
V_t(z,u)=\frac{|u|^2}{2t}+\frac1{4t^2}\partial_u^2\log\sum_{v\in L}e^{-t|v-z|^2}.
\]
Poisson summation leaves an angle-independent prefactor times the reciprocal theta density
\[
P_\eta(\theta)=\sum_{m,n\in\mathbb Z}\eta^{m^2+n^2-mn}e^{i(m\theta_1+n\theta_2)}
=1+2\eta S+O(\eta^3).
\]
The formula uses the angle \(120^\circ\) between \(w_1,w_2\). The shell after squared length \(\ell^2\) has squared length \(3\ell^2\), since \(m^2+n^2-mn\equiv(m+n)^2\bmod3\), so it cannot equal 2. The series and all fixed angle derivatives converge locally uniformly as analytic functions of \(\eta\) near zero. For \(\eta>0\) the shift objective, after subtracting the constant term and dividing by \(2\pi^2r^2\eta/t^2\), is
\[
F_\eta=\frac{D^2\log P_\eta}{2\eta}=D^2 S-2\eta\bigl[(DS)^2+S D^2 S\bigr]+O(\eta^2).
\tag{1}
\]
All remainders are analytic and uniform on the compact phase torus and \(\rho\in[0,1]\).

Put \(a=\rho^2,\ b=1,\ c=(1+\rho)^2\). At \(\eta=0\), maximize \(-c\cos\theta_1-b\cos\theta_2-a\cos\theta_3\). Fix \(\theta_3=x\); the maximum over the other two phases is
\[
f_0(x)=-a\cos x+\sqrt{b^2+c^2+2bc\cos x}.
\tag{2}
\]
For \(b=c\) the only phase where the square root vanishes is \(x=\pi\); this occurs at \(\rho=0\) and is not a maximum. As a function of \(\cos x\) otherwise, (2) is strictly concave. Its maximizing cosine is 1 if \(a\le bc/(b+c)\). For \(a>bc/(b+c)\) it is the interior value
\[
\cos x=\frac{(bc/a)^2-b^2-c^2}{2bc}.
\]
The other endpoint cannot be the maximizer because \(a\le b\le c\) implies \(a<bc/|b-c|\) when \(b\ne c\). At an optimizing \(x\), the \(\theta_1,\theta_2\) maximizer is unique, obtained by aligning the nonzero vector sum of its two phasors. Thus the leading maxima are exactly as in the theorem at \(\eta=0\). The condition \(a>bc/(b+c)\) is the strict reversal of \(1/\rho^2\ge1+(1+\rho)^{-2}\) (with infinity at \(\rho=0\)). The difference of the two sides decreases strictly through zero. For example, at \(\rho=1\) the maximizing pair has \(\cos\theta_3=-1/8\) and \(\cos\theta_1=-31/32\); the limiting centers are not half-lattice points.

Away from \(\rho_0\) these leading maxima are nondegenerate: the fixing-\(x\) transverse Hessian is strictly negative and the reduced second derivative is strictly negative at a maximum by (2). A uniform compactness gap outside their neighborhoods, followed by the implicit function theorem near each maximum, proves the exact statement away from the critical direction for all sufficiently small \(\eta\). In the half-lattice regime the location is fixed exactly by inversion, and in the two-point regime the two isolated maxima have equal value by inversion.

## 2. The critical direction and its first correction

For \(\rho\) near \(\rho_0\), near \((\pi,\pi,0)\) use \(x=\theta_3\) and the transverse phase as the other coordinate. The transverse Hessian is negative at the limiting point, so the analytic implicit function theorem gives its unique nearby maximizing value for each small \(x\). Let \(f_{\rho,\eta}(x)\) be this reduced objective. It is even in \(x\) by inversion, and the transverse optimum at \(x=0\) is the original half-lattice point. Its reduced curvature at \(\eta=0\) is
\[
g(\rho)=f_{\rho,0}''(0)=a-\frac{bc}{b+c}.
\]
It vanishes at \(\rho_0\), with \(g'(\rho_0)>0\) by the strict derivative of the reciprocal condition. At that point the coefficient of \(x^4\) in (2) is \(-b^2c^2/[8(b+c)^3]<0\). This follows by expanding the strictly concave function of \(\cos x\) about 1, where its first derivative is zero.

The tangent to the transverse-optimized curve at the critical point is
\[
v=(-b/(b+c),-c/(b+c),1).
\]
It is a null vector of the leading Hessian. Consequently the first variation of the reduced curvature in \(\eta\) is just the second derivative of the \(\eta\) coefficient in (1) along \(v\): the terms from change of tangent vanish by the null-vector identity. All calculations below are at \(\rho=\rho_0\). Write \(\epsilon=(-1,-1,1)\) for the phase cosines at the half-lattice point and put
\[
K=b+c-a,\qquad A=\sum_i\epsilon_i v_i^2=\frac{2bc}{(b+c)^2},\qquad
B=\sum_i\epsilon_i p_i v_i=-\rho\left(1+\frac{1+\rho}{b+c}\right).
\]
At the base point \(S=-1,DS=0,D^2S=K\). Along \(v\), the first derivative of \(DS\) is \(-B\), the second derivative of \(S\) is \(-A\), and the second derivative of \(D^2S\) is zero by the null identity. The correction to the reduced curvature is therefore \(h=2KA-4B^2\). Since \(a=bc/(b+c)\), \(KA=2a(1-a/(b+c))<2a\) and \(B^2>a\), hence \(h<0\). The unique analytic curve solving \(f_{\rho,\eta}''(0)=0\) has
\[
\kappa=-\frac{h}{g'(\rho_0)}>0,\qquad
g'(\rho_0)=2\rho_0-\frac{2(1+\rho_0)}{[1+(1+\rho_0)^2]^2}.
\]
This gives the stated shift and signs. The numerical values are descriptive; strictness follows from the inequalities above.

For completeness, at the threshold no additional maxima can appear elsewhere. At the central limiting parameters the phase maximum is unique, so all perturbed global maxima in a suitably small parameter rectangle stay in its neighborhood by uniform continuity and a compactness gap. There the reduced derivative is \(x\) times an analytic function of \(x^2\), whose value at zero is \(f_{\rho,\eta}''(0)\), and whose derivative in \(x^2\) is strictly negative near zero by the quartic coefficient. On the nonpositive-curvature side only \(x=0\) can maximize. On the positive side, two symmetric simple nonzero maxima emerge, and \(x=0\) cannot be a maximum. This proves the exact alternatives, including the boundary. A finite compact covering of the \(\rho\) interval makes the small-\(\eta\) restriction direction-independent.

## 3. Optimizing over unit directions

Return in (1) to the actual coefficients \(p_i=w_i\cdot u\) for \(|u|=1\). The leading objective has the universal bound
\[
-\sum_i p_i^2\cos\theta_i\le \sum_i p_i^2=\frac32\ell^2.
\]
Equality requires \(\cos\theta_i=-1\) whenever \(p_i\ne0\). All three phases cannot equal \(\pi\bmod2\pi\) under their sum constraint. Thus equality occurs exactly when one \(p_i=0\), the other phases are \(\pi\), and the zero-weight phase is 0. Near each such pair (shift and direction), the optimized leading angular objective is \((3/2)\ell^2-2p_i^2\), with a strictly negative direction Hessian at \(p_i=0\); the phase Hessian is also negative definite. The cross derivatives vanish at the half-lattice shift (it is stationary in phases for all directions). Hence the leading joint maxima are nondegenerate.

In the perturbed problem each such half-lattice point remains stationary in phases by inversion. Reflection across the direction perpendicular to its exceptional \(w_i\) fixes that shift modulo the lattice and forces stationarity in the directional angle as well. Uniform compactness followed by nondegenerate local continuation therefore leaves exactly these joint maximizing pairs for all sufficiently small \(\eta>0\). At one such pair \(DS=0\), \(S=-1\), and \(D^2S=(3/2)\ell^2\). Equation (1) gives the expansion in the theorem.

## Scope and known comparisons

[Regev–Stephens-Davidowitz, Proposition 3.1 and Corollary 3.2](https://arxiv.org/abs/1502.04796) analyze the log-theta Hessian and prove that the centered covariance is a minimum in positive-semidefinite order. The present extremum is the **maximum** in a specified direction; it need not be at an unweighted theta minimum or an obvious symmetry shift. [Faulhuber's heat kernel work](https://doi.org/10.1007/s11139-019-00224-2) concerns the hexagonal temperature profile and its values, not the maximizing shifts of a directional log-Hessian. The leading triangle energy in (2) has the familiar phase constraint of a classical three-spin model; the fourth-order normal form and the positive displacement of the finite-width threshold are for the full analytic theta density, not just its first-shell approximation. The narrow limit is a different problem, covered in [the Delaunay covariance note](delaunay-gaussian-covariance.md). No exact phase classification for intermediate widths or other lattices is asserted. The [replay](verify-triangular-lattice-gaussian-variance-bifurcation.js) checks the algebraic thresholds and numerically spot-checks the analytic perturbation, without using floating optimization as proof.
