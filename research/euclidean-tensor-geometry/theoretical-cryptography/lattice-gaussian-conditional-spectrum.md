# The conditional-expectation spectrum of a lattice Gaussian

This is a theorem about the law obtained by restricting a positive Gaussian density to a product of two full-rank lattice cosets. It compares that law with the corresponding continuous Gaussian, on the same real spaces. It does not compare implementations, prove the hardness of a learning problem, or give a method for solving such a problem.

**Results.** Every squared singular value of conditional expectation obeys an explicit, translation-uniform two-sided theta bound. The leading nontrivial singular value is closer to the lattice law's ordinary linear canonical correlation: the nonlinear improvement is at most quadratic in the conditional-mean error, with an explicit exponential rate as the mesh vanishes. In the centered two-coordinate model, this gives a sharp correction, of either sign, to the continuous maximal correlation. The transition value has exactly the continuous correlation at *every* width. At the opposite endpoint of narrow Gaussians, the same transition separates decay to zero from convergence to one.

## 1. Setup and all-mode estimate

Separate invertible linear coordinate changes allow the continuous law to be written with zero means and covariance
\[
 C=\begin{pmatrix}I&R\\R^T&I\end{pmatrix}, \qquad \|R\|<1 .
\]
Its marginals have standard Gaussian densities \(\phi_X,\phi_Y\), and its joint density is \(p(x,y)\). Its law \(\mu_h\) on \((hL_X+t_X)\times(hL_Y+t_Y)\), \(h>0\), assigns mass proportional to \(p(x,y)\). Translations \(t_X,t_Y\) are arbitrary. Let \(s_j(h)\), \(j\ge0\), be the singular values, decreasing and with multiplicities, of \(g\mapsto\mathbb E_{\mu_h}[g(Y)\mid X]\) between the two marginal \(L^2\) spaces. Include the constant mode \(s_0(h)=1\) and append zeros in finite-rank cases. The HGR maximal correlation is \(s_1(h)\).

For the moment suppose both dimensions equal \(d\). Apply independent orthogonal changes of coordinates to make \(R=\operatorname{diag}(r_i)\), \(0\le r_i<1\); the lattices are transformed along with the variables. Write \(s_j\) for the decreasing list of products \(\prod_i r_i^{k_i}\), with integer \(k_i\ge0\) and \(0^0=1\). This is the continuous singular-value list. Choose any \(0\le u_i,v_i<1\) with \(u_iv_i=r_i\), for example \(u_i=v_i=\sqrt{r_i}\). For positive definite \(B\), let
\[
 \Theta_L(B,h)=\sum_{\xi\in L^*\setminus\{0\}}
        \exp(-2\pi^2\xi^TB\xi/h^2).
\]
Define
\[
 \begin{split}
 B_X&=\operatorname{diag}((1-u_i^2)/(1+u_i^2)),
 &B_Y&=\operatorname{diag}((1-v_i^2)/(1+v_i^2)),\\
 e_X&=\Theta_{L_X}(B_X,h), & e_Y&=\Theta_{L_Y}(B_Y,h),\\
 b_X&=\Theta_{L_X}(I-RR^T,h),&b_Y&=\Theta_{L_Y}(I-R^TR,h),\\
 E&=e_X+e_Y+e_Xe_Y .
 \end{split}
\]
For all \(j\ge0\),
\[
 \frac{\max(0,s_j^2-E)}{(1+b_X)(1+b_Y)}
 \ \le\ s_j(h)^2\ \le\
 \frac{s_j^2+E}{(1-b_X)(1-b_Y)}
 \quad\text{if }b_X,b_Y<1.
 \tag{1}
\]
The lower bound holds even when either \(b\) is at least one. In particular, the convergence of the squared spectrum is exponentially fast in \(1/h^2\), uniformly over translations and over the mode index. No mode cutoff is used.

If dimensions differ, one can append independent scalar standard normals to the smaller continuous space and restrict each added coordinate to \(hM\mathbb Z\) for any \(M>0\). The enlarged conditional-expectation operator is the tensor product of the original operator with a rank-one constant-mode map, so it has the same nonzero singular values; use (1) in the enlarged dimensions. One can alternatively omit dummy coordinates by treating their one-variable Gaussian factors separately in the proof.

**Proof.** For \(0\le a<1\) let \(K_a\) be the symmetric kernel \(p_a(x,y)/\sqrt{\phi(x)\phi(y)}\) on ordinary Lebesgue space, where \(p_a\) is the standard bivariate normal density with correlation \(a\). It is a positive operator with orthonormal Hermite functions as eigenvectors, eigenvalues \(a^k\). The identity follows by the generating function for probabilists' Hermite polynomials: if \(Y\mid X=x\) has mean \(ax\) and variance \(1-a^2\), then \(\mathbb E[\exp(zY-z^2/2)\mid X=x]=\exp(azx-(az)^2/2)\), so conditional expectation maps the \(k\)-th normalized Hermite polynomial to \(a^k\) times itself. Multiplication by \(\sqrt{\phi}\) changes to Lebesgue space. Thus \(K_aK_b=K_{ab}\), and coordinate products give \(K_R=K_UK_V\). In one dimension,
\[
 K_a(x,z)=\mathrm{const}_a\exp\!\left(
 -\frac{1+a^2}{4(1-a^2)}(x^2+z^2)+\frac{a}{1-a^2}xz
 \right).
\]

Let \(S_X\) send a latent \(L^2(\mathbb R^d)\) function \(f\) to evaluations of \(K_Uf\) on \(hL_X+t_X\), multiplied by \(\sqrt{h^d\det L_X}\). Define \(S_Y\) with \(V,L_Y,t_Y\). Composition \(S_XS_Y^*\) is precisely the sampled continuous kernel \(K_R\) with the two quadrature-volume factors. The kernel of \(S_X^*S_X\), for latent points \(z,z'\), is the rectangular lattice quadrature of \(K_U(x,z)K_U(x,z')\). As a function of \(x\), this integrand is a constant times a translated Gaussian of covariance \(B_X\). Poisson summation therefore bounds the absolute quadrature error by \(e_X\) times the exact integral for **every** \(z,z'\). The continuous integral kernel is \(K_{U^2}\), nonnegative pointwise and of operator norm one. For arbitrary \(f,g\), the error bilinear form is bounded by \(e_X\langle |f|,K_{U^2}|g|\rangle\). Hence, putting \(\Gamma_X=K_{U^2}\) and \(\widetilde\Gamma_X=S_X^*S_X\),
\[
 \|\widetilde\Gamma_X-\Gamma_X\|\le e_X,\qquad
 \|\widetilde\Gamma_Y-\Gamma_Y\|\le e_Y.
\]
These sampling operators are Hilbert–Schmidt: integrating \(K_U(x,z)^2\) over \(z\) gives \(K_{U^2}(x,x)\), a Gaussian in \(x\), whose lattice sum is finite for fixed \(h\). Compare the squared singular values of \(S_XS_Y^*\), first replacing \(S_Y\widetilde\Gamma_XS_Y^*\) by \(S_Y\Gamma_XS_Y^*\), with norm error at most \(e_X(1+e_Y)\). The latter has the same nonzero eigenvalues with multiplicities as \(\Gamma_X^{1/2}\widetilde\Gamma_Y\Gamma_X^{1/2}\). Replacing \(\widetilde\Gamma_Y\) by \(\Gamma_Y\) adds error at most \(e_Y\). The final operator is \(K_{R^2}\), by the same semigroup identity. The min-max principle bounds each eigenvalue difference by \(E\).

To recover conditional expectation for \(\mu_h\), set
\[
 M_X(x)=h^d\det L_Y\sum_{y\in hL_Y+t_Y}p(y\mid x),\quad
 M_Y(y)=h^d\det L_X\sum_{x\in hL_X+t_X}p(x\mid y).
\]
On counting-measure spaces the kernel of conditional expectation after the marginal \(L^2\) isometries is
\[
 \frac{\mu_h(x,y)}{\sqrt{\mu_{h,X}(x)\mu_{h,Y}(y)}}=
       M_X(x)^{-1/2}(S_XS_Y^*)(x,y)M_Y(y)^{-1/2}.
\]
The joint normalizing constant cancels. Poisson summation gives \(|M_X-1|\le b_Y,\ |M_Y-1|\le b_X\). Each positive factor is bounded and bounded away from zero, even outside the range \(b_X,b_Y<1\): the conditional theta mass is continuous, periodic and positive in its center. Multiplicative comparison of singular values using these diagonal matrices proves (1).

## 2. A sharper bound on the top nonconstant mode

Let \(\ell_h\) be the largest absolute correlation obtainable using *linear* functions of \(X\) and \(Y\), with their discrete means subtracted. Define
\[
 \kappa=2\pi^2\min\left\{
  \min_{0\ne\xi\in L_X^*}\xi^T(I-RR^T)\xi,\
  \min_{0\ne\eta\in L_Y^*}\eta^T(I-R^TR)\eta
 \right\}.
\]
As \(h\downarrow0\), for fixed \(R,L_X,L_Y\), uniformly over both translations,
\[
 0\le s_1(h)-\ell_h
       \le O_{R,L_X,L_Y}\!\left(h^{-2}\exp(-2\kappa/h^2)\right).
 \tag{2}
\]
There is no assumption that the largest continuous canonical correlation is simple. The exponent uses the true conditional covariances, not the generally smaller Gaussian covariances used to bound the whole spectrum in (1).

For a conditional normal of mean \(a\) and covariance \(\Sigma\), the shift of the lattice-restricted mean from \(a\) is \(\Sigma\nabla_a\log M(a)\), by differentiating its mass. Poisson summation differentiated once bounds this uniformly in \(a\) and the lattice translation by \(O(h^{-1}\exp[-2\pi^2\min_{\xi\in L^*\setminus0}\xi^T\Sigma\xi/h^2])\); the constant is finite because Gaussian sums with polynomial weights converge. The actual joint covariance converges uniformly to \(C\) by two differentiations of joint mass; the discrete marginal centering and normalization of linear functions therefore change the estimates by bounded factors for small \(h\). Subtracting unconditional means yields
\[
 \|T_h g - \Pi_X T_h g\|\le O(h^{-1}e^{-\kappa/h^2})\,\|g\|
 \quad (g\text{ centered linear}),
 \tag{3}
\]
where \(T_h:L_0^2(Y)\to L_0^2(X)\) is conditional expectation and \(\Pi_X\) is the linear-subspace projection. The same estimate holds for \(T_h^*\).

For details of why the improvement is quadratic, use the self-adjoint dilation \(H=\left(\begin{smallmatrix}0&T_h\\T_h^*&0\end{smallmatrix}\right)\) and let \(\Pi=\Pi_X\oplus\Pi_Y\). The norms of the off-diagonal blocks of \(H\) relative to \(\Pi\) are at most \(\delta=O(h^{-1}e^{-\kappa/h^2})\) by (3). If \(r=\|R\|=0\), both laws factor and (2) is trivial. Otherwise let \(m\) be the multiplicity of \(r\) in the continuous list of linear canonical correlations. The top \(m\) eigenvalues of \(H\) are near \(r\) by (1); the rest stay a positive fixed distance below \(r\), because their limit superior is at most \(\max(r^2,r_{m+1})<r\), with a missing \(r_{m+1}\) interpreted as zero. The top \(m\) eigenvalues of \(\Pi H\Pi\) on its range also tend to \(r\), by joint-covariance convergence. For an orthonormal basis of that top compressed subspace, the eigenvector residuals in the full \(H\) are at most \(\delta\). The spectral theorem bounds each basis vector's projection onto the complement of the top full eigenspace by \(O(\delta)\). Both subspaces have dimension \(m\): the squared Hilbert–Schmidt norm of the reverse missed projection is the same trace \(m-\operatorname{tr}(P_1P_2)\). Thus all unit vectors in \(\ker\Pi\) carry at most \(O(\delta^2)\) mass on the top eigenspace of \(H\). For small enough \(h\), the upper spectral edge on \(\ker\Pi\) is at most \(\ell_h-g\) for a fixed \(g>0\). A unit vector decomposed as \(v+z\), with \(v\in\operatorname{ran}\Pi,\ z\in\ker\Pi\), has Rayleigh quotient at most
\[
 \ell_h-g\|z\|^2+2\delta\|v\|\|z\|\le\ell_h+\delta^2/g.
\]
Variational comparison in the other direction is immediate. This proves (2).

## 3. Exact transition and two sharp asymptotics in two coordinates

Take \(L_X=L_Y=\mathbb Z\), zero translations, and \(R=(r)\), \(0<r<1\). Denote maximal correlation by \(\rho_h\). For fixed \(r\ne1/2\), \(t=2\pi/h\), and \(d_r=\min(1,2(1-r))\), the sharp fine-mesh result is
\[
 \rho_h=r+c_r t^2 e^{-t^2d_r/2}
         +o_r(t^2e^{-t^2d_r/2}),\qquad
 c_r=\begin{cases}
   -2r(1-r^2),&0<r<1/2,\\
    2(1+r)(1-r)^2,&1/2<r<1 .
 \end{cases}
 \tag{4}
\]
The first correction can be negative or positive. At \(r=1/2\),
\[
 \rho_h=\tfrac12\quad\text{for every }h>0 .
 \tag{5}
\]
At the coarse endpoint \(h\to\infty\),
\[
 \rho_h=
 \begin{cases}
 (1+o_r(1))\exp[-h^2(1-2r)/(2(1-r^2))],&0<r<1/2,\\
 1-o_r(1),&1/2<r<1.
 \end{cases}
 \tag{6}
\]
For \(r=0\) the variables are independent. Reflections give the corresponding conclusions for negative correlations after replacing \(r\) by \(|r|\).

For (4), write \(\Sigma_h\) for the discrete covariance. Differentiating centered Poisson summation with respect to the center twice yields
\[
 \Sigma_h=C-t^2 C\,\frac{\sum_{w\in\mathbb Z^2}ww^T e^{-t^2 w^TCw/2}}
                          {\sum_{w\in\mathbb Z^2} e^{-t^2 w^TCw/2}}\,C.
\]
With \(w=(m,n)\), \(w^TCw=m^2+n^2+2r mn\). The shortest nonzero shell is the four axes when \(r<1/2\), and the two antidiagonal points \(\pm(1,-1)\) when \(r>1/2\). Indeed opposite-signed nonzero coordinates have value \((|m|-|n|)^2+2(1-r)|mn|\), while same signs or one zero cannot improve the minimum. The matrices \(\sum ww^T\) on these shells are respectively \(2I\) and \(2\left(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\right)\). Equal marginal variances imply the Pearson correlation is \(\Sigma_{h,12}/\Sigma_{h,11}\), positive for small \(h\); subtracting \(r\) gives the coefficient in (4). Fixed \(r\) gives a positive gap to the next shell, so higher shells are little-o. The error in (2) is \(O_r(h^{-2}e^{-4\pi^2(1-r^2)/h^2})\), little-o of the displayed term because \(2(1-r^2)>d_r\).

For (5), \(Y\mid X=x\) is a lattice Gaussian with center \(x/2\), and reflection about that center preserves \(h\mathbb Z\). Its conditional mean is \(x/2\) exactly. To show no nonlinear functions do better, let \(P\) be conditional expectation viewed as a self-adjoint Markov operator on the common marginal. For \(x<x'\) the two conditional laws are stochastically ordered by monotone likelihood ratio (the ratio is proportional to an increasing exponential in \(y\)). The monotone coupling has expected absolute separation equal to the difference of the means, \((x'-x)/2\). Therefore Lipschitz seminorm is contracted by \(1/2\) under \(P\). For any mean-zero bounded Lipschitz \(f\),
\[
 |P^k f(x)|\le 2^{-k}\operatorname{Lip}(f)\int |x-y|\,d\mu_{h,X}(y).
\]
The right side has finite marginal \(L^2\) norm. Finitely supported functions on \(h\mathbb Z\) are bounded Lipschitz and dense, and centering preserves these estimates. By the spectral theorem, there is no \(L_0^2\) spectral mass outside \([-1/2,1/2]\). The coordinate itself is an eigenfunction of eigenvalue \(1/2\), proving equality.

For (6), on integer indices write \(\eta=1/(2(1-r^2))\), \(w_{ij}=e^{-\eta h^2(i^2+j^2-2rij)}\), \(m_i=\sum_j w_{ij}\). The normalized symmetric kernel is \(K_{ij}=w_{ij}/\sqrt{m_i m_j}\). For \(r<1/2\) compare it with the rank-one matrix \(A_{ij}=w_{i0}w_{0j}/\sqrt{m_i m_j}\). It agrees with \(K\) on index \(0\) on either side. With \(\Delta=\eta(1-2r)>0\), for the same nonzero sign, the entry of \(K-A\) is bounded by \(\exp[-\Delta h^2(i^2+j^2)/2]\), since \(m_i\ge w_{i0}\) and \(2|ij|\le i^2+j^2\). For opposite signs the bound improves to \(\exp[-\eta h^2(i^2+j^2)/2]\). The two entries \((1,1)\) and \((-1,-1)\), divided by \(e^{-\Delta h^2}\), tend to one because \(m_1/w_{10}\to1\): \(j=0\) uniquely minimizes the conditional energy at \(i=1\). Every other entry is exponentially smaller in Hilbert–Schmidt norm, by the displayed square-summable bounds. Subtracting a rank-one operator gives the corresponding upper bound on \(s_1(h)\); the unit odd vector supported on \(\{-1,1\}\) gives the matching lower bound, because \(A\) is zero on it and it is orthogonal to the stationary mode. For \(r>1/2\), \(j=1\) is the unique minimizer at \(i=1\), so \(K_{11}\to1\) while \(K_{1,-1}\to0\). The same odd vector proves the lower bound approaching one, and conditional expectation is a contraction.

## Relation to earlier work and checks

The continuous Hermite spectrum is standard, and [Wang–Huang–Lyu, §II.E and §III](https://arxiv.org/html/1812.00127) characterize the lattice Gaussian two-block Gibbs convergence rate in terms of HGR maximal correlation. In particular, HGR's role in that setting is not a new claim. Their analysis expressly separates the ordinary Pearson coefficient from maximal correlation and does not give the explicit fine-mesh comparison (1)–(4) or the critical identity (5). On the continuous side see [Ghazi–Kamath–Raghavendra, §2.1](https://people.csail.mit.edu/badih/papers/dim_red_Gauss.pdf) for Gaussian maximal correlation and Hermite preliminaries. The use of sampling Gram operators, instead of pointwise approximation to a discontinuous grid embedding, is what makes (1) uniformly exponential over all modes. The two-scale audit then uses a conditional-mean residual only for the leading eigenspace.

The accompanying JavaScript uses no data about systems or cryptographic instances. It checks the sharp shell/coefficient calculations by 253,530 exact integer assertions and makes 1,770 floating-point consistency assertions on synthetic Gaussian laws: finite-width singular-value intervals including shifted grids, leading signs and coefficients, exact critical rate, and the coarse endpoint. The numerical checks do not substitute for the proofs.
