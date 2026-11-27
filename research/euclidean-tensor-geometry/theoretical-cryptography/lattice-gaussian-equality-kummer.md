# Exact equality and quantitative gaps for Gaussian lattice inequalities

Let \(L\) be a full Euclidean lattice, \(t>0\), and
\[
A(z)=\sum_{\lambda\in L}e^{-t|\lambda+z|^2}.
\]
Let \(C(z)\) be the covariance of this Gaussian on \(L+z\), with the same precision \(t\). Write \(L=\bigoplus_j L_j\) as an orthogonal sum of nonzero orthogonally indecomposable lattices, with components \(x_j,z_j,u_j\) and distances \(d_j(z)=\operatorname{dist}(z_j,L_j)\). A lattice is orthogonally indecomposable if it is not an orthogonal direct sum of two nonzero lattices.

**Theorem.** At every fixed \(t>0\) the following characterize equality and quantify the gaps.
1. In the Regev–Stephens-Davidowitz Gaussian mass inequality
   \[
   A(x)^2A(y)^2\le A(0)^2 A(x+y)A(x-y)
   \]
   there is equality exactly when, in each factor \(j\), at least one of \(x_j,y_j\) belongs to \(L_j\). The logarithm of the right side divided by the left is comparable to \(\sum_j d_j(x)^2d_j(y)^2\), with positive finite constants depending only on \(L,t\).
2. The known inequality \(C(z)\succeq C(0)\) sharpens to
   \[
   u^\top [C(z)-C(0)]u\ \asymp_{L,t}\ \sum_jd_j(z)^2|u_j|^2 .
   \]
   Its nullspace is exactly the sum of the factor spans for which \(z_j\in L_j\).
3. For \(X\) the centered Gaussian on \(L\), put \(U=u\cdot X,\ V=v\cdot X\). The mixed fourth cumulant
   \[
   \mathbb E U^2V^2-\mathbb E U^2\,\mathbb E V^2-2(\mathbb E UV)^2
   \]
   is comparable to \(\sum_j |u_j|^2|v_j|^2\). In particular centered directional excess kurtosis is **strictly positive** in every nonzero direction, and mixed equality occurs exactly when the two directions have no common nonzero indecomposable component.

All comparisons are two-sided and include zero values on both sides. The constants are for each fixed lattice and width; no dimension-uniform constant is claimed. The proof uses the parity-class identity of [Regev–Stephens-Davidowitz](https://arxiv.org/abs/1502.04796) and the irreducible theta divisor of an indecomposable principally polarized abelian variety. We give the needed projective separation and two derivative facts directly.

## 1. The parity map is a sum of squares

For \(c\in L/2L\), define \(h_c(z)=\sum_{\lambda\in 2L+c}e^{-(t/2)|\lambda+z|^2}\), let \(h(z)\) be their vector, and set \(m(z)=h(z)/\|h(z)\|\). Reindexing \((a,b)\) by \((a+b,a-b)\) in the original double Gaussian sum gives
\[
A(x)A(y)=\langle h(x+y),h(x-y)\rangle,\qquad \|h(z)\|^2=A(0)A(z).
\tag{1}
\]
Write
\[
\mathcal D(x,y)=\log\frac{A(0)^2A(x+y)A(x-y)}{A(x)^2A(y)^2}
=-2\log\langle m(x+y),m(x-y)\rangle.
\tag{2}
\]
The entries are positive, \(m(-z)=m(z)\) since \(-c=c\bmod2L\), and translating \(z\) by a lattice vector just permutes the entries. Thus \(\mathcal D\) is periodic under shifting either variable by \(L\): the two arguments of the inner product acquire the same permutation, since a parity permutation is its own inverse. On a compact set of representatives the scalar product in (2) is bounded below by a positive constant, so \(\mathcal D(x,y)\asymp\|m(x+y)-m(x-y)\|^2\).

Expand (2) at \(y=\epsilon u\). For unit vectors \(m\), the inner product of \(m(x+\epsilon u)\) and \(m(x-\epsilon u)\) is \(1-2\epsilon^2\|Dm_x u\|^2+O(\epsilon^4)\). Comparison with the log Gaussian masses gives the exact covariance identity
\[
u^\top[C(z)-C(0)]u=t^{-2}\|Dm_z u\|^2.
\tag{3}
\]
Here \(C(z)=(2t)^{-1}I+(4t^2)^{-1}\nabla^2\log A(z)\), by differentiation. This is the differential form of the Cauchy–Schwarz proof.

## 2. Orthogonal lattice factors and irreducible theta divisors

Choose a lattice basis matrix \(B\) with \(G=B^\top B\), and put \(\tau=i(t/\pi)G=iY\). The complex torus \(\mathcal A_\tau=\mathbb C^n/(\mathbb Z^n+\tau\mathbb Z^n)\) has the standard principal polarization with positive Hermitian form \(Y^{-1}\). Its ordinary theta function is
\[
\theta(w)=\sum_{k\in\mathbb Z^n}e^{\pi i k^\top\tau k+2\pi i k^\top w}.
\]
Its theta divisor \(\Theta\) is irreducible when the principally polarized torus is indecomposable. We use also the uniqueness, as polarized factors up to permutation, of the decomposition into indecomposable factors (Shimura; see [Canning–Oprea–Pandharipande, §2.2, Proposition 16 and the preceding paragraph](https://doi.org/10.1007/s00222-025-01367-4)). The factor subvarieties in the product are canonical as an unordered family, as can be seen from the irreducible components of the theta divisor: the connected stabilizer of the component pulled back from one factor is the product of the other factors. Intersecting the connected stabilizers of all other components recovers each factor itself. Indeed a factor's principal theta divisor has trivial translation stabilizer, since translating the divisor to itself fixes its line bundle and hence lies in the kernel of its principal polarization map.

**Claim.** A decomposition of \(\mathcal A_{iY}\) into polarized factors induces an orthogonal decomposition of \(L\). The converse is immediate from an orthogonal block basis, but the forward direction needs the *purely imaginary* period matrix.

Complex conjugation acts on \(\mathcal A_{iY}\) as an antiholomorphic origin-preserving involution. Since the theta series at purely imaginary \(\tau\) satisfies \(\theta(\bar w)=\overline{\theta(w)}\) by negating the summation vector, conjugation preserves the theta divisor. It therefore permutes its irreducible components and the canonical factors. For a conjugation-invariant factor of dimension \(g\) with period lattice \(\Gamma\) and lifted conjugation \(J\), the number of components of its fixed locus is \(|\Gamma^-/(1-J)\Gamma|\le2^g\), where \(\Gamma^-=\{\gamma\in\Gamma:J\gamma=-\gamma\}\). To see the formula, a fixed class with representative \(b\) has \((1-J)b\in\Gamma^-\); changing the lift adds \((1-J)\Gamma\). Every such vector is achieved by taking half of it as \(b\), and the zero class consists of the image of the real \(+1\) eigenspace, a connected torus. The rank of \(\Gamma^-\) is \(g\), and \((1-J)\Gamma\) contains \(2\Gamma^-\), proving the bound. A pair of factors exchanged by conjugation instead has connected fixed locus, the graph of the anti-isomorphism.

The full torus with period matrix \(iY\) has exactly \(2^n\) fixed components: the imaginary part of a fixed class is one of the classes of \((Y/2)\mathbb Z^n/Y\mathbb Z^n\), while the real part is connected. Thus conjugation cannot exchange any factors. Their tangent spaces are \(W_j+iW_j\) for real \(W_j\subset\mathbb R^n\). The period lattices of the factors split the full lattice as a direct sum. Taking purely imaginary parts gives a direct sum of \(Y\mathbb Z^n\) by its intersections with the \(W_j\): any purely imaginary period decomposed into factor periods has each factor period purely imaginary, by uniqueness of the decomposition and conjugation-invariance. The \(W_j\) are mutually orthogonal for \(Y^{-1}\), by the product polarization. Pulling this split of \(Y\mathbb Z^n\) back by \(Y^{-1}\) gives a \(G\)-orthogonal split of the integer basis lattice: \((Yp)^\top Y^{-1}(Yq)=p^\top Yq\), a positive constant times \(p^\top Gq\). This proves the claim. In particular, for an orthogonally indecomposable \(L\), \(\Theta\) is irreducible. It is reduced (a principal theta divisor is reduced; in this irreducible case a multiplicity \(k>1\) would make its degree divisible by \(k^n\) by the integral top self-intersection formula).

## 3. Separation and two nonvanishing jets

Take \(L\) indecomposable for the moment. In basis coordinates let \(c=B\varepsilon\) with \(\varepsilon\in\{0,1\}^n\), and set \(\zeta(z)=\tau B^{-1}z/2\). Then
\[
h_c(z)=e^{-t|z|^2/2}\,\theta_\varepsilon(\zeta(z)),\qquad
\theta_\varepsilon(\zeta)=
\sum_{k\in\mathbb Z^n}
e^{2\pi i(k+\varepsilon/2)^\top\tau(k+\varepsilon/2)+
4\pi i(k+\varepsilon/2)^\top\zeta}.
\tag{4}
\]
These are the second-order theta coordinates of the Kummer map. The addition formula
\[
\theta(w+\zeta)\theta(w-\zeta)=\sum_\varepsilon
\theta_\varepsilon(w)\theta_\varepsilon(\zeta)
\tag{5}
\]
follows by reindexing the two summation vectors by their half-sum and half-difference. The linear map \(z\mapsto\zeta(z)\) is real-to-purely-imaginary and injective, and \(\zeta(z)\) is a two-torsion point exactly when \(z\in L\).

We spell out the properties of (5) that suffice, in addition to irreducibility of \(\Theta\) and its trivial translation stabilizer.

* **Separation.** If the projective theta coordinates at \(\zeta,\zeta'\) agree, (5) gives proportional functions of \(w\). Their zero divisors are \((\Theta-\zeta)+(\Theta+\zeta)\) and \((\Theta-\zeta')+(\Theta+\zeta')\). Uniqueness of the irreducible components and the trivial stabilizer give \(\zeta'\equiv\pm\zeta\) in the complex torus, including when the two translates coincide. Hence \(m(z)=m(z')\) exactly for \(z'\equiv\pm z\bmod 2L\): the forward direction uses (4) and the purely imaginary periods, and the reverse follows from evenness and \(2L\)-periodicity of \(h\).

* **First derivative away from two-torsion.** If \(\partial_a\theta_\varepsilon(\zeta)=b\,\theta_\varepsilon(\zeta)\) for all \(\varepsilon\), differentiate (5) in \(\zeta\) along \(a\). On the smooth part of \(\Theta-\zeta\) off \(\Theta+\zeta\), the identity gives \(\partial_a\theta(w+\zeta)=0\). The two translates are distinct away from two-torsion; thus this forces the constant vector field \(a\) tangent along a dense open part of \(\Theta\). A nonzero constant field cannot be tangent there: on a smooth open piece its local translation flow stays on the divisor, which makes a small translate of the irreducible divisor coincide with it, contradicting the trivial stabilizer. This proves the derivative of the projective theta map is injective there. Equivalently, by (4) and normalization, \(Dm_z\) is injective if \(z\notin L\).

* **Mixed second derivative at zero.** Suppose \(\partial_{a,b}^2\theta_\varepsilon(0)\) is proportional to \(\theta_\varepsilon(0)\) with a common proportionality constant. Differentiating (5) gives
  \[
  2\theta(w)\partial_{a,b}^2\theta(w)-
  2\,\partial_a\theta(w)\partial_b\theta(w)
  =\text{constant}\cdot\theta(w)^2.
  \]
  On \(\Theta\) the product of the two first derivatives vanishes. Their restrictions have well-defined zero loci on \(\Theta\), since the derivative of the theta multiplier only multiplies the vanishing theta function there. Irreducibility forces one derivative to vanish on all of \(\Theta\). The same tangent-field argument gives \(a=0\) or \(b=0\). By (4), normalization at zero, and the vanishing first derivative of the even map \(m\), this proves \(D^2m_0(x,y)\ne0\) for every pair of nonzero real directions \(x,y\).

Only the last, bilinear nonvanishing property is needed for quantitative gaps. It avoids assuming smoothness of the entire theta divisor or differentiating a singular quotient.

## 4. From the parity map to all equality cases

By (2) and separation, \(\mathcal D(x,y)=0\) on an indecomposable lattice precisely when \(x+y\equiv\pm(x-y)\bmod2L\), which means \(x\in L\) or \(y\in L\). By the first-derivative assertion and (3), \(C(z)-C(0)\) is positive definite for \(z\notin L\); for \(z\in L\) it vanishes.

For quantitative bounds, compactness of the two real unit spheres and mixed second-derivative nonvanishing give
\(\|D^2m_0(x,y)\|\asymp |x||y|\). Near zero, evenness and analyticity give
\(Dm_z u=D^2m_0(z,u)+O(|z|^3|u|)\), proving (3) comparable to \(|z|^2|u|^2\). Away from the lattice, the first-derivative assertion and compactness give uniform bounds above and below by positive multiples of \(|u|^2\). By periodicity up to coordinate permutation this yields the desired global distance bound.

For (2), let \(F(x,y)=m(x+y)-m(x-y)\). Near \(x=y=0\), \(F\) vanishes on both coordinate axes and has mixed second derivative \(2D^2m_0\), so
\[
F(x,y)=2D^2m_0(x,y)+o(|x||y|).
\]
The uniform remainder follows by integrating the mixed derivative of \(F\) on the rectangle of line segments from zero to \(x,y\). Thus the gap has the required order when both shifts are small. When \(x\) stays away from the lattice and \(y\) is small, use \(F(x,y)=2Dm_x y+O(|y|^3)\) and injectivity uniformly on a compact set. When both stay away, separation and compactness give a uniform positive gap. Periodicity of the squared norm of \(F\) under either lattice shift, and symmetry of the gap in \(x,y\), prove the comparison everywhere.

For the mixed cumulant \(\kappa(U,U,V,V)\) in the theorem, translate the law on \(L+\epsilon v\) back to \(L\). It becomes the centered law weighted by \(e^{-2t\epsilon V}\), after normalization, and translation does not affect covariance. Expanding the variance of \(U\) under this tilt gives \(2t^2\epsilon^2\kappa(U,U,V,V)+O(\epsilon^4)\) for the difference from its value at zero, by the logarithmic moment generating function and symmetry. Expanding (3) at the same shift yields the exact identity
\[
\kappa(U,U,V,V)=\frac{\|D^2m_0(u,v)\|^2}{2t^4}.
\]
The mixed jet estimates prove the asserted comparison on an indecomposable lattice. Finally orthogonal product factors have independent Gaussian components, so their covariances and fourth cumulants add, and their log gaps in (2) add by multiplication of masses. The full result follows with the smallest and largest of the factor constants.

## Prior results and scope

[Regev–Stephens-Davidowitz, Theorem 2.1, Corollary 3.2 and Proposition 3.3](https://arxiv.org/abs/1502.04796) establish the non-strict mass, covariance and fourth-moment inequalities. The Gaussian-specific step here is to identify their parity vector with the real slice of second-order theta coordinates, transfer orthogonal factorization using the real-locus argument, and extract sharp equality and the quadratic product orders. The classical second-order theta notation is also used in [Grushevsky–Krichever, §2](https://www.math.columbia.edu/department/krichever/pdfs/2010-2014/2010-IDSEAACOPVBAPOQ.pdf); our jet argument is explicitly given above. No priority claim over every source is made. These results concern abstract lattice Gaussian statistics, not a cryptographic attack, solver, or deployment.

Replay: node verify-lattice-gaussian-equality-kummer.js (Node.js 18+, no dependencies). The analytic proof is independent of the numerical sanity checks.
