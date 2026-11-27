# The quartic cost of matching exact lattice Gaussian masses

Nearest-site quantization minimizes squared distance to a lattice if the masses of its cells can be chosen by the quantizer. Requiring instead the **exact** discrete Gaussian masses adds a positive quartic term at small mesh. This term has an explicit matrix expression and holds on every fixed lattice and for every fixed Gaussian covariance, even when the covariance and the cell moment matrix do not commute.

**Scope and comparison.** [Conway–Sloane](https://neilsloane.com/doc/Me82.pdf) study Voronoi moments and the leading quantization cost. [Kitagawa–Mérigot–Thibert](https://doi.org/10.4171/JEMS/889) develop the semi-discrete Laguerre dual for prescribed masses. The present question is the cost asymptotic for countably many sites with exact sampled Gaussian masses, not a computational method for semi-discrete transport. The earlier [lattice transport tangent](lattice-wasserstein-tangent.md) compares two laws on the same discrete lattice; here one law is continuous and the first error term beyond nearest rounding is the focus. No cryptographic instances, learning algorithms or concrete schemes are analyzed.

## 1. Sharp expansion

Let \(L\subset\mathbb R^d\) be a full lattice, \(V_L\) its centered Euclidean Voronoi cell, and \(v_L=\det L\). Define
\[
 M=\frac1{v_L}\int_{V_L} uu^{\mathsf T}\,du.
\]
Fix \(C\succ0\), and let \(\mu\) be the centered real Gaussian \(N(0,C)\) with density \(p\). For \(h>0\) and an arbitrary translate \(z\) modulo \(L\), take sites \(h(L+z)\) and let \(\nu_h\) be the discrete Gaussian on those sites whose probabilities are proportional to \(p(y)\). The cost in \(W_2^2\) is ordinary Euclidean squared distance, not the \(C^{-1}\)-norm.

Let \(D\) be the unique symmetric solution of
\[
 DC+CD=M. \tag{1}
\]
For fixed \(L,C\), as \(h\downarrow0\), uniformly in the translate,
\[
 \boxed{\qquad
 W_2^2(\mu,\nu_h)
   =h^2\operatorname{tr}M+h^4\operatorname{tr}(DCD)+O_{L,C}(h^5).
 \qquad} \tag{2}
\]
In a basis diagonalizing \(C=\operatorname{diag}(c_i)\), \(D_{ij}=M_{ij}/(c_i+c_j)\), so the quartic coefficient is \(\tfrac12\sum_{i,j} M_{ij}^2/(c_i+c_j)>0\). If \(C=I\), it equals \(\tfrac14\operatorname{tr}(M^2)\). In rank one on a unit lattice with \(C=1\), the expansion is \(h^2/12+h^4/576+O(h^5)\). In contrast, the squared error of nearest Euclidean rounding to the same sites is \(h^2\operatorname{tr}M+O_{L,C}(e^{-c/h^2})\), with freely induced output weights, not the exact weights of \(\nu_h\).

Equivalently at fixed mesh on \(L+z\), with a continuous and a discrete Gaussian of common covariance parameter \(s^2C\) and common center zero, the cost is \(\operatorname{tr}M+s^{-2}\operatorname{tr}(DCD)+O(s^{-3})\). This is a statement about the probability laws and the optimal cost, not an assertion that nearest rounding to perturbed cells exactly gives the discrete target.

## 2. A geometric estimate for slightly perturbed cells

For a symmetric positive definite matrix \(B\) close to \(I\), let \(V_B\) be the Voronoi cell using squared norm \(u^{\mathsf T}Bu\), and \(M_B=v_L^{-1}\int_{V_B}uu^{\mathsf T}du\). The cells have the same volume \(v_L\), are centrally symmetric, and are uniformly bounded. Writing \(\delta=\|B-I\|\),
\[
 M_B=M+O_L(\delta),\qquad
 0\le\operatorname{tr}(M_B-M)=O_L(\delta^2). \tag{3}
\]
To prove this, compare the Euclidean nearest representative \(u\in V_L\) of a point of \(\mathbb R^d/L\) to its \(B\)-nearest representative \(u_B\in V_B\). Both have uniformly bounded norm since the norms are comparable near \(I\). If \(u_B=u+\lambda\ne u\), then \(\lambda\in L\) is nonzero and bounded, hence in a fixed finite set. The two minimizing properties give
\[
 0\le\|u+\lambda\|^2-\|u\|^2\le
     \delta\big(\|u+\lambda\|^2+\|u\|^2\big).
\]
For each nonzero \(\lambda\), this condition restricts \(u\) to a slab of thickness \(O_L(\delta)\) around its Euclidean bisector. Thus the representatives differ on Haar mass \(O_L(\delta)\). Their outer products differ there by a bounded amount, while their squared norms differ only by \(O_L(\delta)\), proving both assertions in (3).

## 3. A candidate power diagram and its output masses

Take \(B_h=I+h^2 D\), which is positive definite for small \(h\). For an input \(x\), define \(N_h(x)\) to minimize
\[
 \|x-y\|^2+h^2 y^{\mathsf T}D y
 \qquad(y\in h(L+z)).
\]
Break null ties arbitrarily. Completing the square shows that this is nearest rounding of \(B_h^{-1}x\) in the \(B_h\)-norm. Its cell at \(y\) is therefore \(B_h(y+hV_{B_h})\). Write \(w_y\) for the probability of this cell under \(\mu\), and \(q_y\) for the desired mass under \(\nu_h\).

We claim
\[
 \sum_y(1+\|y\|^2)|q_y-w_y|=O(h^4),\qquad
 \sum_y\frac{(q_y-w_y)^2}{w_y}=O(h^8).
 \tag{4}
\]
For details set \(B=B_h\) and \(Q=B C^{-1}B\). Changing variables in the cell integral, with \(U_B\) uniform on \(V_B\), gives
\[
 \frac{w_y}{h^d v_L p(y)}
 = (\det B)\,e^{-\frac12 y^{\mathsf T}(Q-C^{-1})y}
   \mathbb E\exp\!\left(-h\,y^{\mathsf T}Q U_B
                        -\frac{h^2}2 U_B^{\mathsf T}Q U_B\right). \tag{5}
\]
The expectation can replace the first exponential factor by its hyperbolic cosine, since \(U_B\) is symmetric. The determinant and outside exponential have joint expansion
\[
 1+h^2\bigl(\operatorname{tr}D-y^{\mathsf T}D C^{-1}y\bigr)
 +O\bigl(h^4(1+\|y\|^4)e^{K h^2\|y\|^2}\bigr).
\]
The inside expectation is
\[
 1+\frac{h^2}2\bigl(y^{\mathsf T}C^{-1}M C^{-1}y
                        -\operatorname{tr}(C^{-1}M)\bigr)
 +O\bigl(h^4(1+\|y\|^4)e^{K h\|y\|}\bigr).
\]
Indeed the second-order expression first has \(Q\) and \(M_B\) instead of \(C^{-1}\) and \(M\), differing by \(O(h^2)\) by (3). The remainder bounds are ordinary real Taylor inequalities for the exponential and the hyperbolic cosine, with uniformly bounded \(U_B\); the two displayed constants and the fixed degree may be enlarged without changing the assertion. Equation (1), multiplied by \(C^{-1}\) on both sides, gives \(C^{-1}M C^{-1}=C^{-1} D+D C^{-1}\). Taking the trace with \(C^{-1}\) on one side of (1) also gives \(\operatorname{tr}(C^{-1}M)=2\operatorname{tr}D\). The \(h^2\) terms in (5) cancel. It follows that the ratio in (5) differs from one by at most \(K h^4(1+\|y\|^{K'})e^{K(h\|y\|+h^2\|y\|^2)}\), for fixed constants. A lower bound for the same ratio is \(K^{-1}e^{-K(h\|y\|+h^2\|y\|^2+1)}\), directly from bounded \(U_B\) and (5).

The normalizer of \(q_y\), relative to \(h^d v_L p(y)\), is \(1+O(e^{-c/h^2})\) by Poisson summation, uniformly over translates. The bounds just proved give (4) after summing polynomially weighted Gaussian envelopes over the sites. Such sums times \(h^d\) are uniformly bounded for small \(h\): the fixed power and the extra exponent are absorbed into a Gaussian of slightly larger covariance, and this latter lattice sum is bounded by Poisson summation, or by the packing bound on numbers of sites in annuli. In particular the relative error control is used only under summation against Gaussian tails, not asserted to be uniformly small for arbitrarily far sites.

## 4. From approximate to exact masses at a smaller cost

Let \(J_h=\mathbb E_\mu\|X-N_h(X)\|^2\). The definition of \(N_h\) as a pointwise penalized minimizer implies that any coupling of \(\mu,\nu_h\) has cost at least
\[
 J_h+h^2\sum_y y^{\mathsf T}Dy(w_y-q_y)\ \ge\ J_h-O(h^6), \tag{6}
\]
by (4). This uses no existence theorem for a dual maximizer or finite-support approximation.

For the upper bound, change the *continuous input* density to \(\widetilde p(x)=p(x)q_y/w_y\) on the cell of \(N_h\) labeled \(y\). It is a probability density and \(N_h\) sends it to the exact target \(\nu_h\). Its relative entropy to \(\mu\) is \(\sum_y q_y\log(q_y/w_y)\), bounded by the second quantity in (4) using \(\log u\le u-1\). [Talagrand's Gaussian transportation inequality](https://geodesic.mathdoc.fr/item/GFA_1996__6_1_58238/), whitened by \(C\), gives
\[
 W_2(\mu,\widetilde\mu)=O(h^4),\qquad d\widetilde\mu=\widetilde p(x)\,dx.
\]
For \(x=B(y+h u)\) in the cell, \(\|x-y\|^2\le O(h^2+h^4\|y\|^2)\), so (4) shows that the \(N_h\) error under \(\widetilde\mu\) differs from \(J_h\) by \(O(h^6)\). Coupling the original input to \(\widetilde\mu\) and then applying \(N_h\) yields squared cost at most
\(J_h+O(h^6)+O(h^4)\,O(h)+O(h^8)=J_h+O(h^5)\); this is the square of the triangle bound in \(L^2\), using \(J_h=O(h^2)\) from the same cell estimate and bounded second moments. Together with (6), this reduces the exact cost to \(J_h+O(h^5)\). Moving discrete output masses directly by a triangle inequality need not give this accuracy; the small continuous density change is the reason it works.

## 5. Evaluation of the candidate cost

Let \(R_B(a)\) denote the \(B\)-nearest representative of \(a+L\) in \(V_B\), a bounded \(L\)-periodic function. The error can be written
\[
 X-N_h(X)=(I-B^{-1})X+h R_B(B^{-1}X/h-z).
\]
Under a Gaussian input, the expectation of any bounded periodic function of \(B^{-1}X/h-z\) differs from its Haar mean by \(O(e^{-c/h^2})\) times its supremum norm, uniformly in \(z\) and for \(B\) close to \(I\). The same statement with an extra linear weight in \(X\) has exponentially small expectation, because the zero Fourier coefficient is then zero. To check these facts, periodize the density of \(B^{-1}X/h\) over \(L\): its Fourier series at dual vectors is Gaussian with widths uniformly comparable to \(1/h\). For the linear-weight version the Fourier coefficients follow by a derivative of the Gaussian transform, adding only a polynomial prefactor in \(1/h\) and the dual norm, still exponentially small in total away from the zero dual vector. Uniform boundedness and Poisson summation justify the pairing with the bounded periodic representatives even where they are discontinuous.

It follows that the mixed term in the squared error is exponentially small, and the cell term is \(h^2\operatorname{tr}M_B+O(e^{-c/h^2})\). From (3), \(\operatorname{tr}M_B=\operatorname{tr}M+O(h^4)\). Meanwhile \((I-B^{-1})=h^2D+O(h^4)\), so its Gaussian squared contribution is \(h^4\operatorname{tr}(DCD)+O(h^6)\). Insert these facts into (6) and the matching upper bound to get (2). Taking \(B=I\) in the same periodic expectation gives the stated ordinary nearest-rounding cost.

**Replay.** Run `python3 verify-gaussian-transport-quartic.py` for exact rational checks of the Lyapunov cancellation, noncommuting examples, and the Voronoi-moment stationarity on small planar perturbations. The proof of the asymptotic is analytic and requires neither numerical transport solvers nor finite-precision sampler assumptions.
