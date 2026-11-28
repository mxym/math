# The Poisson hard edge of dyadic random module matrices

The smallest singular values across the canonical places of a random dyadic cyclotomic matrix have an exact asymptotic law. At every fixed rectangular matrix shape, their suitably rescaled squares to a power form a unit-rate Poisson process. This is not a consequence of a fixed-dimensional Fourier CLT: the rare events have probability of order one over the number of places, and some tuples of places have exact arithmetic relations. The proof gives a local-density comparison *uniformly over every fixed tuple of distinct places*, even for discrete coefficient noise.

This is standalone random Euclidean matrix geometry, not a lattice-solving algorithm, a scheme evaluation, or a cryptographic hardness assertion. [Barrera–Manrique, Theorem 1.2](https://arxiv.org/pdf/2109.02282) already gives the Rayleigh minimum and joint upper extreme for **scalar ordinary circulants**. The new scope here is dyadic odd-root Fourier frequencies, every fixed rectangular shape, a hard-edge point process, and the stated varying input laws. The [dyadic log-Jacobian result](dyadic-log-jacobian.md) gives a one-sided small-singular-value bound, sufficient for its log-volume law, not a limiting extreme distribution. The [upper spectral extreme result](dyadic-spectral-extreme.md) addresses the opposite end of the spectrum.

## 1. Model and statement

Let \(n\to\infty\) through powers of two, \(R_n=\mathbb Z[\zeta_{2n}]\), and \(N=n/2\). Use one representative of each conjugate pair of places, so their root exponents \(a\) are distinct odd residues modulo \(2n\), no two equal up to sign. Fix integers \(1\le r\le m\). In an \(r\)-by-\(m\) matrix \(X\) over \(R_n\) (or its real coefficient version), each entry has independent coefficients \(Z_{n,\ell}\), \(\ell=0,\ldots,n-1\), with all coefficients and entries iid within a given \(n\). The coefficient law \(Z_n\) is real, centered, with variance \(v_n>0\). Assume
\[
 \max(v_n,v_n^{-1})=n^{o(1)},\qquad
        \mathbb E|Z_n|^3/v_n^{3/2}\le n^{o(1)} .
 \tag{1}
\]
Here an upper bound \(n^{o(1)}\) allows any fixed constant or subpolynomial growth. For fixed \(c,C,b_0,\ell_0>0\), also assume
\[
\begin{split}
 |\mathbb E e^{2\pi i u Z_n}|&\le \exp[-c v_n\operatorname{dist}(\ell_0u,\mathbb Z)^2],
                    &&u\in\mathbb R,\\
 \log\mathbb E e^{u Z_n}&\le C v_n u^2, && |u|\le b_0 .
\end{split}
 \tag{2}
\]
These include every fixed centered nondegenerate integer law with a finite exponential moment in a neighborhood of zero, with \(\ell_0\) its lattice span (so in particular Rademacher coefficients are covered). They also include the signed sparse law with probabilities \(p_n/2,p_n/2,1-p_n\) on \(1,-1,0\), for \(0<p_n\le1/2\), \(1/p_n=n^{o(1)}\); and discrete Gaussian coefficient widths satisfying the variance condition (1). Details are in §6.

For each place \(a\), let \(X_a\) be the complex evaluation at \(e^{\pi i a/n}\) and put \(G_a=X_a/\sqrt{n v_n}\). The limiting entry convention is a standard complex normal with real part and imaginary part each of variance \(1/2\). Put
\[
 d=m-r+1,\qquad C_{r,m}=\frac{\Gamma(m+1)}{(r-1)!\,\Gamma(d+1)^2}.
\]
The point measure with one point per conjugate pair of places,
\[
             \sum_a \delta_{\,C_{r,m}N\,s_{\min}(G_a)^{\,2d}},
 \tag{3}
\]
converges on \([0,\infty)\) to a Poisson point process of unit intensity. In particular the rescaled minimum in (3) tends to \(\operatorname{Exp}(1)\); taking its \(2d\)-th root gives the corresponding Weibull law for the normalized least singular value. The conjugate duplicate is not counted twice. For \(r=m=1\), this means \(\min_a|X_a|/\sqrt{v_n}\) converges to the Rayleigh law with cdf \(1-e^{-x^2/2}\). For \(r=m\), \(C_{r,r}=r\); for \(r=1\), \(C_{1,m}=1/m!\).

Neither a growing matrix shape nor polynomially vanishing \(v_n\) is covered. For the common full dyadic discrete-Gaussian model where the earlier upper spectral result gives \(\max_a s_{\max}(G_a)/\sqrt{\log N}\to1\) in probability, (3) also gives the limit of the abstract canonical condition number after division by \(\sqrt{\log N}(C_{r,m}N)^{1/(2d)}\) by Slutsky. No joint independence of upper and lower extremes is claimed.

## 2. A uniform angular lemma via simultaneous frequency compression

Fix a positive tuple size \(k\). For distinct places \(a_1,\ldots,a_k\) and coefficients \(z_j\in\mathbb C\), put
\[
 y_\ell=\operatorname{Re}\sum_{j=1}^k z_j e^{\pi i a_j\ell/n},
       \quad 0\le\ell<2n,\qquad A=\left(\sum_j|z_j|^2\right)^{1/2}.
\]
For any fixed \(b>0\) and sufficiently small fixed \(\tau_k>0\), uniformly over the places and \(b\le A\le C_0 n^{\tau_k}\), with fixed \(C_0\),
\[
 \frac1n\sum_{\ell=0}^{n-1}\operatorname{dist}(y_\ell,\mathbb Z)^2
                 \ \ge\ c_{k,b,C_0}\,(1+A)^{-4k}.
 \tag{4}
\]
Crucially this works even if the frequency tuple satisfies short relations. To prove it, use Dirichlet's box argument with \(M=\lfloor n^{1/(2k)}\rfloor\). Among the \(M^k+1\) vectors of phases
\((t a_j/(2n)\bmod1)_{j=1}^k\), \(0\le t\le M^k\), two lie in the same box of side \(1/M\). Subtract their indices to get \(1\le h\le M^k\) with \(\operatorname{dist}(h a_j/(2n),\mathbb Z)\le1/M\) for all \(j\).

Let \(g=\gcd(h,2n)\) and \(L=2n/g\). Addition of \(h\) partitions the \(2n\) coefficient indices into \(g\) orbits of length \(L\), with \(L\ge2\sqrt n\). Along an orbit starting at \(\ell_0\), the phases are values at \(t/L\), \(0\le t<L\), of
\[
 f_{\ell_0}(u)=\operatorname{Re}\sum_{j=1}^k
       z_j e^{\pi i a_j\ell_0/n}e^{2\pi i b_j u},
 \qquad b_j \equiv a_j(h/g)\pmod L,\quad |b_j|\le L/M.
\]
Each \(b_j\) is odd, hence nonzero: \(L\) is a power of two and \(h/g,a_j\) are odd. This is precisely where the dyadic odd-root setting is used; aliasing between two nonzero modes on a chosen orbit is allowed. For large \(n\) every squared polynomial \(f_{\ell_0}^2\) has degree \(<L\), so its discrete average over that orbit equals its integral. Across all indices, orthogonality of the distinct signed modes gives mean \(y_\ell^2=A^2/2\). The uniform bound \(|f_{\ell_0}|\le\sqrt{k}\,A\) then implies a positive fraction (depending only on \(k\)) of orbits have \(\|f_{\ell_0}\|_{L^2[0,1]}\ge A/2\). All orbit polynomials have mean zero.

On such an orbit apply [Nazarov's measurable Turán inequality](https://m.mathnet.ru/php/archive.phtml?jrnid=aa&option_lang=eng&paperid=397&wshow=paper) to \(f_{\ell_0}-q\) for each integer \(q\). With at most \(2k+1\) terms and purely imaginary frequencies, it gives
\(\sup_{[0,1]}|f_{\ell_0}-q|\le (K_k/|E|)^{2k}\sup_E|f_{\ell_0}-q|\) for any measurable set \(E\) of positive length. The supremum on the left is at least \(A/2\) by zero mean and the \(L^2\) bound. Hence the length of \(|f_{\ell_0}-q|\le\varepsilon\) is at most \(K_k(2\varepsilon/A)^{1/(2k)}\). Only \(O_k(1+A)\) integers can meet the range up to \(\varepsilon\le1\). Taking \(\varepsilon=c_{k,b}(1+A)^{-2k}\) for a sufficiently small constant, their union has measure at most \(1/2\). It follows that the continuous integral of \(\operatorname{dist}(f_{\ell_0},\mathbb Z)^2\) is at least \(c'_{k,b}(1+A)^{-4k}\).

The squared-distance function is 1-Lipschitz and \(\|f_{\ell_0}'\|_\infty\le C_k A L/M\). Thus the error of the Riemann average on the orbit is \(O_k(A/M)\). Choose, for example, \(\tau_k=1/(20k^2)\); \((4k+1)\tau_k<1/(2k)\) makes this error negligible throughout \(A\le C_0 n^{\tau_k}\). The positive fraction of good orbits gives the full discrete lower bound. Finally \(y_{\ell+n}=-y_\ell\) since all \(a_j\) are odd, so the full and half averages of squared lattice distance agree. This proves (4).

## 3. The multi-place local density comparison

For a fixed tuple of \(k\) places, view its matrices \(G_{a_j}\) together as a vector in \(\mathbb R^{D}\), \(D=2krm\). The reference density \(g_{\mathrm{ref}}\) is that of \(k\) independent \(r\)-by-\(m\) matrices of iid standard complex normals. Add independent real noise with a smooth compactly supported probability density of radius \(\xi_n=n^{-1/2-\tau_k/2}\) in \(\mathbb R^{D}\). If \(g_{n,\mathrm{sm}}\) denotes the resulting density, then
\[
       \sup_{x\in\mathbb R^{D}}|g_{n,\mathrm{sm}}(x)-g_{\mathrm{ref}}(x)|
                         =O(n^{-c_k'})
 \tag{5}
\]
for a positive \(c_k'\), uniformly over all place tuples. Constants may depend on the fixed matrix shape and input-law bounds. Translation and small perturbation by this independent auxiliary noise are only tools in the proof.

Here are the Fourier estimates for (5), using \(2\pi\) convention. For a dual vector \(t\in\mathbb R^{D}\), each entry of the matrix contributes a product of characteristic factors \(\mathbb E e^{2\pi i Z_n y_\ell/\sqrt{n v_n}}\), with \(y_\ell\) as in §2 and \(\sum_j|z_j|^2\) equal to the squared real dual norm at that entry. Orthogonality gives \(\sum_{\ell<n} y_\ell^2=n\sum_j|z_j|^2/2\) exactly, since the square is invariant under \(\ell\mapsto\ell+n\). The variance of the whole realified vector is therefore \(I/2\). When \(\|t\|\le K_0\sqrt{n v_n}\) for a sufficiently small fixed \(K_0>0\), all arguments \(\ell_0 y_\ell/\sqrt{n v_n}\) in (2) have magnitude at most \(1/2\); here \(\ell_0\) is the lattice-span constant of (2). Equation (2) and the exact second-moment identity give a modulus bound \(e^{-c'\|t\|^2}\).

For \(\|t\|\le n^{1/20}\), Taylor expansion of each characteristic logarithm and (1) give for the joint Fourier transform
\[
          \exp\big[-\pi^2\|t\|^2+O(n^{-1/2+o(1)}\|t\|^3)\big].
\]
This follows from \(\log\mathbb E e^{2\pi i u Z_n}=-2\pi^2 v_n u^2+O(\mathbb E|Z_n|^3 |u|^3+v_n^2|u|^4)\) in the small uniform neighborhood being used; the total fourth-square remainder is absorbed. Thus its integrated difference from \(e^{-\pi^2\|t\|^2}\) on this region is \(O(n^{-1/2+o(1)})\). The auxiliary smooth factor differs from \(1\) by at most \(O(\xi_n\|t\|)\), and it does not increase any modulus.

In the middle range \(K_0\sqrt{n v_n}<\|t\|\le T_n=\sqrt{n v_n}\,n^{\tau_k}\), at least one entry block has dual norm between \(K_0\sqrt{n v_n}/\sqrt{rm}\) and \(T_n\). For that entry rescale its coefficients in (4) by \(\ell_0/\sqrt{n v_n}\), to put their total magnitude between two fixed-constant multiples of \(1\) and \(n^{\tau_k}\). Equations (2) and (4) bound the modulus of that entry's characteristic product by
\[
                         \exp[-c'' n v_n (1+n^{\tau_k})^{-4k}],
\]
which is superpolynomially small by (1). The modulus of the joint product is no larger. The missing part between \(n^{1/20}\) and \(K_0\sqrt{n v_n}\) already has Gaussian Fourier decay. Beyond \(T_n\), the auxiliary density's transform is bounded by \(C_s(1+\xi_n\|t\|)^{-s}\) for any fixed \(s\), by integrating by parts. Since \(\xi_n T_n=n^{\tau_k/2+o(1)}\), choosing \(s\) large for the fixed \(D,k\) bounds its integrated outer tail by a negative power of \(n\). Integrating all these estimates and using Fourier inversion proves (5). No frequency exclusion, other than equal or conjugate places, has been made.

We will also use a uniform coordinate tail outside a ball of radius \(R_n=K\sqrt{\log n}\), where \(K\) can be chosen for any prescribed power of \(n^{-1}\). Each real coordinate of each \(G_{a_j}\) is a sum of independent centered terms with coefficients bounded by \(1/\sqrt{n v_n}\). Applying the mgf bound in (2) at arguments \(O(\sqrt{\log n}/\sqrt{n v_n})=o(1)\) gives probability \(O(n^{-M})\) for any fixed \(M\) by choosing \(K\) sufficiently large. The same holds after the bounded auxiliary noise, and for the Gaussian reference.

## 4. From local densities to the matrix hard edge

The uniform *additive* density estimate gives the necessary *relative* accuracy on these rare events because their volume is small. For one \(r\)-by-\(m\) complex matrix in a Euclidean ball of radius \(R\), the volume where \(s_{\min}\le x\) is at most
\[
                         C_{r,m}\,'\, x^{2d}(1+R)^{2rm}.
 \tag{6}
\]
Indeed the event gives a unit vector of row coefficients with combined row norm at most \(x\); some coefficient has absolute value at least \(r^{-1/2}\), so its row is within \(\sqrt r\,x\) of the span of the other rows. Conditional on these other rows as fixed variables, the orthogonal complement has complex dimension at least \(d=m-r+1\). The tube volume inside radius \(R\) is thus at most a constant times \(x^{2d}(1+R)^{2m}\) for \(0<x\le1\). Integrating the other rows and summing over the choices of last row gives (6), including rank-deficient boundary configurations.

For an independent standard complex normal \(r\)-by-\(m\) matrix \(G\), put \(\alpha=m-r=d-1\). The complex Wishart eigenvalues of \(GG^*\) have symmetric density proportional to
\(\prod_i \lambda_i^\alpha e^{-\lambda_i}\prod_{i<j}(\lambda_i-\lambda_j)^2\) for positive \(\lambda_i\). This is the classical complex Wishart change of variables. The integral of that expression over unordered coordinates is
\[
 Z_{r,\alpha}= \prod_{i=1}^r i!\,\Gamma(\alpha+i).
\]
Indeed expanding the squared Vandermonde gives \(r!\) times the Gram determinant of the monomials of degrees \(0,\ldots,r-1\) for weight \(\lambda^\alpha e^{-\lambda}\). Factoring \(\Gamma(\alpha+i+1)\) from row \(i=0,\ldots,r-1\) leaves monic rising-factorial polynomials in \(\alpha+i+1\) in the successive columns; their determinant is \(\prod_{i=0}^{r-1}i!\). Integrating one eigenvalue up to \(t\downarrow0\), dominated convergence in the other variables increases their exponents from \(\alpha\) to \(\alpha+2\). Events that two eigenvalues are at most \(t\) contribute \(o(t^{\alpha+1})\), for example by the two integrations of powers \(\lambda^\alpha\) with other polynomial factors bounded by an integrable exponential times a polynomial. Thus
\[
 \Pr(s_{\min}(G)^2\le t)
 \sim \frac{r}{\alpha+1}\frac{Z_{r-1,\alpha+2}}{Z_{r,\alpha}}t^{\alpha+1}
 = C_{r,m}\, t^d .
 \tag{7}
\]
This fixed-shape formula does not use a growing-matrix hard-edge theorem.

Fix positive \(x_1,\ldots,x_k\) in a joint threshold calculation for (3), and set \(t_j=(x_j/(C_{r,m}N))^{1/(2d)}\), the thresholds for singular values. In the ball of radius \(R_n=K\sqrt{\log n}\) the volume of the joint sublevel event is at most a power of \(1+R_n\) times \(\prod_j t_j^{2d}=O(n^{-k})\) by (6). Equation (5) therefore bounds the probability comparison error on this ball by \(o(n^{-k})\), and the outside tail is also \(o(n^{-k})\). To remove the auxiliary noise, use the fact that each singular value changes by at most the operator norm of the perturbation, at most \(\xi_n\) here. The thresholds \(t_j\pm\xi_n=t_j(1+o(1))\) are positive for large \(n\) since \(d\ge1\). The same estimate and (7) apply to both bounding events. As a result, uniformly over all distinct place tuples,
\[
 \Pr\big(C_{r,m}N s_{\min}(G_{a_j})^{2d}\le x_j\ \text{for all }j\big)
                   = N^{-k}\prod_j x_j+o(N^{-k}).
 \tag{8}
\]

## 5. Poisson law

Mixed factorial moments of counts on disjoint bounded intervals of \([0,\infty)\) are sums over distinct ordered places. Joint interval probabilities follow from (8) by finite endpoint differencing (use \([0,x]\) for the interval at zero). For any fixed total factorial order \(k\) the moments therefore converge to the products of the interval lengths to their respective orders, since the number of ordered places is \((N)_k\sim N^k\). These determine the independent Poisson counts. Tightness on bounded intervals follows from the first moments, yielding the point-process statement in (3). The probability of no point in \([0,x]\) tends to \(e^{-x}\), giving the asserted minimum law. In particular, accidental exact rank loss has probability tending to zero, by bounding its probability by that of a point in \([0,x]\) and then letting \(x\downarrow0\).

## 6. Allowed coefficient laws

For a fixed centered nondegenerate integer law let \(\ell_0\) be the gcd of its support differences. Its characteristic modulus equals one only at \(\ell_0 u\in\mathbb Z\), by equality in the triangle inequality of unit phases. Away from those frequencies there is a uniform compact gap; at them the second-order expansion gives a quadratic gap, so the first bound in (2) holds for some constant. Its mean-zero local mgf bound follows from the exponential moment. This also covers centering a fixed affine lattice law directly. For the sparse signed law, the characteristic function is \(1-p_n+p_n\cos(2\pi u)\ge0\) for \(p_n\le1/2\), and the mgf is \(1-p_n+p_n\cosh u\). Equation (2) and \(\mathbb E|Z_n|^3=p_n=v_n\) follow directly.

For discrete Gaussian coefficient weight proportional to \(e^{-\pi z^2/t^2}\), write \(q=e^{-\pi/t^2}\). Jacobi's product expresses the characteristic function as
\[
 \prod_{j\ge1}\left(1-\frac{4q^{2j-1}}{(1+q^{2j-1})^2}\sin^2(\pi u)\right).
\]
If \(t\le1\), its first factor suffices since \(v\asymp q\), by summing the coefficient masses. The local mgf and the third absolute moment are bounded by \(1+C v u^2\) for \(|u|\le1\) and \(C v\), respectively, by summing the same Gaussian tails with an \(e^{|z|}\) factor. If \(t\ge1\), the first \(\max(1,\lfloor t^2\rfloor)\) factors have uniformly positive coefficients before \(\sin^2\); their product gives an exponent of order \(t^2\). Here \(v\asymp t^2\), the third moment is \(O(t^3)\), and the mean-zero mgf is at most \(e^{t^2u^2/(4\pi)}\) by the centered Poisson mass maximum. The variance lower bound for large \(t\) follows by summing coefficients in any fixed positive-width fraction of the interval \([t,2t]\), and extends to \(t\ge1\) by continuity. This proves (1)–(2) throughout the stated subpolynomial variance range.

## Reproduction

Run \(\texttt{python3 verify-dyadic-hard-edge.py}\) (standard library). The script verifies exact dyadic subgroup compression and phase parity arithmetic, and the Laguerre normalization ratio and several finite hard-edge constants. These are checks of the identities behind the proof, not evidence about a real system.
