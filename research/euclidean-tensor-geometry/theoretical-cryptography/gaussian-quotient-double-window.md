# The joint phase and entropy window for Gaussian mixing on random quotient tori

Fix a full-rank Euclidean lattice \(\Lambda\subset\mathbb R^d\), with \(d\ge1\) and covolume \(V\). Let \(\lambda>0\) be the shortest nonzero length in \(\Lambda^*\), and let \(N_1\) be the number of vectors of that length, counting both signs. Let \(s=s_m>0\) be a Gaussian width in the convention \(g_s(x)=s^{-d}e^{-\pi\|x\|^2/s^2}\).

For each \(m\), take a full sublattice \(\Gamma=\Gamma_m\subseteq\Lambda\) whose additive quotient is identified with a finite field \(F\) of cardinality \(Q=Q_m\). Sample \(A\in F^{r\times m}\) with independent uniform entries and take the lattice
\[
      \Lambda_A=\{z\in\Lambda^m:A(z\bmod\Gamma)=0\}.
\]
The identifications need only respect addition; the field structure supplies the hash. Write \(D_A\) for the TV distance of the centered spherical Gaussian on \(\mathbb R^{dm}\) of width \(s\), reduced modulo \(\Lambda_A\), from probability Haar measure on its torus.

**Theorem.** Suppose as \(m\to\infty\) that
\[
 \frac{\lambda_1(\Gamma)}{s\sqrt{\log m}}\longrightarrow\infty,\qquad
 m e^{-2\pi s^2\lambda^2}\longrightarrow a\in[0,\infty),\qquad
 \frac{r\log Q-m(\log(s^d/V)+d/2)}{\sqrt m}\longrightarrow b\in\mathbb R .
                                                                         \tag{1}
\]
Put \(v=N_1a\), \(c=1-\Phi(b/\sqrt{d/2})\), with \(\Phi\) the standard normal CDF. Then
\[
       D_A\ \xrightarrow{L^1\ \mathrm{over}\ A}\ 
                \mathbb E\big(1-c\,e^{\sqrt v Z-v/2}\big)_+,
                \qquad Z\sim N(0,1).                                    \tag{2}
\]
For \(v=0\) this is \(1-c\). For \(v>0\) it equals
\[
    \Phi\!\left(\frac{v/2-\log c}{\sqrt v}\right)
       -c\,\Phi\!\left(\frac{-v/2-\log c}{\sqrt v}\right).
\]
The bottom phase and top entropy transitions combine in the same clipped likelihood, rather than as two additive TV errors. For \(v>0\) and \(0<c<1\), (2) is strictly greater than both the phase-only distance and \(1-c\), and strictly less than their sum: apply the pointwise comparisons of \((1-cL)_+\) with \((1-L)_+\) and \((1-L)_++(1-c)L\), and use \(\mathbb E L=1\) and both tails of the lognormal. In particular the expression separates the shortest dual shell of the fixed base lattice from the spherical Gaussian energy dispersion \(d/2\).

For a number-field ring of integers \(R\) of fixed degree \(d\), one can take the canonical \(\Lambda=\iota(R)\) and \(\Gamma=\iota(\mathfrak p)\) for prime ideals \(\mathfrak p\). The algebraic norm and arithmetic-geometric mean give \(\lambda_1(\Gamma)\ge\sqrt d\,(N\mathfrak p)^{1/d}\), so \(Q^{1/d}/(s\sqrt{\log m})\to\infty\) is sufficient for the first condition, with \(F=R/\mathfrak p\). No inertness or principal-ideal hypothesis is needed. For \(\Lambda=\mathbb Z\), any growing prime \(Q\) with \(\Gamma=Q\mathbb Z\) and \(Q/(s\sqrt{\log m})\to\infty\) supplies examples; when \(a>0\), primes of polylogarithmic size with exponent bigger than one allow \(r\) to be rounded with \(o(\sqrt m)\) error in the last numerator.

**Prior and scope.** [Luzzi–Ling–Bloch, *Optimal rate-limited secret key generation from Gaussian sources using lattices*, Theorem 1 and Appendix C](https://arxiv.org/abs/2206.10443) gives \(L^1\)/KL secrecy-good lattices up to the volume-to-noise threshold \(2\pi e\), using a fine/coarse Construction A decomposition. This theorem treats actual TV, equal to half the \(L^1\) flatness factor, for a specified random ensemble in a simultaneous fixed-base phase and second-order volume window. It does not improve their first-order threshold or their KL result, and does not concern worst-case lattices, a security reduction, or any operating system. Compare the conditional hash information-spectrum bounds in [module-information-spectrum.md](module-information-spectrum.md); here phase Haar, unlike the comparison there, is not the actual phase marginal. Equations (3)–(4) below retain that difference.

## 1. A two-part conditional hash comparison

We first give the comparison that will be used. Suppose \(U\) has law \(P_U\ll H\) with density \(L(U)\) relative to a probability \(H\). Given \(U\), a finite \(X\in F^m\) has an arbitrary conditional distribution. Independently draw the uniform matrix \(A\) and compare \(P_A=\mathcal L(U,AX\mid A)\) with \(H\times U(F^r)\). Let \(K=r\log Q\), and for a positive cutoff \(\eta\), put
\[
   I=-\log P(X\mid U),\quad
   G=\{I\ge K+\eta\},\quad B=\{I<K-\eta\},\quad
   g(u)=\Pr(G\mid U=u).
\]
Write \(P_{A,G}\) for the pushed-forward subprobability of \(G\) and \(\widetilde P_G=g(u)P_U(du)\,U(F^r)\) for its shaped uniform comparison. Then
\[
      \mathbb E_A\|P_{A,G}-\widetilde P_G\|_1\le e^{-\eta/2}.            \tag{3}
\]
For each \(u\) this is the standard second moment calculation for a subprobability of mass \(g(u)\) and maximal atom at most \(e^{-K-\eta}\), using exact \(Q^{-r}\) collisions for distinct inputs. In detail the expected squared output error relative to \(g(u)Q^{-r}\), multiplied by \(Q^r\), is at most \(g(u)e^{-\eta}\). Cauchy–Schwarz and integration in \(P_U\) give (3).

Set
\[
     F_G=\mathbb E_H(1-L(U)g(U))_+,\qquad
     E_A=\|P_{A,G}-\widetilde P_G\|_1 .
\]
For every \(A\),
\[
 F_G-E_A-\Pr((G\cup B)^c)-e^{-\eta}
    \ \le\ d_{\rm TV}(P_A,H\times U(F^r))
    \ \le\ F_G+E_A.                                                    \tag{4}
\]
To prove the upper bound use the negative part against \(H\times U(F^r)\): adding discarded source mass cannot increase it, and changing \(P_{A,G}\) by its shaped comparison costs at most \(E_A\). For the lower bound, conditional on \(u\), the points defining \(B\) have mass greater than \(e^{-K+\eta}\), so their image has cardinality at most \(e^{K-\eta}\). The combined set of these images over \(u\) therefore has reference measure at most \(e^{-\eta}\). Off that set, adding the \(B\) mass has no effect on the negative part. The middle band costs at most its probability, and removing the small reference set costs at most its reference measure. This proves (4) without assuming independence of \(I\) and \(U\), or adding the bottom and top TV errors.

## 2. Phase law and residue information

Choose a bounded fundamental region \(\mathcal F\) of \(\Lambda\), half-open up to null sets, and write one Gaussian draw as \(Y=u+z\) with \(u\in\mathcal F,z\in\Lambda\). Base Haar measure \(H_0\) is Lebesgue measure divided by \(V\) on \(\mathcal F\). The phase density relative to it is
\[
        h_s(u)=V\sum_{z\in\Lambda}g_s(u+z)
              =\sum_{w\in\Lambda^*}e^{-\pi s^2\|w\|^2}e^{2\pi i w\cdot u}.
\]
Fourier orthogonality gives \(\int(h_s-1)=0\) and \(\int(h_s-1)^2=(N_1+o(1))e^{-2\pi s^2\lambda^2}\) under \(H_0\). Also \(\|h_s-1\|_\infty=O_\Lambda(e^{-\pi s^2\lambda^2})\): factor out the shortest shell in the absolutely convergent uniform bound for \(s\ge1\). The second assumption in (1) implies \(s\to\infty\).

For the product at \(m\) coordinates put \(L_m(u)=\prod_i h_s(u_i)\). If \(\rho=e^{-\pi s^2\lambda^2}\), the bounded expansion of the logarithm yields
\[
 \mathbb E_{H_0}\log h_s=-(N_1+o(1))\rho^2/2,\qquad
 \operatorname{Var}_{H_0}(\log h_s)=(N_1+o(1))\rho^2 .
\]
Under \(H_0^{\otimes m}\) the sum \(\log L_m\) consequently converges in distribution to \(N(-v/2,v)\). For \(v>0\) this follows from the triangular-array Lindeberg condition, since each centered summand is uniformly \(O(\rho)\); for \(v=0\) use the second moment. Under the actual phase law \(h_s\,dH_0\), the mean of \(\log h_s\) is \(O(\rho^2)\) (use \(\int(h_s-1)=0\)) and its variance is \(O(\rho^2)\). Therefore
\[
               m^{-1/2}\log L_m(U)\ \longrightarrow 0
               \quad\text{in actual phase probability}.              \tag{5}
\]

The conditional probability of an integer part \(z\) given \(u\) is \(Vg_s(u+z)/h_s(u)\). Its self-information is
\[
          \log(s^d/V)+T+\log h_s(u),\qquad
          T=\pi\|Y\|^2/s^2.
\]
Unconditionally \(T\) has the law of \(\chi_d^2/2\), hence mean and variance \(d/2\). Uniformly over the phase \(u\), the first three conditional moments of \(T\) tend to the corresponding unconditional moments as \(s\to\infty\). To see this, apply Poisson summation to \(x\mapsto\pi^j\|x\|^{2j}e^{-\pi\|x\|^2}\) scaled to mesh \(1/s\) on \((u+\Lambda)/s\), for \(j=0,1,2,3\). The zeroth dual term is the continuous integral in every case, and the sum of absolute nonzero terms tends to zero since the Fourier transforms are Schwartz and the lattice is fixed. Dividing by the \(j=0\) sum handles normalization. In particular the uniform centered third absolute moments are bounded and the conditional variances tend uniformly to \(d/2>0\).

Given the full phase vector \(U\), the energies \(T_i\) are independent. The one-dimensional Berry–Esseen inequality for independent summands gives a conditional normal approximation with error \(O(m^{-1/2})\), uniformly in \(U\), after centering by the conditional mean and scaling by the conditional standard deviation. This standard deviation divided by \(\sqrt m\) tends uniformly to \(\sqrt{d/2}\). The conditional-mean offset
\[
       m^{-1/2}\sum_i(\mathbb E[T_i\mid U_i]-d/2)
\]
tends to zero in \(L^2\) under the actual phase law: the summands are iid and centered there by total expectation, with variance tending to zero by the uniform first-moment limit. Together with (5) this proves the following for the **integer parts**: the conditional probability, given the phases, that their joint self-information lies below \(r\log Q\pm 2\log m\) tends in \(L^1(P_U)\) to \(\Phi(b/\sqrt{d/2})=1-c\). Indeed the threshold shift after centering and rescaling tends in phase probability to its prescribed constant, and the probabilities are bounded.

We also need this for the **residue** vector \(X=(z_i\bmod\Gamma)_i\). Write \(\ell=\lambda_1(\Gamma)\). With probability \(1-o(1)\), all continuous Gaussian blocks \(Y_i\) have norm at most \(\ell/4\), by a Gaussian tail bound and the first condition in (1). On this event, for any nonzero \(w\in\Gamma\),
\(\|Y_i+w\|^2-\|Y_i\|^2\ge\|w\|^2/2\). Thus the residue atom at the observed point differs from the integer atom by a ratio between one and \(1+\sum_{w\in\Gamma\setminus\{0\}}e^{-\pi\|w\|^2/(2s^2)}\) per coordinate. This nonzero sum is \(O_d(e^{-\pi\ell^2/(4s^2)})\) for \(\ell/s\ge1\): split off half the exponent and bound the rest with the packing count \((1+2R/\ell)^d\) for lattice points of norm at most \(R\). By (1) its product effect changes joint self-information by \(o(1)\). On the complement use only its \(o(1)\) probability. Consequently the same cutoff conclusion holds for residue self-information in \(L^1(P_U)\), using the integer-part result also with thresholds shifted by \(\pm1\). The middle band has probability \(o(1)\).

## 3. Application to the random lattice torus

The matrix is surjective with probability \(1-o(1)\). Indeed the quotient satisfies \(VQ\ge v_d(\ell/2)^d\), where \(v_d\) is the Euclidean unit-ball volume: the lattice \(\Gamma\) has disjoint open balls of radius \(\ell/2\), so the ball volume fits in its quotient torus. By (1),
\(\log Q-(\log(s^d/V)+d/2)\to+\infty\), and hence \(Q^{r-m}=o(1)\). The standard random-field matrix rank bound gives failure probability at most \(\sum_{j=0}^{r-1}Q^{j-m}\).

For a full-row-rank \(A\), represent a point on \(\mathbb R^{dm}/\Lambda_A\) by its phase \(U\in\mathcal F^m\) and by its integer part's syndrome \(A(z\bmod\Gamma)\in F^r\). Haar measure is \(H_0^{\otimes m}\) times uniform syndrome, since a fundamental region is the union of \(Q^r\) translates of \(\mathcal F^m\) by the \(\Lambda_A\)-coset representatives of \(\Lambda^m\). This agrees with the joint hash representation of the actual wrapped Gaussian.

Apply (4) with \(\eta=2\log m\). Section 2 gives \(\mathbb E_{P_U}|g(U)-c|\to0\) and middle probability \(o(1)\); replacing \(g\) by \(c\) in \(F_G\) costs at most this \(L^1(P_U)\) difference. Equation (3) gives a vanishing expected error. By the base-phase limit under Haar,
\(\mathbb E_{H_0^{\otimes m}}(1-c L_m)_+\) tends to the expression (2), since the function of \(\log L_m\) being integrated is bounded and continuous. The comparison holds in mean absolute error over matrices, and the exceptional non-surjective matrices cost at most their \(o(1)\) probability for the torus distance. This proves (2). Completing the square for the truncated lognormal integral gives the stated closed form.

**Replay.** Run `python3 verify-gaussian-quotient-double-window.py`. It checks the two-part comparison on exact small conditional sources and the clipped-normal integral numerically, and uses no actual cryptographic system or parameter choice. The asymptotic proof is independent of the checks.
