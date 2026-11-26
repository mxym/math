# Exact all-length gap of the odd twisted deformed t–J chain

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

Consider the full local Hamiltonian of [Hagendorf §4.2](https://arxiv.org/abs/1207.0357), without imposing a special translation sector. For every odd length \(N\ge3\), twist \(\pi\), and real \(|\zeta|>1\), set \(L=N-1\) and \(t=\zeta^2-1\). Its spectral gap is exactly
\[
\Delta_N(\zeta)=\min\left\{4+2t(1-\cos(\pi/N)),\ \lambda_{\min}(M_N(t))\right\},
\]
where \(M_N(t)=t A+\operatorname{diag}(6+2\zeta,8,\ldots,8,6-2\zeta)\), and \(A\) is the size-\(L\) Laplacian with weight 2 on each edge of the path and weight 1 on the edge joining the two ends (parallel to the path edge at \(L=2\)). The other \(\zeta\ne0\) cases at twists 0 and \(\pi\) are in [the original kernel and gap analysis](DEFORMED-TJ.md). The two branches cross exactly once at every odd length. This result does not assert the gap at arbitrary twists.

The [circular exclusion argument](CIRCULAR-EXCLUSION-CYCLES.md#consequence-for-the-odd-pi-twisted-deformed-tj-chain) reduces the full gap to one-hole blocks. The [one-hole analysis](ODD-PI-TJ-GAP.md#one-hole-gauge-and-finite-matrix) gives the stated two candidates, from pure background and one minority spin. The [even-content argument](ODD-PI-TJ-FINITE-CERTIFICATES.md#analytic-even-content-exclusion-at-every-odd-length) excludes mixed even \(k\) at every length. Here we exclude all mixed odd \(3\le k\le L/2\). For \(7\le N\le41\), after the content comparison below, the [quick exact checker](verify-odd-pi-gap-three-minority.js) verifies just three-minority content at 18 odd lengths (36 interval certificates) using the [finite certificate inequalities](ODD-PI-TJ-FINITE-CERTIFICATES.md#odd-mixed-sectors). A slower companion independently tests every mixed content through 41. At \(N=3,5\) the [explicit small cases](ODD-PI-TJ-GAP.md#three-sites) apply. For \(N\ge43\), the proof below uses uniform analytic inequalities and does not enumerate lengths.

## Reduction to three minority spins

Take \(\zeta>1\) by symmetry, \(\nu=(\zeta-1)/(\zeta+1)=e^{-a}\) with \(a>0\), and let \(\phi_k\) be the normalized open-chain kink vector with amplitudes proportional to \(\nu^{\operatorname{inv}(w)}\) on content-\(k\) words. The inversion orientation may be reversed throughout without changing rotation overlaps. Denote the one-step cyclic rotation by \(R\). We show that for any rotation \(R^u\), the autocorrelation \(\langle\phi_k,R^u\phi_k\rangle\) is nonincreasing for \(0\le k\le L/2\). Thus the squared projection \(p_0(k)\) of \(\phi_k\) on the rotation-invariant subspace, the average of these autocorrelations, is at most \(p_0(3)\) for the sectors in question.

Put \(G_m(z)=\prod_{i=0}^{m-1}(1+z\nu^{m-1-2i})\). The rotation autocorrelation equals
\[
\frac{[z^k]\,G_u(z)G_{L-u}(z)}{[z^k]\,G_L(z)}.
\]
In fact splitting each word after \(u\) letters makes its doubled internal inversions plus the between-part inversions from both rotations. If the pieces carry \(r,k-r\) ones, the sum between pieces is \(k(L-k)-r(u-r)-(k-r)(L-u-k+r)\), so the common \(\nu^{k(L-k)}\) cancels from the centered coefficient ratio.

For even \(m\), \(G_m\) is a product of reciprocal pairs \(1+A z+z^2\), with \(A=\nu^d+\nu^{-d}\) for \(d=1,3,\ldots,m-1\). For odd \(m\) the positive exponents are \(2,4,\ldots,m-1\), and there is a factor \(1+z\). If both split sizes are odd, pair the two \(1+z\) factors as \(d=0\). In either parity, after sorting the split pair exponents its \(i\)-th exponent is at most \(2i-1\): merge two odd lists starting at 1, or a zero followed by two even lists starting at 2. The comparison is therefore a succession of increases \(A\mapsto A'\ge A\) in individual reciprocal quadratics.

For each increase, writing \(B_j\) for the coefficients of the product of the other pairs, the ratio of the before and after coefficients at \(k\ge1\) is
\[
1-\frac{A'-A}{ A'+(B_k+B_{k-2})/B_{k-1} }.
\]
The expression \((B_k+B_{k-2})/B_{k-1}\) is nonincreasing as \(k\) approaches the center from the left. Here is a proof that handles all parameters. Recenter \(B\) as a symmetric convolution of kernels \(K=(1,A,1)\) on \(\mathbb Z\). If \(B\) is obtained by starting from \(\delta_0\), then its two adjacent shifts summed, denoted \(C\), are obtained by starting from \(\delta_{-1}+\delta_1\). On the nonnegative half-line, initially \(B_i C_j-B_j C_i\ge0\) for \(i<j\). Each symmetric convolution is represented there by the folded matrix with entries \(K(j-i)+K(j+i)\) for \(i>0\), and \(K(j)\) at \(i=0\). This tridiagonal matrix has nonnegative \(2\)-by-\(2\) minors: the only adjacent principal minor at the boundary is \(A^2-2\), the others there are \(A^2-1\), and every other minor has no nonzero negative-product term. The ordering of the pair of columns is preserved by multiplying such a matrix by the two-column matrix \((B,C)\); this follows by expanding the resulting \(2\)-by-\(2\) minors over pairs of intermediate rows. Thus \(C_j/B_j\) is nondecreasing away from the center on the half-line. By symmetry this proves the claimed behavior approaching the center. The ratio at \(k=0\) is 1. Multiplying all successive coefficient ratios (nonnegative and nonincreasing up to the center) proves the autocorrelation comparison.

## Three-spin defect controls the rank-one comparison

Let \(\alpha=2(1-\cos(\pi/N))\), \(s=\alpha t\), and \(\xi=La/2\). In odd content only momentum 0 need be tested, by Perron–Frobenius. The open-chain kink gap from [Koma–Nachtergaele, Proposition 2](https://arxiv.org/pdf/cond-mat/9512120#page=8) gives \(g=4+2t(1-\cos(\pi/L))\ge4+s\). The rotation term has gap at least \(r=2t(1-\cos(2\pi/L))\ge4s\) on the complement of its invariant subspace: \(\sin(\pi/L)\ge2\sin(\pi/(2N))\) follows from \(\sin u\ge u-u^3/6\), \(\sin v\le v\), and \(6L^2\ge N\pi^2\). By the [rank-one test](ODD-PI-TJ-FINITE-CERTIFICATES.md#odd-mixed-sectors), it is sufficient that
\[
1-p_0(k)\ge \frac{T(g+r-T)}{gr},\qquad T=\min(s,4),
\]
which then bounds that block below by \(4+T\). This target dominates the smaller candidate (the one-minority constant trial is below 8). The expression on the right decreases in \(g,r\) as both exceed \(T\). Using \(g\ge4+s,r\ge4s\) reduces its upper bound to \((1+s)/(4+s)\) for \(s\le4\), or \(5/(4+s)\) for \(s\ge4\).

To bound \(1-p_0(3)\), for a fixed split index \(u\) write \(v=|2u/L-1|\) and \(q=\cosh(v\xi)/\cosh\xi\). The ratio of the split and full \(j\)-th power sums of the segment weights is \(c_j=\cosh(jv\xi)/\cosh(j\xi)\), by summing each geometric progression. Thus \(c_1=q\), \(c_2=q^2-(1-q^2)/\cosh(La)\), and \(c_3\le q^3\), by the double- and triple-angle identities. Let \(S_j=\sinh(jLa)/\sinh(ja)\) be the full sums and \(e_3=[z^3]G_L(z)\). Newton's third identity gives
\[
1-\frac{[z^3]G_uG_{L-u}}{e_3}
\ge (1-q^3)\left(1-\frac{2S_1S_2}{6 e_3\cosh(La)}\right).
\]
Indeed the numerator \(6(e_3-[z^3]G_uG_{L-u})\) is \(S_1^3(1-q^3)-3S_1S_2(1-qc_2)+2S_3(1-c_3)\); here \(q(1-q^2)/(1-q^3)\le2/3\) on \([0,1)\), and equality at \(q=1\) is treated directly. The centered geometric progression gives
\[
e_3=\frac{\sinh(La)\sinh((L-1)a)\sinh((L-2)a)}{\sinh a\,\sinh(2a)\,\sinh(3a)}.
\]
For example, the general formula \(e_k=\prod_{i=1}^k \sinh((L-i+1)a)/\sinh(ia)\) follows by induction on the geometric progression length, splitting off its last weight; the identity after simplification is the addition law for \(\sinh\). Substitution now gives
\[
\frac{2S_1S_2}{6e_3\cosh(La)}
=\frac23\,\frac{\sinh(3a)\sinh(La)}{\sinh((L-1)a)\sinh((L-2)a)}
\le\frac{8L}{3(L-1)(L-2)}<\frac7{100}\quad(L\ge42).
\]
Use \(\sinh(La)/\sinh((L-1)a)\le e^a L/(L-1)\) from concavity of \(1-e^{-2xa}\), \(e^a\sinh(3a)\le\sinh(4a)\), and monotonicity of \(\sinh x/x\). Averaging over the \(L\) rotations therefore bounds the defect by
\[
1-p_0(3)\ge\tfrac{93}{100}\left[1-\frac1L\sum_{u=0}^{L-1}
\left(\frac{\cosh((2u/L-1)\xi)}{\cosh\xi}\right)^3\right].
\]

## Uniform control from three elementary moments

Each term of the bracket is nondecreasing in \(\xi\), since \(\cosh(v\xi)/\cosh\xi\) is nonincreasing for \(0\le v\le1\). By \(a=2\operatorname{artanh}(1/\zeta)\ge2/\zeta\), we have \(\xi\ge L/\sqrt{1+t}\). Also \(L^2\alpha>(153/50)^2=9.3636\) and \(\alpha<3/500=0.006\) for \(N\ge43\): use \(\alpha^{1/2}=2\sin(\pi/(2N))\), the sine bounds, and \(3.14<\pi<22/7\). In detail,
\[
L\sqrt\alpha\ge (L/N)\pi(1-\pi^2/(24N^2))>153/50
\]
since the right side increases in \(N\) and the lower bound obtained with \(N=43\), \(\pi>3.14\), \(\pi^2<10\), already suffices. It follows that for \(s\ge4\),
\[
\xi^2\ge \frac{9.3636}{s+0.006}\ge\frac{93}{10s}.
\]
For \(s\le4\) it follows instead that \(\xi^2\ge93/40\).

For \(0\le v\le1\) the nonnegative Taylor coefficients of \(\cosh\) give \(\cosh(v\xi)\le1+v^2(\cosh\xi-1)\). If \(\xi^2\ge93/(10s)\), put \(\eta=93/(20s+93)\), so \(1-\operatorname{sech}\xi\ge \xi^2/(2+\xi^2)\ge\eta\). Thus
\[
1-\Big(\frac{\cosh(v\xi)}{\cosh\xi}\Big)^3
\ge 3\eta(1-v^2)-3\eta^2(1-v^2)^2+\eta^3(1-v^2)^3.
\]
For \(v=|2u/L-1|\) over \(u=0,\ldots,L-1\), the averages of \((1-v^2)^j\) for \(j=1,2,3\) are respectively
\[
\tfrac23(1-L^{-2}),\qquad \tfrac8{15}-\tfrac8{15L^4},\qquad
\tfrac{16}{35}+\tfrac{16}{15L^4}-\tfrac{32}{21L^6}.
\]
These identities follow by expanding the powers and summing powers of \(u\) (equivalently the first three even grid moments are \(1/3+2/(3L^2)\), \(1/5+4/(3L^2)-8/(15L^4)\), and \(1/7+2/L^2-8/(3L^4)+32/(21L^6)\)). Since \(L\ge42\), the bracket average is at least
\[
F(\eta)=2(1-42^{-2})\eta-\tfrac85\eta^2+\tfrac{16}{35}\eta^3.
\]
For \(s\ge4\), \(0<\eta\le93/173\), and the ratio of this bound to \(5/(s+4)\) is
\[
\frac{F(\eta)(s+4)}5
=\frac1{10}\left[2(1-42^{-2})-\tfrac85\eta+\tfrac{16}{35}\eta^2\right]\left[\tfrac{93}{10}+\big(8-\tfrac{93}{10}\big)\eta\right].
\]
Both factors in square brackets are positive and decreasing on the indicated interval. The worst ratio is at \(s=4\), and \( (93/100)F(93/173)>5/8\) by direct rational substitution. This gives \(1-p_0(3)\ge 5/(s+4)\) for \(s\ge4\). For \(s\le4\), the bound \(\xi^2\ge93/40\) permits the same fixed choice \(\eta=93/173\), and gives \(1-p_0(3)\ge5/8\ge(1+s)/(4+s)\). Content monotonicity now rules out every higher odd sector. This completes the theorem.

The earlier fixed [scalar-polynomial checker](verify-odd-pi-gap-all-lengths.js) is kept as an independent cross-check for the large-length inequality; the uniform proof above does not depend on it.


## The two branches switch exactly once at every length

For \(N=3\) the explicit formula gives the unique crossing [directly](ODD-PI-TJ-GAP.md#three-sites). For \(N\ge5\) take \(u=4/t\), \(\alpha=2(1-\cos(\pi/N))\), and \(a_0=2-\alpha\). Work with \((M_N-P_N I)/t\). Remove the field at the two ends temporarily, and use the even and odd subspaces of path reflection, with normalized endpoint coordinates \((e_1+e_L)/\sqrt2\) and \((e_1-e_L)/\sqrt2\). The endpoint diagonals are \(u/2+a_0\) and \(u/2+a_0+2\); each couples by \(-2\) to its respective interior coordinate. The endpoint field restores a single cross coupling of magnitude \(2|\zeta|/t\). The interior matrices are fixed matrices plus \(u I\) and are strictly positive even at \(u=0\). In fact setting the endpoint values to zero leaves the weight-2 path with Dirichlet endpoints, whose least eigenvalue is \(4(1-\cos(\pi/(L-1)))>\alpha\) before subtracting \(\alpha\). The sine eigenvectors give this value directly.

After eliminating the interiors, let the two endpoint diagonals be \(u/2+X(u)\) and \(u/2+Y(u)\). Then \(X=a_0-4h_e(u)\), \(Y=a_0+2-4h_o(u)\), where \(h_e,h_o\) are the first diagonal entries of the positive interior resolvents. Both are strictly increasing since each \(h\) decreases strictly. Moreover \(Y(u)\ge2\): at \(u=0\) the seam edge alone contributes twice the squared odd endpoint coefficient, and the weight-2 path form dominates \(\alpha\) on the odd subspace. Indeed that subspace has sum zero and the first nonzero weight-2 path eigenvalue is \(4(1-\cos(\pi/L))>\alpha\). Taking the minimum over interior coordinates proves \(Y(0)\ge2\). At \(u=0\), \(X(0)<0\) by testing a constant nonzero vector in the even subspace before the interior elimination. As \(u\to\infty\), \(X(u)\to a_0>0\).

Since \(4\zeta^2/t^2=u+u^2/4\), the remaining two-by-two determinant is
\[
(u/2+X)(u/2+Y)-u-u^2/4
=(Y+u/2)\left[X+\frac{u(Y-2)}{2Y+u}\right].
\]
The bracket is strictly increasing in \(u\), as \(X\) is strictly increasing and the correction is nondecreasing in both \(u\) and \(Y\) for \(Y\ge2\). It starts negative at \(u=0\), and becomes positive for sufficiently large \(u\). Its unique zero decides positivity because the odd diagonal \(Y+u/2\) is positive. Therefore the pure-wave branch is the gap at weak coupling and the one-minority branch at strong coupling, with a unique tie. This also explains the uniqueness for the two previously computed small-length polynomials.


For completeness the transition coupling \(t_*(N)\) satisfies \(t_*/N^2\to4/\pi^2\). At \(t\ge16L\), put \(\delta=32/L\) and compare \(M_N\) to \((8-\delta)I\). In the same reflection bases its diagonal blocks are \(tA_e+\delta I-2P_e\) and \(tA_o+\delta I-2P_o\), where \(P_e,P_o\) project onto the respective endpoint coordinate. The odd block is at least \((2t-2)P_o+\delta I\) by the seam term, so the Schur complement subtracts at most \(4(t+1)/(2t-2)\le6\) times \(P_e\) from the even block. For an even reflected vector \(f\) in full coordinates, the mean and the telescoping difference bound give
\[
2|f_1|^2\le 4\|f\|^2/L+4L\sum_{i=1}^{L-1}|f_i-f_{i+1}|^2
\le 4\|f\|^2/L+2L\langle f,A_e f\rangle.
\]
Thus \(tA_e+\delta I-8P_e\succeq0\). Combined with the constant trial, \(8-32/L\le \lambda_{\min}(M_N)\le8-4/L\) on this range. At large \(N\), take \(t=(4-32/L)/\alpha\ge16L\); the pure wave is still no higher, giving \(4-32/L\le\alpha t_*\le4-4/L\). This proves the limit.
