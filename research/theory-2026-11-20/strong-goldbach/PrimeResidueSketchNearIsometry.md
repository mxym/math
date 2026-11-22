# Long prime residue sketches: uniform near-isometry and reflected compression

This is an unconditional operator statement on the **actual primes** in a fixed central interval. The weights may be arbitrary real numbers, chosen with full knowledge of the target or of the primes; no prime progression theorem for the weights themselves is assumed. It extends the scope of the [sharp rough filter](https://github.com/mxym/math/commit/29f772d7) and the local filter mixture analysis as an **upper-norm statement**, but does not give their signed secondary terms. In particular it is not a positive Goldbach lower bound.

Fix \(0<\eta<1/2\), real \(B>0\), nonnegative nonzero \(g\in C_c^\infty(1,2)\). For large even \(N\), write \(L=\log N\), \(T=\log L\), \(Q=N/L^B\), \(W_q=(\log q)g(q/Q)\) for actual prime moduli \(q\), \(G=\sum_{q\ \mathrm{prime}}W_q\), and \(\langle f\rangle=G^{-1}\sum_q W_qf(q)\). Let \(\mathcal P=\{p\ \mathrm{prime}:\eta N\le p\le(1-\eta)N\}\). For arbitrary \(a=(a_p)_{p\in\mathcal P}\in\mathbb R^{\mathcal P}\) set \(A=\sum a_p\), \(\Delta=\sum a_p^2\), and
\[
 A_q(b)=\sum_{p\equiv b(q)}a_p,\qquad E_q(0)=0,\qquad
 E_q(b)=A_q(b)-\frac A{q-1}\quad(b\ne0).
\]
All summands exceed the modulus for sufficiently large \(N\), so the zero class is empty. Put \(V_q(a)=\sum_b E_q(b)^2\), \(\Gamma_q(a)=\sum_b E_q(b)E_q(N-b)\), and \(R_a(N)=\sum_{p+p'=N}a_pa_{p'}\), using ordered pairs. Then uniformly in the target and **all** such vectors,
\[
 \boxed{\quad
 \langle V_q(a)\rangle=\Delta+O(\varepsilon_N\Delta),\qquad
 \langle\Gamma_q(a)\rangle=R_a(N)+O(\varepsilon_N\Delta),\qquad
 \varepsilon_N=\frac{T\log(2T)}{L}.
 \quad}                                                        \tag{1}
\]
Constants depend only on \(\eta,B,g\). Equivalently, the map \(U:a\mapsto(\sqrt{W_q/G}E_q)_q\) satisfies \(\|U^*U-I\|\ll\varepsilon_N\), and \(\|U^*\mathcal J U-J_N\|\ll\varepsilon_N\), where \(\mathcal J\) reflects each residue at \(N-b\) and \(J_N\) is physical reflection compressed to the actual-prime coordinates (its entry is \(1_{p+p'=N}\)). These are operator inequalities because the quadratic forms are real symmetric and the estimates hold for every vector. The corresponding mixed-weight errors are \(O(\varepsilon_N\|a\|_2\|b\|_2)\).

## 1. One kernel for the genuine nonzero aliases

Write \(e(t)=\exp(2\pi i t)\), \(Y=N/Q=L^B\), \(H=2Y\). Fix an even smooth \(\psi\) supported in \((-1,1)\), equal to one on \([-1/2,1/2]\). For \(S(\alpha)=\sum a_pe(p\alpha)\), use the scalar kernel
\[
 \mathcal K(\alpha)=G^{-1}\sum_{q\ \mathrm{prime}} W_q
                   \sum_{h\in\mathbb Z\setminus\{0\}}\psi(h/H)e(-hq\alpha).
\]
Only \(|h|\le H\) can occur. In either congruence \(p+p'\equiv N\pmod q\) or \(p-p'\equiv0\pmod q\), every physical alias \(h\ne0\) has \(|h|\le N/Q\), so the cutoff is exactly one on it. Thus the exact nonzero modular pair contributions are respectively
\[
   \int_0^1 e(-N\alpha) S(\alpha)^2\mathcal K(\alpha)d\alpha,
   \qquad \int_0^1 |S(\alpha)|^2\mathcal K(\alpha)d\alpha.       \tag{2}
\]
The true zero aliases are respectively \(R_a(N)\) and \(\Delta\).

Take disjoint log-major arcs \(\mathfrak M\) of denominator \(r\le R=L^C\) and radius \(R/N\), with \(C\) fixed sufficiently large depending on \(B\) and the desired inverse-log reserve. For \(\alpha\notin\mathfrak M\), every \(-h\alpha\), \(0<|h|\le H\), is outside the large rational arcs of a somewhat smaller logarithmic order at scale \(Q\): a rational approximant there of denominator \(\le L^D\) and error \(\le2L^D/Q\) pulls back to denominator \(\le |h|L^D\) and error \(\le2L^D/(Q|h|)\). Choose \(C>D+B+2\). The ordinary Vinogradov–Vaughan bound for the **unweighted (apart from \(\log q,g\)) genuine modulus primes** then gives \(\mathcal K\ll_A L^{-A}\) on the complement, choosing \(D\) to absorb the \(O(H)\) frequencies. This step uses no property of \(a\). See [Bhowmik–Grimmelt, Proposition 4.1](https://arxiv.org/html/2607.27282v2#S4.SS3).

For \(\alpha=b/r+\beta\in\mathfrak M\), Siegel–Walfisz at the \(Q\)-scale and partial summation give, uniformly to arbitrary inverse-log accuracy,
\[
 \mathcal K(\alpha)=\frac{Q}{G}\int_1^2 g(u)
   \left[\frac{1}{\varphi(r)}\sum_{h\ne0}\psi(h/H)c_r(h)e(-hQu\beta)\right]du
   +O_A(L^{-A}).                                                \tag{3}
\]
The residue is reduced and \(c_r(bh)=c_r(h)\); the modulation costs at most \(1+H Q|\beta|\ll R\) in variation. The sum over \(h\) also costs only a fixed log power; all errors are measured against \(G\asymp Q\). Use Poisson and the complete reduced-numerator expression for \(c_r(h)\). The bracket in (3) is
\[
 \frac H{\varphi(r)}\sum_{c(r)}^*\sum_{j\in\mathbb Z}
      \widehat\psi\bigl(H(j+Qu\beta-c/r)\bigr)-1.              \tag{4}
\]
The \(-1\) removes \(h=0\), because \(c_r(0)=\varphi(r)\) and \(\psi(0)=1\). Fourier transforms use the convention \(\widehat\psi(t)=\int\psi(v)e(-t v)dv\).

On every \(r>1\) arc the absolute value of the averaged (4) is \(O_g(r/\varphi(r))\). To prove this let \(t=Q|\beta|\). If \(t\ge 1/(4r)\), replace the reduced grid by the full grid of spacing \(1/r\) and use \(|\widehat\psi(x)|\ll_D(1+|x|)^{-D}\). On the signed interval with endpoints \(t,2t\), at most \(O(rt+1)\) grid cells are needed, and over one full cell the integral of the periodic sum of this majorant is \(O(1/H)\). The change from \(u\) to \(tu\) costs \(1/t\); multiplying by \(H/\varphi(r)\) gives \(O(r/\varphi(r))\). If \(t<1/(4r)\), the reduced grid avoids zero and its distance from \(tu\) is bounded below by \((m-1/2)/r\) for its \(m\)-th nearest point on either side. The tail sum is \(O((r/H)^D)\) for \(r\le H\), or \(O(r/H)\) for \(r>H\); both suffice after multiplication. For \(r=1\), remove the \(j=0\) term and the same two estimates give \(O(1)\) for what remains.

On the symmetric fundamental interval \([-1/2,1/2]\) take the continuous principal term
\[
     P_0(\alpha)=\frac{QH}{G}\int_1^2 g(u)\widehat\psi(HQu\alpha)\,du .
\]
At the central rational this is exactly the removed \(j=0,r=1\) term; away from the central arc it decays with arbitrary log reserve since \(HQ=2N\). It follows from (3)–(4) and the minor bound that \(\mathcal K-P_0\) is \(O(\log\log(3R))\) on \(\mathfrak M\) and \(O_A(L^{-A})\) off it. Here use the elementary bound \(r/\varphi(r)\ll\log\log(3r)\). In **both** integrals in (2), the principal term \(P_0\) contributes
\[
 \frac{A^2}{G}\int_1^2 g(u)\frac{du}{u}+O_A(\Delta L^{-A})
                =\left\langle\frac{A^2}{q}\right\rangle+O_A(\Delta L^{-A}).      \tag{5}
\]
For the first equality extend the \(\alpha\)-integral to \(\mathbb R\) with a rapidly decreasing tail, using \(\sum|a_p|\le\sqrt N\sqrt\Delta\), then invert the transform. Its physical weight is \(\psi(k/(HQu))=1\) for \(k=p+p'-N\) or \(p-p'\), since \(|k|\le N\). The second equality is ordinary smooth PNT, with arbitrary log reserve chosen after \(B\) since \(A^2/G\ll L^B\Delta\). This identifies the centering exactly to the needed scale, rather than only bounding the central arc.

## 2. A prime-restricted logarithmic major-arc norm for arbitrary weights

Let \(y=N/(2R)\). For each reduced fraction \(\xi\) of denominator at most \(R\), Plancherel after convolution with \(1_{[0,y]}\) gives
\[
 \int_{|\beta|\le R/N}|S(\xi+\beta)|^2d\beta
   \ll y^{-2}\int_{\mathbb R}\left|\sum_{x<p\le x+y}a_pe(\xi p)\right|^2dx.       \tag{6}
\]
Indeed that convolution's Fourier multiplier has absolute value \(\ge 2y/\pi\) on the displayed \(\beta\) interval. For a window meeting the central support, all positions are \(\asymp_\eta N\) on taking \(N\) large. Consider the matrix with rows \(\xi\), columns genuine primes in the window and entries \(\sqrt{\log p}\,e(\xi p)\) (put \(a_p=0\) outside the chosen support). Its row Gram is, by Siegel–Walfisz for the rational difference \(\xi-\xi'\) of denominator \(\le R^2\),
\[
 y\,\mathbb E_{u\in(\mathbb Z/D_0\mathbb Z)^*} e((\xi-\xi')u)+O_M(NL^{-M}),
 \qquad D_0=\operatorname{lcm}(1,\ldots,\lfloor R\rfloor).
\]
The last expression is only a finite **model** average; SW is applied to the actual denominator \(\le R^2\), never to \(D_0\). Any pair of distinct row frequencies is orthogonal on all residues mod \(D_0\). Restricting that full average to uniform units multiplies its squared norm by at most \(D_0/\varphi(D_0)\ll\log(3R)\). Thus the model Gram norm is \(\ll y\log(3R)\), and the entrywise SW errors have operator norm \(\ll_M R^2 NL^{-M}=o(y)\) by taking \(M>3C+1\). Apply this estimate to the column vector \(a_p/\sqrt{\log p}\). For each window the sum over \(\xi\) on the right of (6) is bounded by \(\ll y\log(3R)\sum_{x<p\le x+y}a_p^2/\log p\). Integrate over \(x\), so each \(p\) is counted for exactly length \(y\). We obtain
\[
   \int_{\mathfrak M}|S(\alpha)|^2d\alpha
        \ll_\eta \frac{\log(3R)}{L}\Delta,                   \tag{7}
\]
with no bound or structure on the input vector.

## 3. Actual centering and consequence

Multiply (7) by the bound \(O(\log\log(3R))\) from (4); on the remaining arcs use Parseval \(\int|S|^2=\Delta\). Equations (2) and (5) now bound the centered nonzero alias terms in absolute value by \(O(T\log(2T)\Delta/L)\). To pass to the specified centered variance, use \(\sum_b A_q(b)^2-A^2/(q-1)=V_q(a)\). For the reflected term the corresponding principal is \(v_N(q)A^2\), with \(v_N(q)=(q-\nu_q(N))/(q-1)^2=1/q+O(q^{-2})\), and the possible extra linear term is \(-2A E_q(N)/(q-1)\) if \(q\nmid N\). These all cost \(O_A(\Delta L^{-A})\) uniformly: \(|A|\le\sqrt N\sqrt\Delta\), \(|A_q(b)|\ll\sqrt{N/q+1}\sqrt\Delta\) by counting integer lifts, so the linear bound is \(\ll \Delta N^{-1/2} L^{3B/2}+\Delta N^{-1}L^{2B}\). This proves (1).

At a putative bad even target, \(J_N=0\) on the genuine-prime coordinates; simultaneously **every** real weighting of the actual central primes then has reflected covariance \(O(\varepsilon_N\Delta)\), while its ordinary variance is \((1+O(\varepsilon_N))\Delta\). Equivalently, even and odd projected energies are both \((1/2+O(\varepsilon_N))\Delta\) for all such weightings. Thus trying to pay the known alias deficit via the total unsigned variance cannot work merely by finding a different weight on the same actual prime support. This does not give the one-sided sign on the residual order-\(N\mathfrak S(N)\) phase, and does not disprove a different modulus range, arithmetic detector altering the kernel, or any approach using genuinely independent parity-sensitive information. The earlier local-calibration proof still has a sharper \(O(T/L)\) envelope on its narrower class and a proved signed example, not superseded in those respects.

### Compatibility with the sharper fixed smooth weight

For the special \(a_p=(\log p)w(p/N)\), with fixed nonnegative smooth \(w\) supported within the central interval, \(\Delta=(1+o(1))NL\int w^2\). Thus (1) allows an error \(O_w(NT\log(2T))\). The separate [prime-modulus additive calculation](https://github.com/mxym/math/commit/b73b2635) gives the much more precise *signed* correction \(-N\mathfrak S(N)\int w(t)w(1-t)dt+O(e^{-B}N\mathfrak S(N))+o_B(N)\), whose size is at most \(O_w(NT)\). These estimates are compatible for every even target. Formula (1) is stronger in the class of weights, weaker in its error and silent about its sign. An absolute upper envelope below the unconditioned calibrated debit could not hold uniformly over weights, already by that signed calculation, irrespective of whether any bad target exists.

### Comparison with the prime-modulus large sieve

[Iwaniec, *The large sieve with prime moduli*, Rev. Mat. Iberoam. 38 (2022), Thms. 2 and 5](https://ems.press/content/serial-article-files/39116), is directly related prior art for arbitrary weights and genuine prime moduli. In our scale \(Q=N/L^B\), its Thm. 2 applies to the uncentered nonzero additive samples \(S(a/q)\): choose its smoothness mask \(P\) containing all primes below \(D=Q/\sqrt N\), which are below the central support. The theorem's factor \(Q^2/\log D\) gives \(\langle V_q(a)\rangle\ll\Delta\) after the logarithmic modulus weight and the \(q^{-1}\) from finite Parseval. It neither gives the diagonal-asymptotic error in (1) nor retains the signed target reflection. The cited Thm. 5 integrates offset strips \([1/(9cCD),1/(cCD)]\), subject to \(DC^2\le N\); for \(C=R\) these do not include the complete central intervals used in (6)–(7). Its density saving is of square-root type, so we do not use it as a substitute for the prime-specific small-rational Gram. No priority for either the large sieve or the short-window inequality is asserted.
