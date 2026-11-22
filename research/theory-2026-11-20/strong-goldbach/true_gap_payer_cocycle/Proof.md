# Transporting the calibrated payer across the genuine Goldbach gap

Use the [thin direct gap](../thin_true_giant_gap/Proof.md), including its genuine fixed-target prime average. Thus \(N=2x\) is even, \(J=xJ_0\subseteq[x,1.5x]\), \(P=N-y\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), \(\xi=.10\), and \(\Delta=100\log\ell/\ell^2\). Let the pair family \(\mathcal P_y\) retain its literal membership and let the odd payer have fixed \(m\ge3\) and disjoint genuine prime exponent bands all in \((.74\epsilon,.78\epsilon)\), with \(0<\epsilon<\min(.005,.04/m)\) fixed. This is one admitted choice of the payer in the prior score, not a claim about every permitted payer. Write \(V_N(z),V_z,H\) for the two Euler factors and rough harmonic prefix in that note. In particular \(H=\sum_{s\le x^\xi}R_z(s)\log s/s\).

For \(0\le t\le 2\Delta\), define the **actual** model at gap parameter \(t\) by
\[
 R_\pm^{(t)}(y)=\sqrt y\,x^{\pm t},\qquad
 J_c^{(t)}(y)=H/V_z+\tfrac12\!\left[
   \log^2\left(\frac{y}{cR_+^{(t)}(y)}\right)-(\xi L)^2\right],
 \qquad
 \lambda_t(y)=\frac{4\sum_{c\in\mathcal P_y}J_c^{(t)}(y)/c}
                    {2^m\sum_{c\in\mathcal H}J_c^{(t)}(y)/c}.
\]
For fixed \(\delta,t\) in these ranges, let \(\mathcal R_{\delta;\lambda_t}\) be the very same arithmetic score as in the thin-gap note, with raw and free cutoffs \(R_-^{(\delta)},R_+^{(\delta)}\) but payer coefficient \(-2^m\lambda_t(y)\). The \(\mu_2(c)1_{c<C_y}\) and pairs \(4\,1_{c\in\mathcal P_y}\) are not changed. Let
\[
 B(\delta,t)=\sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
                         \log P\ \mathcal R_{\delta;\lambda_t}(y).
\]
All reflected primes in this definition are genuine.

**Theorem.** Uniformly for the actual even target, \(\Delta\le\delta\le2\Delta\), and \(0\le t\le2\Delta\),
\[
\begin{split}
 B(\delta,t)-B(\delta,\delta)
 &=-2^m V_N(z)V_z\int_J
    (\lambda_t(y)-\lambda_\delta(y))
               \sum_{c\in\mathcal H}\frac{J_c^{(\delta)}(y)}c\,dy
       +o_{\epsilon,m,J_0}(x\mathfrak S(N)),                          \tag{1}\\
 B(\delta,\delta)&=\mathcal G_J(N)+o_{\epsilon,m,J_0}(x\mathfrak S(N)).
\end{split}
\]
The main integral in (1), including its prefactor, has sign \(\operatorname{sgn}(\delta-t)\) and absolute value
\[
        \asymp_{m,J_0,\mathrm{bands}}\epsilon |t-\delta|\,\ell^4
                                                   x\mathfrak S(N)  \tag{2}
\]
if \(t\ne\delta\). In particular both \(\Delta,2\Delta\) are inside **proved** BV coverage, but
\[
 B(\Delta,2\Delta)-B(2\Delta,2\Delta)
       =-\Theta_{m,J_0,\mathrm{bands}}\bigl(
                       \epsilon\Delta\ell^4 x\mathfrak S(N)\bigr),
\]
where \(\Theta\) denotes lower and upper bounds by strictly positive constants for sufficiently large \(x\). Thus moving between these genuinely short gaps with the payer held fixed is not an \(o(x\mathfrak S(N))\) error. Transporting the payer cancels exactly this deterministic large effect, leaving \(B(\Delta,\Delta)-B(2\Delta,2\Delta)=o(x\mathfrak S(N))\). No asymptotic is asserted for \(B(0,t)\), at the unproved own-root cutoff.

## 1. The exact payer slope

Put \(h=H/(V_zL^2)-\xi^2/2\). We first check \(h=o(1)\). For fixed \(0<\tau<\xi\), integer rough counting on the range \(s>x^\tau\) via elementary Bonferroni as in the thin-gap note gives the harmonic tail \(\tfrac12 V_z(\xi^2-\tau^2)L^2+O_{\tau,A}(L^{-A})\). The actual remaining prefix has upper bound
\[
 \sum_{s\le x^\tau}\frac{R_z(s)\log s}s
       \ll \tau L(1+\tau\ell^2).
\]
Indeed its unsigned Euler harmonic sum is at most a constant times \(\log(x^\tau)/\log z=\tau\ell^2\) when \(x^\tau>z\) and at most 1 otherwise. These constants are absolute; the moving harmonic bound uses no target information. Since \(V_z\asymp\ell^2/L\), first \(x\to\infty\) and then \(\tau\downarrow0\) prove \(h=o(1)\).

For fixed \(y\) put \(a_c(t)=\log y/(2L)-t-\log c/L\), so that \(J_c^{(t)}(y)/L^2=h+a_c(t)^2/2\). On every pair and payer c, and all prescribed t, \(a_c(t)\in[.44,.51]\) eventually. Let
\[
                     \rho(a)=\frac{a}{h+a^2/2}.
\]
The derivative \(\rho'(a)=(h-a^2/2)/(h+a^2/2)^2\) is strictly negative and bounded away from zero and infinity in magnitude uniformly here, for large \(x\). Payer \(c\)'s have \(\log c/L>.74m\epsilon\ge2.22\epsilon\). Pair \(c\)'s have \(\log c/L<2\epsilon+2\log(1.5)/L\). Thus every payer \(a_c\) lies at least \(.2\epsilon\) below every pair \(a_c\) for large enough \(x\), whereas the largest such separation is \(O_m(\epsilon)\).

Each average below uses positive weights \(J_c^{(t)}(y)/c\) on its indicated genuine family. Differentiating the two sums in the ratio with respect to t, not with respect to y, gives the exact relation
\[
 \partial_t\lambda_t(y)
  =\lambda_t(y)\left(
             \langle\rho(a_c(t))\rangle_{\mathcal H}
                   -\langle\rho(a_c(t))\rangle_{\mathcal P_y}
                \right)
  \asymp_{m,\mathrm{bands}}\epsilon .                              \tag{3}
\]
To verify the lower and upper bounds on \(\lambda_t(y)\) uniformly here, note that each \(J_c^{(t)}\asymp L^2\); the payer harmonic sum has a positive constant limit from the actual disjoint prime bands scaled by \(\epsilon\); the pair harmonic sum is bounded above by the reciprocal pair triangle and below by taking one prime from each of two disjoint fixed exponent intervals contained in \((.55\epsilon,.75\epsilon)\), ensuring both \(p,q<C_y\) and \(pq>C_y\). Their limiting reciprocal masses do not depend on \(\epsilon\). Thus (3) is uniform in y, including its pair-support jumps; those jumps do not depend on t. Its integration from \(\delta\) to \(t\) proves the claimed sign and magnitude of the difference of the two actual coefficient functions.

## 2. Literal same-target evaluation of the difference

For \(\Delta\le\delta\le2\Delta\) the proof of the thin-gap identity is uniform: use the same sieve level \(x^{\Delta/2}\) and its same \(u=50\log\ell\) for the free rough variable. Its error savings do not deteriorate as \(\delta\) increases, while the largest modulus only decreases. The same holds for the raw summand. The two matching main values and the literal calibration at \(\delta\) prove the second part of (1).

The difference of scores at fixed \(\delta\) is **exactly** the payer term with \(-2^m(\lambda_t(y)-\lambda_\delta(y))\), i.e. only actual \(y=sca\), \(c\in\mathcal H\), \(a>R_+^{(\delta)}(y)\), with coefficient \(\log s\,R_z(y)\). Evaluate it by the same free-variable prime progression argument, with actual modulus \(scd\) upon opening the roughness of a by sieve divisor d. The local factor is the precise \(V_N(z)\), because \(sc\) is rough and the remaining sieve primes exclude those dividing \(N\). Dropping \(p\mid N,\ p>z\) from the model of the rough fixed factors costs \(O_A(xL^{-A})\) by their absolute harmonic bounds. The payer coefficients have bounded size and \(O_{m,\epsilon}((1+\log\ell)^2)\) total y-variation uniformly in \(t,\delta\) as in the thin-gap proof; thus the same maximal prefixes also evaluate their difference without assuming smoothness at the jumps. The absolute payer envelope in the principal is at most \(O_{m,\epsilon}(x\mathfrak S(N)\ell^4)\), from \(V_N(z)V_z\), \(\sum_{\mathcal H}1/c=O_m(1)\), and \(J_c^{(\delta)}\ll L^2\). Therefore the dimension-one fundamental lemma controls its absolute error to \(o(x\mathfrak S(N))\), including the signed coefficient by the positive upper-minus-lower bound. This gives (1).

Finally \(V_N(z)V_z\asymp\mathfrak S(N)\ell^4/L^2\), \(|J|\asymp_{J_0}x\), and \(\sum_{\mathcal H}J_c^{(\delta)}(y)/c\asymp_m L^2\) uniformly. Combine with (3) to get (2). Since \(\epsilon\Delta\ell^4\to\infty\), the error in (1) cannot hide the sign at \(t=2\Delta,\delta=\Delta\). In the literal opposite direction, one may use \(t=0,\delta=\Delta\) to obtain a positive shift of the same order at the **admitted** actual gap, but this says nothing about signed arithmetic at the real own-root cutoff. After calibrating, no proof here controls the unrestricted endpoint remainder between \(\delta=\Delta\) and \(\delta=0\).
