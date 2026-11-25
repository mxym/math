# Removing the full top delta sector up to its exact target atom

This calculation uses **Dirichlet GRH** in the [verified Dirichlet scope](https://math.mit.edu/~drew/grh/). Unlike [the previous modulus-family deletions](DirectGoldbachGRHCompleteAliasTranches.md), it includes **every** top modulus, with no assumption on its factorization. The resulting expression retains the actual unknown Goldbach discrepancy. The coefficient is close to one, so this is not itself a sign estimate.

Let \(X=N\) be even, \(0<\delta<1/4\) fixed, \(Q=X^{1-\delta}\), \(L=\log X\), and \(T=Q/L^C\) for fixed \(C>0\). Let \(w,g\) be the fixed genuine interior prime test weights, \(R(M)=\sum_{p+p'=M}\log p\log p'\,w(p/X)g(p'/X)\), and \(I(z)=\int w(u)g(1+z-u)\,du\). Use the constant kernels, pole and centered blocks \(M_q,D_q\) in the [exact delta identity](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/ExactDeltaLinearRemoval.md) and its [polynomial-scale top representation](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/LargeConductorDeltaSectors.md). This note uses the **entire unprojected** \(D_q\) in \(T\le q\le Q\). Put
\[
 \kappa_T=\frac{c_Q}{Q}\sum_{T\le q\le Q}\frac{\varphi(q)}q C_{q/Q}.
\]
Then for some fixed \(c>0\),
\[
 \sum_{T\le q\le Q} D_q
   =\kappa_T\big(R(N)-X\mathfrak S(N)I(0)\big)+O(X^{1-c}).
 \tag{1}
\]
The main effect is an explicit reduction to smaller moduli, not an estimate for the true \(R(N)\).

## Exact divisor switch and centered part

For a genuine long-prime weight \(v=w,g\) let
\[
 E_{v,d}(a)=\Theta_v(a;d)-X\!\int v/\varphi(d)
 \quad (a\bmod d\text{ a unit}),\qquad
 H_d=\sum_{\substack{a+b=N\bmod d\\a,b\ {\rm units}}}E_{w,d}(a)E_{g,d}(b).
\]
All actual primes on the supports exceed \(Q\). Pushing the true centered vector modulo \(q\) down to any \(d\mid q\) gives exactly this vector, since every unit class has \(\varphi(q)/\varphi(d)\) unit lifts. Expand the actual Ramanujan sum by its divisor identity. Since the physical kernel is constant at these top moduli, this gives
\[
 \sum_{T\le q\le Q}D_q
 =\frac{c_Q}{Q}\sum_{\substack{m,d\\T\le md\le Q}}
       \frac{\mu(m)}m C_{md/Q}H_d.
 \tag{2}
\]
No product-conductor mask has been commuted with this identity.

The GRH smooth prime prefix estimate and Dirichlet character Parseval give \(\sum_a|E_{v,d}(a)|^2\ll XL^{O(1)}\), uniformly for all \(d\le Q\): character Parseval divides by \(\varphi(d)\), and the true pole-centered individual character error is \(O(\sqrt X L^{O(1)})\). Reflected pairing is a partial permutation of units, hence \(|H_d|\ll XL^{O(1)}\). Thus in (2) the tail \(m>M=X^\epsilon\), for any sufficiently small fixed \(\epsilon>0\), costs \(O(X L^{O(1)}/M)\), by \(\sum_{m>M}1/m^2\).

Let \(U_d(N)=\#\{a\bmod d:\ (a,d)=(N-a,d)=1\}\) and
\[
 B_d(N)=d\,U_d(N)/\varphi(d)^2
       =\prod_{\ell\mid d}\left(1+\frac{c_\ell(N)}{(\ell-1)^2}\right).
\]
Expanding \(H_d\), the true prime–prime term is exactly \(\sum_{k\in\mathbb Z}R(N+kd)\) (all prime inputs are automatically units). The mixed term is evaluated via
\[
 \sum_{p}(\log p)v(p/X)1_{(N-p,d)=1}
 =X\int v\,\frac{U_d(N)}{\varphi(d)}+O(X^{1/2+o(1)}).
\]
Indeed open the indicator over \(e\mid d\) with coefficients \(\mu(e)\). Only reduced residues \(p=N\bmod e\) have actual prime counts here, the GRH AP error is \(O(\sqrt X L^{O(1)})\) per divisor, and the local product of principal coefficients is \(U_d/\varphi(d)\). Hence the two mixed terms plus the pure lattice mean give
\[
 H_d=\sum_{k\in\mathbb Z}R(N+kd)
      -\frac{X^2}{d}\int w\int g\,B_d(N)
      +O\big(X^{3/2+o(1)}/d\big).
 \tag{3}
\]
This evaluation is for the whole congruence, not for separately chosen aliases.

## Evaluate the non-target terms without a sieve on the free modulus

Write \(V_m(t)=C_{mt/Q}1_{\{T\le mt\le Q\}}\), viewed on positive reals. Its supremum and total variation are \(L^{O(1)}\), by the defining smooth sum for \(C_x\). For every \(k\ne0\) in the actual range \(|k|\ll Xm/T\), use \(d=(p+p'-N)/k\) in the real weight \(V_m\), with the literal condition \(p+p'\equiv N\bmod |k|\). An actual GRH AP estimate in \(p'\) at this small modulus, and then in \(p\), gives
\[
 \sum_{d\ge1}V_m(d) R(N+kd)
  = X B_{|k|}(N)\int_0^\infty V_m(t) I(kt/X)\,dt
       +O(X^{3/2+o(1)}).
 \tag{4}
\]
For the first substitution fix the genuine \(p\); the weight in \(p'\) has uniformly \(L^{O(1)}\) variation, including the sharp \(d\) endpoints, and the residue is \(N-p\bmod |k|\). If nonreduced it has no actual prime. The continuous model is divided by \(\varphi(|k|)\). The second substitution in \(p\) consists only of the \(U_{|k|}\) admissible unit classes, so the number of possible errors is canceled by that \(1/\varphi(|k|)\). The integrated weight in the second step has supremum and variation \(O(XL^{O(1)})\), by translation of the smooth prime window and bounded variation of \(V_m\). Changing the continuous variable \(p'\) to \(d\) supplies the factor \(|k|\); this gives exactly \(B_{|k|}\), with no periodic independent-prime hypothesis. Summing the errors in (4) with the weights in (2), for \(m\le M\), costs \(O(MX^{5/2+o(1)}/(QT))\), a power saving for \(T=Q/L^C\) if \(\epsilon+2\delta<1/2\).

## Match the full off-target main and the lattice subtraction

For squarefree \(e\) put \(b(e)=\prod_{\ell\mid e}c_\ell(N)/(\ell-1)^2\), zero otherwise, so \(B_k=\sum_{e\mid k}b(e)\) for \(k\ne0\), \(B_0=\sum_e b(e)=\mathfrak S(N)\). Put \(\mathcal J=\sum_e b(e)/e\). The elementary Euler bounds give
\[
 \sum_e|b(e)|\ll(\log\log(3X))^{O(1)},\qquad
 \sum_e |b(e)|\sqrt e\ll \exp(O(\sqrt L))=X^{o(1)} .
\]
For the latter, primes not dividing \(N\) have summable contribution \(O(p^{-3/2})\); for primes dividing \(N\) split their \(O(p^{-1/2})\) contribution at \(L\) and use their number above \(L\) at most \(L/\log L\).

For \(t\) in the range of \(V_m\), Poisson/Riemann summation gives
\[
 \sum_{k\ne0} B_{|k|}(N) I(kt/X)
 = \frac Xt\,\mathcal J\int I-\mathfrak S(N)I(0)
       +O((X/t)^{-1/4}X^{o(1)}).
 \tag{5}
\]
Indeed include \(k=0\) first, expand over \(e\), and compare each progression in \(k\) to its integral. For \(e\le\sqrt{X/t}\), smooth Poisson gives arbitrary power accuracy in \(X/t\). Above that threshold the uniform Riemann sum error is \(O(1)\), bounded by the total variation of \(I\) regardless of the step. The displayed moment pays their tail. Then remove the exact zero-index model term. Inserting (5) into (4) and summing gives the off-target main
\[
 X^2\mathcal J\int w\int g\int V_m(t)\,\frac{dt}{t}
   -X\mathfrak S(N)I(0)\int V_m(t)\,dt
\]
for each \(m\), since \(\int I=\int w\int g\). In (3) the lattice subtraction has precisely the first of these terms up to a small error: summing the divisor expansion for \(B_d\) and applying the uniform integer Riemann bound gives
\[
 \sum_{d\ge1}V_m(d)B_d(N)/d
  =\mathcal J\int V_m(t)\,\frac{dt}{t}
       +O((m/T)L^{O(1)}).
\]
The same sharp-endpoint bound replaces \(\int V_m\) by \(\sum_dV_m(d)\) with \(L^{O(1)}\) error. Since \(X/t\ge X/Q\), (5) leaves a power error even after normalization. Errors in (3) and the last lattice sum cost at most \(O(X^{3/2+o(1)}/Q+X^{2+o(1)}M/(QT))\); these save a power for the stated parameters. The \(k=0\) term in (3) remains the actual \(R(N)\). Restoring the tail \(m>M\) in its coefficient costs \(O(X^{1-\epsilon+o(1)})\) by the elementary two-prime upper sieve for \(R(N)\). Recombining \(\sum_{m\mid q}\mu(m)/m=\varphi(q)/q\) now proves (1).

## What the reduction leaves to prove

The full target-atom coefficient in the exact cover is 1, and \(C_{q/Q}\) is bounded above and bounded away from zero as \(q/Q\to0\). In particular \(1-\kappa_T\asymp T/Q=L^{-C}\). Reinsert the established pole main and the two mixed families of the exact cover. For any fixed \(C>0\), their errors and the power error in (1) are negligible even after dividing by \(1-\kappa_T\). Hence the actual requirement becomes
\[
 (1-\kappa_T)\big(R(N)-X\mathfrak S(N)I(0)\big)
   =\sum_{q<T}D_q+o(X L^{-C}).
\]
An absolute middle-sector estimate with additional positive powers of \(\log X\) does **not** decide this equation; its loss remains after the division. A genuinely signed estimate on the remaining sector at scale \(X(1-\kappa_T)\) is needed for positivity. The computed top sector does not by itself supply it.
