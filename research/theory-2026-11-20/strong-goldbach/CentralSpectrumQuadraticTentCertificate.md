# Quadratic mesh certificate for a positive central Goldbach spectral threshold

This is a deterministic refinement of the [central signed-cell quantization](CentralSpectrumQuantization.md). It certifies the existing spectral criterion from sufficiently accurate *given* weighted pair counts; it is not a proof of their arithmetic bounds, of \(P_3\), or of Goldbach. The argument is a nodal interpolation and Schur-complement bound, with no claim of general numerical-analysis priority.

Use the same \(a=1/3,b=2/3,\ell=b-a,\ S=S(N),\ \omega(t)=\sqrt{t(1-t)}\), reflected measure \(\sigma=\omega(S\,dt-\nu_N)\), and positive function \(\rho_N\) as in that note. Write \(R(t)=1-t\), \(p=1/\rho_N^2\), \(p_*=\min p>0\), and \(K=\operatorname{Lip}(1/p)/\min(1/p)\). On the real energy space \(g(b)=0,\ E(g)=\int_a^b p|g'|^2\) with \(g\in H^1\), the top positive spectral value is the nonnegative part of the supremum of
\[
 \frac{Q(g)}{E(g)},\qquad Q(g)=\int g(t)g(Rt)\,d\sigma(t).
\]
Indeed \(f\mapsto g(t)=\int_t^b\rho_N(u)f(u)\,du\) is an onto isometry from real \(L^2\) to this energy space, and the formula follows from the reflected kernel. The real test suffices for the real self-adjoint kernel.

## The finite certificate

Use a uniform grid \(t_j=a+jh,\ h=\ell/m,\ 0\le j\le m\), with ordinary piecewise-linear nodal functions \(\psi_j\) and signed nodal moments \(m_j=\int\psi_j\,d\sigma\). Reflection makes \(m_j=m_{m-j}\). For nodal data \(x_j\), set \(x_m=0\) and define
\[
 E_h(x)=\sum_{j=0}^{m-1}\frac{(x_{j+1}-x_j)^2}{\int_{t_j}^{t_{j+1}}\rho_N^2},
 \qquad Q_h(x)=\sum_{j=0}^{m}m_jx_jx_{m-j},
 \qquad \lambda_h=\max\bigl(0,\sup_{x\ne0}Q_h(x)/E_h(x)\bigr).
\]
The tridiagonal stiffness matrix is assembled by each edge \(j\) with weight \((\int_{t_j}^{t_{j+1}}\rho_N^2)^{-1}\) and endpoint \(x_m=0\). The numerator matrix has anti-diagonal entries \(m_j\) where both indices are retained (a reflected pair gives two equal entries, the central fixed index at most one). The resistance integral is elementary:
\[
 \int_u^v\rho_N^2=2\pi\sum_{\gamma\in\{1/\log N,\,1/8\}}
 \frac{N^{-2\gamma}}{2+2\gamma}\bigl(u^{-2-2\gamma}-v^{-2-2\gamma}\bigr),
\]
with both summands retained if the exponents coincide.

Let \(M=|\sigma|([a,b])\), \(\Gamma=\max_j |\sigma|([t_j,t_{j+1}])\), or use any upper envelopes. Put
\[
 e=\frac{h\Gamma}{p_*}(1+2K\ell),\qquad d=\frac{h\Gamma}{4p_*},
 \qquad b_0=\frac{\ell M}{p_*}.
\]
Then, for every \(T>d\),
\[
 \boxed{\ \lambda_h+e+\frac{b_0d}{T-d}\le T
        \quad\Longrightarrow\quad\lambda_+(T_N)\le T.\ }
\]
Always \(\lambda_+(T_N)\ge\max(0,\lambda_h-e)\). An unconditional upper bound is the largest eigenvalue of the \(2\)-by-\(2\) matrix with diagonal \(\lambda_h+e,d\) and off-diagonal \(\sqrt{b_0d}\). The boxed test also admits a direct directed matrix check: with \(\theta=T-e-b_0d/(T-d)\), require \(\theta\ge0\) and \(\theta E_h-Q_h\) positive semidefinite. A numerical implementation must use sufficiently accurate enclosed inputs; the proof does not assume that an unenclosed floating-point comparison certifies an inequality.

## Proof

For \(x_j=g(t_j)\) let \(g_h\) interpolate in the local resistance coordinate \(\int_{t_j}^t1/p\). It has exact energy \(E_h(x)\), and \(r=g-g_h\) vanishes at each node and is energy-orthogonal to \(g_h\), since \(p\,g_h'\) is constant on each open cell. On a cell put \(\xi=(t-t_j)/h\). The two reflected factors interpolate from \(x,y\) by increments \(\Delta x,\Delta y\) as \(x+\theta_1\Delta x,y+\theta_2\Delta y\) in increasing \(t\). Both \(\theta_i\) lie in \([0,1]\) and differ from \(\xi\) by at most \(Kh\): the resistance density differs from its cell average by at most \(\operatorname{Lip}(1/p)h\), and the denominator is bounded below by \(h\min(1/p)\). The same applies to the reflected density. Relative to the ordinary interpolant of the nodal products the difference is
\[
 x\Delta y(\theta_2-\xi)+y\Delta x(\theta_1-\xi)
                +\Delta x\Delta y(\theta_1\theta_2-\xi).
\]
Use \(\sup |g_h|\le\sqrt{\ell E_h/p_*}\), \(\sum|\Delta x|\le\sqrt{\ell E_h/p_*}\) and its reflected counterpart, and \(\sum|\Delta x\Delta y|\le hE_h/p_*\). The endpoint product interpolation is exact at each grid atom, so there is no ambiguity about assigning atoms. Integration gives \(|Q(g_h)-Q_h(x)|\le e E_h(x)\).

For \(r\) on one cell, let \(A=\int_{t_j}^t1/p,\ B=\int_t^{t_{j+1}}1/p\). Both endpoints of \(r\) are zero, so Cauchy–Schwarz separately to the left and right gives \(|r(t)|^2(1/A+1/B)\le E_{\rm cell}(r)\). Therefore \(|r(t)|^2\le E_{\rm cell}(r)(A+B)/4\le E_{\rm cell}(r)h/(4p_*)\); nodes satisfy this too. Integrating gives \(\int |r|^2\,d|\sigma|\le d E(r)\). Also \(\int |g_h|^2\,d|\sigma|\le b_0 E(g_h)\). By reflection and Cauchy–Schwarz the diagonal residual term is bounded above by \(d E(r)\) and the mixed quadratic term by \(2\sqrt{b_0d}\sqrt{E(g_h)E(r)}\). Completing the square in \(\sqrt{E(r)}\) proves the boxed bound; restriction to \(r=0\) proves the stated lower bound.

## Only the nodal moments are needed

The variation envelopes can be recovered from the same inputs. The atomic moments \(u_j=S\int\omega\psi_j\,dt-m_j\) are nonnegative, since \(\nu_N\) is positive. Lebesgue measure and the arithmetic atomic measure are mutually singular, hence
\[
 M=2S\int_a^b\omega\,dt-\sum_j m_j,\qquad
 |\sigma|([t_j,t_{j+1}])\le S\int_{t_j}^{t_{j+1}}\omega\,dt+u_j+u_{j+1}.
\]
The cell inequality uses \(\psi_j+\psi_{j+1}=1\) throughout the closed cell and both hats are nonnegative globally. Background tent integrals reduce to \(\int\omega\,dt,\int t\omega\,dt\), both elementary. Thus one need not measure separate absolute cell variations. This envelope is also \(O(S(h+\eta_N))\) with \(\eta_N=N^{-1/2}\log^3N\), since each \(u_j\) is bounded by the atomic mass on its interval of width at most \(2h\), to which the [existing local sieve bound](CentralSpectrumQuantization.md) applies. The same bound gives \(M\ll S\); all \(p_*,1/p_*,K\) are uniformly bounded in the central interval for large \(N\).

At any fixed positive normalized threshold \(T=cS\), the added slack for small enough \(h\) is \(O_c(S h(h+\eta_N))\). In particular its normalized upper bound is \(O_c(h^2)\) above the finite-\(N\) floor scale \(h\ge\eta_N\). A sufficient mesh dimension for normalized slack at most \(\epsilon\) is \(O_c(\epsilon^{-1/2}+\eta_N/\epsilon)\), rounding up (with fixed adequate constants). The statement is about certification at a positive threshold, not a quadratic operator-norm approximation near zero.
