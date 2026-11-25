# A reflection-even direct central Goldbach spectral test

This is a fixed-target deterministic reduction on *genuine prime pairs*. It replaces the unrestricted signed central operator by a positive-perturbation comparison. It does not supply the arithmetic estimate needed to prove a positive gap.

Keep the [central kernel and energy](CentralSpectrumQuantization.md) with \(a=1/3,\ b=2/3,\ \omega(t)=\sqrt{t(1-t)}\), \(S=S(N)\), and \(p_N=1/\rho_N^2\). Replace the atomic measure by its true prime-only part
\[
 \nu_N^{\rm pr}=\frac1N\sum_{\substack{n,N-n\ {\rm prime}\\ n/N\in[a,b],\ (n,N)=1}}
             \log n\log(N-n)\,\delta_{n/N}.
\]
It is positive and reflection invariant. This deletion is exact, not an assumption about primes. Alternatively, removing all terms with at least one proper prime power changes the energy operator by \(O(N^{-1/2}(\log N)^2)\): there are \(O(\sqrt N)\) such integers up to \(N\), each atom has weight at most \((\log N)^2/N\), and the central evaluation functionals are uniformly bounded. The only prime pair with \((n,N)>1\) is \(n=N/2\) with \(N/2\) prime; it is directly checkable.

## Restrict the primitive, not the original vector

On \(g(b)=0\) with inner product given by \(E(g)=\int p_N |g'|^2\), the exact discrepancy form is \(\int g(t)g(1-t)\omega(t)(S\,dt-d\nu_N^{\rm pr}(t))\). Restrict to reflection-even \(g\). Then \(g(a)=g(b)=0\), and pointwise \(g(t)g(1-t)=g(t)^2\). Thus the compressed discrepancy is \(A-P_0\), with the two bounded positive semidefinite operators given by
\[
 A[g,g]=S\int_a^b\omega(t)g(t)^2\,dt,\qquad
 P_0[g,g]=\int_a^b\omega(t)g(t)^2\,d\nu_N^{\rm pr}(t).
\]
The unrestricted direction of opposite reflection parity used in [the two-sign spectrum argument](CentralParitySpectrumTests.md) is absent here; no claimed bound for that direction is needed. The even condition is on the primitive \(g(t)=\int_t^b\rho_N(u)f(u)du\), not on \(f\).

On the half interval \([1/2,b]\) this is a weighted energy space with coefficient \(k_N(t)=p_N(t)+p_N(1-t)\). The top model eigenvalue \(\lambda_0\) and its unit-energy eigenfunction \(g_0\) are the first solution of
\[
 -(k_N g_0')'=(2S/\lambda_0)\omega g_0,\quad
 g_0'(1/2)=0,\quad g_0(b)=0 .
\]
The model eigenvalue is simple and \(g_0\) can be chosen strictly positive in the interior, by the one-dimensional mixed-boundary Sturm–Liouville problem. Its gap \(\Delta\) from the next model eigenvalue satisfies \(\Delta\asymp S\) uniformly for large \(N\). Indeed \(k_N\) tends uniformly to a fixed strictly positive coefficient, so min–max and comparison of the quadratic forms give convergence of the first two normalized eigenvalues to separated limits. Let \(U\ge\|P_0\|\); the [elementary central sieve bound](CentralSpectrumQuantization.md) and uniform energy-to-sup bound give \(U\ll S\).

## Quantitative gap with just one arithmetic moment

Write \(m=P_0[g_0,g_0]\). Then
\[
 \frac{m\Delta}{8(U+\Delta)}\le
 \lambda_0-\lambda_+(A-P_0)\le m .
\]
The upper bound follows by testing \(g_0\). For the lower, write a unit-energy \(g=u g_0+h\) with \(h\) energy-orthogonal to \(g_0\). The model loses at least \(\Delta E(h)\) and \(P_0\) can only increase the loss. If \(E(h)\ge m/[4(U+\Delta)]\), this suffices. Otherwise \(|u|\ge\sqrt3/2\), and the triangle inequality for \(P_0^{1/2}\) gives \(P_0[g,g]\ge((\sqrt3-1)^2/4)m\ge m/8\). These imply the stated lower bound (including the nonnegative spectral convention, since \(\Delta\le\lambda_0\)). The trivial case \(m=0\) is included. In particular, with the exact prime-only measure the spectral gap is positive if and only if \(m>0\). Every genuine unit pair in the open central interval contributes positively to \(m\).

This arithmetic moment is separable. Set \(w(t)=\sqrt t\,g_0(t)\) on \([a,b]\) and zero elsewhere. Then
\[
 N m=[e(N\alpha)]\left(\sum_{\substack{p\ {\rm prime}\\(p,N)=1}}
           \log p\,w(p/N)e(p\alpha)\right)^2 .
\]
The regular model makes \(w\) uniformly bounded and of bounded variation; on a compact central interval this adapted weight may be used in the usual small-major-arc prime approximation, with the positive main factor \(N S\int w(t)w(1-t)dt\). It does not estimate its fixed-\(N\) signed minor coefficient. Above the proper-power noise floor, a strictly smaller certified bound for the reflection-even discrepancy suffices without controlling the full norm, the odd primitive sector, or all local signed discrepancies at asymptotic accuracy. Producing such a bound uniformly for true prime pairs is the remaining arithmetic task, not a consequence of the perturbation inequality.
