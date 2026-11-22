# A stronger uniform exponential moment on the same central rough cusp

Stay on the **same** \(W=x^{1/\ell}\)-rough central source
and the identical \(F(y)\) in [the global-largest cusp proof](Proof.md).
For every fixed \(1<b<3/(2\sqrt2)\) there is the stronger bound
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm true\ prime}\\
                  y\ {\rm squarefree},\ P^-(y)>W}}
       \log P\,L\, b^{\omega(y)} |F(y)|
        \ll_{b,J_0} x\mathfrak S(N).                      \tag{A}
\]
It yields \(O_{b,J_0}(x\mathfrak S(N)b^{-K})\) for the rank \(>K\)
tail. In particular \(b=53/50\) is permissible because
\(2(53/50)^2<9/4\), and gives the exponential rate
\(\log(53/50)>0.058\). No new sign claim is made about the genuine
low-rank even sum.

To see this, insert \(b^{\omega(S)}\) **once in the original
harmonic weight** \(a_\beta(S)/S\) of (11), using
\(\omega(y)=2+\omega(S)\) in its exact global-largest, log-mark
expansion. Thus the only fixed prime cost is \(b^2\).
In Cauchy--Schwarz each square bracket uses that same single
measure \(a_\beta(S)b^{\omega(S)}/S\), with \(c(S)\) multiplying
the first one and dividing the second. Each prime coefficient
sum that led to (13) is therefore multiplied by \(b\) and
its Euler mass is \(O_b((1+\beta X)^{b\sqrt2})\).
The two square roots in Cauchy give this same exponent,
not twice it. Formula (12), the \(X^{1/2}\) band length and
\(|\widehat h(\xi)|\ll(1+|\xi|)^{-2}\) now give the summable
dyadic power \(X^{b\sqrt2-3/2}\).
The range \(X>L^{100}\) is negligible by the same
\(w^{-O_b(1)}\) positive bound and Fourier decay.
The largest-prime Rankin exponential (9) is unchanged,
so the \(\beta\)-sum is still absolutely bounded.
The prime-harmonic and numerical \(T_y\)-freeze errors
only change their fixed powers of \(1/w\).
The accumulated sieve floors use a fixed larger
\(\tau(H)\)-power and retain \(x^{1-.4\beta}\)
times a fixed log power. This proves (A) on actual
fixed-target true prime rows, uniformly also for a
moving \(K\); applying positive Markov with respect to
(A) has the full factor \(b^{-K}\), not \(b^{-K/2}\).

This sharpens the rank-tail rate of the direct central rough
proof. The earlier [unrestricted result](../ExponentialEvenTail.md)
states \(0.0154\) after limsup in the target for each fixed rank;
this addendum does **not** improve its wider all-reflected-row
scope or assert a small effective rank at which the error is
below a given numerical target. The own-root transfer and
reference \(2|J|\mathfrak S(N)\) are unchanged.
