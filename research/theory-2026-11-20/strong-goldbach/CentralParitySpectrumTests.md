# Both signs of central spectrum detect a macroscopic window discrepancy

Let \(T_N,K_N,\sigma,S,\eta\) be as in [the fixed-target localization proof](CentralPointwiseLocalization.md). Thus \(\sigma\) is reflection-invariant on \([a,b]=[1/3,2/3]\), its local variation is at most \(C_0 S(|I|+\eta)\) on every closed interval, and \(\rho_N\) has an absolute positive lower bound. Let
\(D=\sup_{a\le s\le t\le b}|\sigma([s,t])|\).
For absolute \(c,C>0\),
\[
c(D-CS\eta)_+^2/S\ \le\ \lambda_+(T_N),\lambda_+(-T_N)\ \le\ C D .
\]
This strengthens the elementary same-sign rectangle argument only for the unrestricted spectrum, by using two signed Sobolev tests.

For \(f\in L^2\) real put \(F(t)=\int_t^b\rho_N(u)f(u)du\). The rank-one integral representation gives
\(\langle f,T_Nf\rangle=\int F(t)F(1-t)d\sigma(t)\).
Conversely every real \(F\in H^1([a,b])\) with \(F(b)=0\) comes from \(f=-F'/\rho_N\). Put \(D_R=\sup_{1/2\le s\le t\le b}|\sigma([s,t])|\). Reflection identifies the other half's supremum, and an interval crossing \(1/2\) can be split into two closed intervals, subtracting the midpoint atom (at most \(C_0S\eta\)). Hence \(D\le2D_R+C_0 S\eta\).

Choose a right-half closed interval \([s,t]\) of mass magnitude \(d\ge16 C_0 S\eta\), and put \(r=d/(16 C_0 S)\). The variation bound forces \(t-s\ge15r\). Let \(g\) on the central interval be zero outside \([s,t]\), rise linearly from zero to one on \([s,s+r]\), equal one on \([s+r,t-r]\), then fall linearly to zero. The cutoff loses at most \(2C_0S(r+\eta)\le d/4\) in absolute signed mass, including edge atoms. Thus \(|\int g^2d\sigma|\ge3d/4\). Define \(F_\pm(t)=g(t)\pm g(1-t)\). Because \(g\) vanishes at \(1/2,b\) and is supported in the right half, both are in \(H^1\) with \(F_\pm(b)=0\), and \(\int|F_\pm'|^2=2\int|g'|^2=4/r\). They have opposite reflection parities, so
\[
\int F_\pm(t)F_\pm(1-t)d\sigma(t)=\pm 2\int g^2d\sigma.
\]
The two associated \(f\)'s therefore give opposite-sign Rayleigh quotients of absolute size at least \(c d r=c'd^2/S\). Taking intervals approaching \(D_R\), and applying the pointwise localization upper bound for \(\|T_N\|\), proves the assertion after enlarging \(C\). If the threshold \(D\ge CS\eta\) is not met the asserted lower bound is zero. The antipodal parity test is not restricted to the original nonnegative symmetric Goldbach-weight test vectors.

In particular \(\lambda_+(T_N)/S\to0\) along a sequence of targets if and only if every signed central window discrepancy divided by \(S\) tends uniformly to zero. Because \(g(t)=\sqrt{t(1-t)}\) and its reciprocal are bounded and have bounded variation centrally, Stieltjes partial summation also equates weighted and unweighted window discrepancies up to absolute constants. A fixed threshold such as \(0.0350\) is not claimed to be equivalent to the full asymptotic; neither an actual prime-pair deficit nor a surplus at any large target is proved here.
