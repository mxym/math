# The smooth-divisor channel of the signed Goldbach switch

With [the small-radical profile theorem](SmallRadicalSmoothProfileParity.md) as input, one specific channel of the old signed divisor kernel has a true signed saving. This is a component estimate on a specified decomposition, not a stronger bound for the whole small-prime-containing sector than GlobalRoughLocalization.md.

Fix a compact interior interval \(J\subset(0,1)\), \(I=PJ\), \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), and \(y=\exp(L^\delta)\), \(0<\delta<.1\). For \(m=P-p\) with \(p\in I\) prime, write \(a=a_y(m)\) for its complete \(y\)-smooth part, \(b=b_y(m)\) for its rough part. Let \(\epsilon>0\) be fixed and \(P^\epsilon\le\alpha\le P^{1-\epsilon}\). The proposed channel of the triangular kernel is
\[
K^{\rm sm}_\alpha(m)=\sum_{d\mid a}\mu(d)\min(0,\log(\alpha d/m)).
\]
It uses *all* smooth divisor assignments \(d\mid a\), not just primes or \(d\le y\). Uniformly in the stated range,
\[
\left|\sum_{\substack{p\in I\ {\rm prime}\\a_y(P-p)>1}}
           (\log p)\mu(P-p) K^{\rm sm}_\alpha(P-p)\right|
\ll_{B,J,\delta,\epsilon} S(P)P/\sqrt{\log L}.
\tag{1}
\]
This differs from [GlobalRoughLocalization.md](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/GlobalRoughLocalization.md), which bounds the *full* \(K_\alpha\) for small-containing rows after cancellations between divisor assignments (and may give a sharper power for that full kernel). The elementary near-full largest-prime subcase is already covered in [OneSidedLargestFactor.md](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/OneSidedLargestFactor.md); it is not asserted anew here.

Choose any \(\kappa\in(\delta,1)\). The part \(a>H=\exp(L^\kappa)\) is negligible even with the potentially unbounded divisor count: \(|K^{\rm sm}_\alpha(m)|\ll L\tau(a)\), and counting all multiples of \(a\) before prime weighting costs at most
\[
P L^2\sum_{\substack{a>H\\a\ {\rm smooth}}}\frac{\tau(a)}a
\ll P L^2(\log y)^2 e^{-L^{\kappa-\delta}}.
\]
The last bound is Rankin with \(s=1/\log y\): the Euler product \(\prod_{\ell\le y}(1-\ell^{-1+s})^{-2}\ll(\log y)^2\) by the same local comparison as in the profile proof.

For \(1<a\le H\), \(m\gg_J P\) and \(\alpha a<m\) for sufficiently large \(P\), uniformly in \(\alpha\). Thus every smooth divisor lies in the negative log branch. Since \(\sum_{d\mid a}\mu(d)=0\),
\[
 K^{\rm sm}_\alpha(m)=\sum_{d\mid a}\mu(d)\log d=-\Lambda(a).
\]
This exact cancellation removes the potentially large coefficient \(\log(\alpha/m)\) on all nontrivial profiles. Because \((a,b)=1\), the remaining signed integrand is \((\log p)F(a)\mu(b)\) for \(F(a)=-\mu(a)\Lambda(a)\mathbf1_{a>1}\). If \(b\) is squarefree then \(\mu(b)=\lambda(b)\). Otherwise a prime \(\ell>y\) satisfies \(\ell^2\mid m\); counting all integers before imposing primality gives \(O(P/y)\) such \(m\), so the total replacement cost with the two log weights is \(O(P L^2/y)\).

The profile theorem now applies with this genuine weight of at most logarithmic height. It is supported only at prime profiles \(a=\ell\le y\), and the exact model first absolute moment is
\[
\mathbb E_\nu|F|
  =V_y(P)\sum_{\substack{\ell\le y,\ \ell\ {\rm prime}\\\ell\nmid P}}
       (\log\ell)\frac{\ell-1}{\ell(\ell-2)}
  \ll V_y(P)\log y \ll S(P).
\]
In the last step, Chebyshev and partial summation bound \(\sum_{\ell\le y}(\log\ell)/\ell\); the uniform rough-layer identity is \(V_y(P)\sim e^{-\gamma}S(P)/\log y\). The weighted relative estimate proves (1).

The profile \(a=1\) is **not included**. There \(d=1\) is the only smooth divisor; the weight is \(\log(\alpha/m)=\log(\alpha/P)-\log(m/P)\), with the first term of order \(L\). Existing rough-profile parity controls the constant term only by \(O(P L V_y(P)/\sqrt{\log L})\) in the sum, and the bounded remainder trivially by \(O(PV_y(P))\); the first bound can greatly exceed \(PS(P)\). No small logarithmic change of cutoff or reweighting of a fixed \(\log L\) number of independent tags removes that gap. The terms with rough divisors of \(m\) other than 1 are also outside this channel.
