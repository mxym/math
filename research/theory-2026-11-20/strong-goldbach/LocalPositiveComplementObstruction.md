# The genuine complement cannot be everywhere nonpositive

Use the original reflected \(C\), not \(C^\dagger\), and the true \(q\)-prime row of [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md). Define
\[
 T_{2x}=\sum_{\substack{s,q\ \mathrm{prime},\ x^{.10}<s<x^{.14}\\
        x/2<sq\le x,\ (sq,2x)=1}}
          W_s(q) C(2x-sq).
\]
Let \(D_{2x}\) be the same sum restricted to the physical chamber of that note, counted once per pair. It proves \(D_{2x}\le-c_*M_{2x}\) for all sufficiently large \(x\), with \(c_*>0\) fixed. Let \(E_{2x}=T_{2x}-D_{2x}\). Then for every fixed \(17/30<\theta<1\), every sufficiently large \(X\), and \(H=\lfloor X^\theta\rfloor\),
\[
 \#\{x\in\mathbb Z:X<x\le X+H,\quad E_{2x}\ge(c_*/2)M_{2x}\}
                         \gg_{\eta,\theta} H .
 \tag{1}
\]
Thus a strategy attempting even the weak claim “all of the remaining signed complement is nonpositive” would be false on the actual fixed-target arithmetic. This is **not** an obstruction to \(E_{2x}\le(.010+c_*)M_{2x}\), or to another signed bound adequate for the Goldbach criterion. No pointwise estimate of \(E_{2x}\) of that strength is supplied.

## 1. Whole true-row centering and uniform upper

The literal expansion (3) of [ForcedHighRankNegativeQuotient.md](ForcedHighRankNegativeQuotient.md), used now against actual true \(q\), gives
\[
 T_{2x}=Z_{2x}-\mathcal M_{2x}+O_A(xL^{-A}),\quad
 Z_{2x}=\sum_{s,q\ {\rm in\ the\ true\ row}}W_s(q)\Lambda(2x-sq),
 \quad \mathcal M_{2x}=(J+o(1))M_{2x},
\]
where \(J=\int_{.1}^{.14}(1-2t)^2\,dt/t\). Apply full-scale generalized BV and its exact finite \(\mu/\phi\) moments: see [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), §3, and [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), §§1–3. The three genuine short reflected ranges have modulus at most \(Q_0\) or \(UV\), or \(U\) in the first term, all with arbitrary log margin from \(\sqrt x\). The first short log-weight gives \(\mathfrak S(Nsq)\), and each other short main is zero to log precision by the constant moment (including its base-prime overlap). On this actual prime source, the factors from \(s,q\) change \(\mathfrak S(Nsq)/\mathfrak S(N)\) by \(1+O(x^{-.10})\) because they are distinct polynomial primes. Ordinary PNT and reciprocal-prime summation in \(s\) give the stated \(J\), uniformly in \(x\).

Moreover \(Z_{2x}\ll M_{2x}\) uniformly. For fixed \(s\nmid N\) use the dimension-two upper Selberg sieve on the literal linear forms \(q,N-sq\) on an interval of length \(\asymp x/s\), and count genuine primes in both forms. Their sole exceptional roots are at primes dividing \(sN\); the singular factor is \(O(\mathfrak S(N))\) since \(s\) is prime. This is precisely the uniform Selberg normalization in [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md), §3. The pair count is \(O(\mathfrak S(N)x/(sL^2))\), and the factor \(\log m\) costs \(O(L)\). Summing \(1/s\) is \(O(1)\). Proper prime powers in \(m\) cost \(O(x^{1/2}L^2)\): each \(m\) determines \(sq\), with at most one eligible short prime \(s\). This proves \(|T_{2x}|\ll M_{2x}\) by the centered identity, not by any bound for arbitrary \(C(m)\). Also \(|D_{2x}|\ll M_{2x}\): for fixed \(s,K=pcab\) the same two-form upper in the free \(w\) variable, with \(w\) polynomially rough and \(q\) prime, counts \(O(\mathfrak S(N)x/(sK L^2))\); \(C(m)\ll_\gamma L\) for every such \(m\) since its rank with multiplicity is bounded by \(4+O(1/\gamma)\), \(\gamma=.004\). The harmonic sum \(\sum1/(sK)\) is \(O(1)\).

## 2. Moving target window and actual centering

Freeze the central \(n=sq\) endpoints and the \(s\)-band at \(X\). The literal weight \(W_s(q)\) does not depend on the target. The central edges affect \(O(H)\) integers \(n\), each with at most one admissible short factor in the union of bands. The total error is \(O(H^2\log X)\), from all \(x\) in the interval and the trivial \(\Lambda\) bound. A band endpoint \(S=X^.10\) or \(X^.14\) moves by \(O(SH/X)\), so there are \(O(SH/X+1)\) possibly changed short prime values. For each such \(s\asymp S\) there are \(O(X/(s\log X))\) possible true \(q\) by the ordinary prime upper bound, and the maximum absolute cost over all targets per \(q\) is \(O(H\log X)\). Both edge costs are \(o(HX/\log X)\) since \(H=X^\theta\) and \(\theta<1\) is fixed.

In the frozen central sum \(n=sq\) is odd, and as \(X<x\le X+H\) the variable \(2x-n\) runs through the odd integers in a shift of an interval of length \(2H+O(1)\) at scale \(X\). The prime \(m=2x-n\) in that interval is much larger than either \(s\) or \(q\), so it is automatically coprime to \(n\) and \(N\) has no common factor with \(n\). Removing proper prime powers uniformly costs \(o(HX/\log X)\) by the preceding per-target bound, also on the frozen supports. The ordinary prime number theorem in short intervals [Guth–Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552) applies uniformly, since \(\theta>17/30\). If the interval is longer than the stated upper length \(x^{.99}\), divide it into comparable shorter windows inside the theorem’s range and sum. Restricting the von Mangoldt sum to odd integers removes only powers of 2, an \(O(\log^2 X)\) error. Thus each genuine frozen \(n\) sees \((2+o(1))H\) Mangoldt mass. The \(2\) is exactly the spacing of consecutive even targets, not a factor from any unproved pair correlation.

The total frozen \(W_s(q)\) mass is \((J+o(1))X/(2\log X)\) by ordinary prime reciprocal summation in \(s\) and PNT for \(q\). Therefore
\[
                \sum_{X<x\le X+H}Z_{2x}=(J+o(1))HX/\log X .
\]
In the same window \(\sum\mathfrak S(2x)=(2+o(1))H\) and \(\sum\mathfrak S(2x)^2\ll H\), uniformly in \(X\). Expand the singular series as \(2C_2\sum_{d\mid x,\ d\ {\rm odd}}\mu^2(d)\prod_{p\mid d}1/(p-2)\); its square has the same form with local increment \(2/(p-2)+1/(p-2)^2\). In either case the coefficient divided by \(d\) is summable, and the sum of coefficients up to \(2X\) costs at most a fixed power of \(\log X\) by the finite Euler product. The error from the floor in the count of \(d\)-multiples is then negligible relative to \(H\). The first complete Euler product is \(1/C_2\), giving mean 2. Consequently \(\sum M_{2x}\sim HX/\log X\), \(\sum M_{2x}^2\ll H(X/\log X)^2\), and \(\sum T_{2x}=o(\sum M_{2x})\).

Finally \(\sum E_{2x}\ge(c_*+o(1))\sum M_{2x}\), and \(|E_{2x}|\ll M_{2x}\) uniformly by §1. Thus the targets satisfying the threshold in (1) carry a fixed positive fraction of the \(M_{2x}\)-mass. Cauchy and the displayed second moment give their count \(\gg H\). This proves the local obstruction without bounding an exceptional fixed target or using a second-moment claim about binary Goldbach.

**Comparison (checked through November 21, 2026).** The repository's
[marked negative chamber](ActualNegativeThreeMarkReserve.md) and [pointwise
high-rank opening](ForcedHighRankNegativeQuotient.md) are individual-target
statements, whereas the present consequence concerns the other configurations
over each short target interval. [Chirre–Hagen's 2026 short-interval theorem](https://doi.org/10.1007/s40993-026-00767-6)
counts existence of Goldbach numbers under RH and does not give this
unconditional assertion about the signed complement. [Pham's October 2026 v1](https://www.preprints.org/manuscript/202610.3061)
uses a different two-row benchmark. This proof does not assume RH or any
two-prime asymptotic.
