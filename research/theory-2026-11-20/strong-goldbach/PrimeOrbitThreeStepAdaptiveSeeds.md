# An adaptive polylogarithmic seed set for every center

Use the actual unit-prime graph, the ordered pair count \(R(N)\), and the three-step avoidance statistic \(U_3(N,S)\) of [the fixed-pivot proof](PrimeOrbitThreeStepPairEstimator.md). The statement below uses its general estimate (2); no assertion about exceptional zeros is needed.

**Theorem.** For each fixed \(0<\varepsilon<1\) there is a fixed \(B>2\) such that, for *every* sufficiently large even \(N\), taking
\[
 S_N=\{s\text{ prime}: (\log N)^2<s\le(\log N)^B,\ s\nmid N\}
\]
gives the absolute estimate
\[
 \big|\,|U_3(N,S_N)|-R(N)\,\big|\ll_\varepsilon
 N/(\log N)^{3-\varepsilon}.
\]
Thus if such a target is unrepresented, every prime vertex except at most this many reaches \(S_N\) in at most three steps. Conversely, sufficiently many three-step avoiders at the same target would force a pair. This is still an estimate, not a lower bound on the number of avoiders. The menu may grow; a prescribed small prime can divide a center and so cannot serve as its unit pivot.

**Proof.** Put \(L=\log N,\ L_2=\log L\); choose \(\delta=1-\varepsilon/2\). We check the uniform harmonic hypothesis (1) of the fixed-pivot proof. For \(S=S_N\), the sum \(H=\sum_{s\in S}1/(s-1)\) tends to \(\log(B/2)\) by Mertens' theorem. Removing primes dividing \(N\) loses \(O(1/L)\), since such primes exceed \(L^2\) and there are \(O(L)\) prime divisors. Choose fixed \(B\) so large that \(e^{-H}<\varepsilon/16\) eventually. Fix an even integer \(k\) so large that \(\sum_{j>k}H^j/j!<\varepsilon/16\) throughout the eventual bounded range of \(H\). For each product \(d\) of \(1\le j\le k\) distinct seeds, \((N,d)=1\) and \(d\le L^{Bk}\). Distinct seed subsets give distinct moduli. Thus for any \(e^{L_2^2}\le X\le N-3\) the classical Bombieri–Vinogradov theorem for the prime-counting function yields
\[
 \sum_d\left|\pi(X;d,N)-{\rm Li}(X)/\phi(d)\right|\ll X/\log^3 X.
\]
Indeed \(L^{Bk}\le X^{1/2}/(\log X)^{C_0}\) throughout this interval for large \(N\), for every fixed \(C_0\); the standard maximal reduced-residue version covers the moving residue \(N\). See e.g. [Harper's proof of Bombieri–Vinogradov, theorem 7.1](https://warwick.ac.uk/fac/sci/maths/people/staff/harper/elementarymethodsnotes2.pdf).

The lower Bonferroni inequality through the even index \(k\) applies to the union of \(t\equiv N\bmod s\). Its main coefficient differs from \(1-\prod_{s\in S}(1-1/(s-1))\) by at most the indicated exponential-series tail. Before removing the nonunits, the number of primes in that union up to \(X\) is consequently at least \((1-\varepsilon/4){\rm Li}(X)\) for all large \(N\). Deleting 2 and all \(t\mid N\) costs \(O(L)\), negligible even at the lower endpoint \(X=e^{L_2^2}\). Below \(N-3\) every remaining \(t\) is a vertex with a genuine edge to \(S\); hence \(T(X)\ge\delta X/\log X\) on this range. By partial summation from \(e^{L_2^2}\) to \(Y\),
\[
 \sum_{t\in T,\ t\le Y}1/t\ge \delta\log\log Y-O_\varepsilon(\log L_2+1).
\]
The inequality also holds below \(e^{L_2^2}\) by nonnegativity after enlarging the constant. This proves (1). Apply (2), use \(|S|\le L^B\), and absorb \(L_2^{C'}\) by \(L^{\varepsilon/2}\). No term estimates a binary count at any center other than \(N\).
