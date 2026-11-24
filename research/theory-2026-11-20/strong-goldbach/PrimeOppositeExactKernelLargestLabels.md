# Largest-factor label supply in both shorter exact-profile P4 windows

Written corollary, 2026-11-24. Apply the exact prescribed small-factor version of the [full-kernel P4 result](PrimeOppositeExactKernelPlantedP4.md), with its normalized \(B_0=2XS_1/(\varphi(dm)L)\). The setup fixes \(a,b,A\), \(dm\le L^A\), and a genuine reduced root profile as in that theorem. For the two true prime-root intervals the following rows survive:
\[
\begin{array}{c|c|c}
\text{prime-root window} & \text{count at least} & \text{largest quotient prime}\\\hline
(aN^{.4832},\,bN^{.4832}] & .003 B_0 & q(p)>N^{.25002}\\
(x,\,x+N^{.4916}],\ x\in[a\sqrt N,b\sqrt N] & .012 B_0 & q(p)>N^{.25012}.
\end{array}
\]
Here \(Q=(N-p)/d\) remains squarefree, \(\Omega(Q)\le4\), and all its primes are at least \(N^{.0393}\). The original prescribed valuations are unchanged. Uniformly in the indicated windows and profiles, the rows yield \(\gg N^\alpha\) actual distinct largest labels for the respective exponent \(\alpha\). If at least half the retained rows have \(q(p)\le N^{.4}\), these distinct lower labels already have positive reciprocal mass and occupy \(\gg\log N\) dyadic scales. Otherwise there are \(\gg N^{.4}/(\log N)^2\) distinct higher labels. These are across the whole indicated set of prime roots; no single-root or terminal-component assertion follows.

**Proof.** The exact directed margins proved in the [asymmetric-kernel note](PrimeOppositeExactAsymmetricP4Kernel.md), and preserved by planting, are at least .0074 and .0362 in the two windows, before rounding both to the common .005. If the true maximum \(q(p)\le N^\alpha\), then \(\Omega(Q)\le4\) and \(Q\ge N/(2d)\) force \(q(p)\ge(N/(2d))^{1/4}\). Thus \(t=\log q/L\) is in the genuine long-mark band with \(t\in[.25-o(1),\alpha]\).

Recall \(\rho=.4832\) or \(.4916\) is the actual source-window-length exponent, and \(\theta=.4832\) or \(.5\) the actual prime-root size exponent. For the switched count on each such \(q\), at \(\mu=.0393\) the true normalized coefficient is \(\theta/(2\mu^2J_{\mathrm{exact}}(v))\), \(v=(\rho-t-.00002)/(.0786)\). In both cases \(2.96\le v\le3.1\) eventually. The [original one-subtraction bound](PrimeOppositeSubSquareRootShortP4.md) lower bounds the exact denominator even here:
\[
 J_{\mathrm{exact}}(v)\ \ge\ \tfrac54v^2-\tfrac12v^2\log v-v+\tfrac14
 \ \ge\ .68v^2-v+.25\ \ge\ 3.247888.
\]
The middle inequality uses \(\log3.1<1.14\), certified by the degree-five positive exponential Taylor lower at \(1.14\), and the last follows by evaluating the increasing quadratic at \(2.96\). Since \(\theta\le.5\), the resulting true cap is \(<50\) in units \(B_0/q\) by rational cross multiplication. Aggregate lattice floors are those of the exact-kernel proof, \(o(B_0)\), and the exact planted normalization has not changed.

The harmonic sum of marks from \((N/(2d))^{1/4}\) to \(N^\alpha\) is \(\log(\alpha/.25)+o(1)\), uniformly since \(d\le L^A\). Bounding \(\log(1+x)\le x\) gives removed cost at most \((.004+o(1))B_0\) for \(\alpha=.25002\) and \((.024+o(1))B_0\) for \(\alpha=.25012\). The displayed lower counts follow with strict slack.

For \(N^\alpha<q\le N^{.4}\), use the same low-label [two-form cap](PrimeOppositePlantedLargestLabelSupply.md) at fixed \(K=N^{.02}\) on its actual affine progression of length \(Y/(dmq)\). The normalizing coefficient is now \(\theta/.0004\le1250\), since \(X\sim Y/(\theta L)\). The individual error \(O(N^{.04}L^C)=o(B_0/q)\) is still uniform, since \(Y/q\gg N^{.0832}\). Hence the number of prime roots per label is at most \(1300 B_0/q\), and any fixed positive fraction of \(B_0\) retained here gives positive reciprocal mass and the stated count and scales. Above \(N^{.4}\), CRT gives at most \(Y/(dmq)+1\) prime roots per \(q\). Since \(Y/(dmN^{.4})\to\infty\), any fixed positive fraction of \(B_0\gg Y/(dmL^2)\) yields the stated \(\gg N^{.4}/L^2\) count. Both tails involve only actual labels on the prescribed profile.
