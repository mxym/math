# Polynomial-denominator arcs for the actual fixed-target signed Liouville field

This removes a genuine frequency sector of the [remaining signed singleton field](G23SingletonReopenedVaughanTranche.md), not a sector of the prime–prime convolution. It is a direct estimate on the unsquared sum, preserving its actual coefficients and not invoking the stronger [absolute moving-slope covariance](G23SingletonMovingSlopeCovariance.md). It gives no lower bound for a Goldbach pair.

Fix a large target \(P\), \(L=\log P\), \(0<\delta<.1\), \(y=\exp(L^\delta)\), and write \(\lambda_y(m)=\lambda(m)1_{P^-(m)>y}\). Fix any integer interval \(I\subset[1,P]\), and coefficients \(c_n\) supported on \([1,P]\) with \(\sum |c_n|^2\ll P L^C\) for a fixed \(C\). Put
\[
 C(\alpha)=\sum_n c_ne(n\alpha),\quad Z(\alpha)=\sum_{m\in I}\lambda_y(m)e(m\alpha),
 \quad Q=\sqrt P\,e^{-L^{3/5}},\quad H=L^B,
\]
where \(B>0\) is fixed. Let \(\mathcal U\) be the union on the frequency circle of
\[
 |\alpha-a/q|\le H/(qP),\qquad q\le Q,\quad 0\le a<q .
\]
Then for every \(A>0\),
\[
 \int_{\mathcal U}|C(\alpha)Z(\alpha)|\,d\alpha\ll_{A,B,C,\delta}P L^{-A}.
\]
It follows in particular that the contribution of this union to the actual \(P\)-th coefficient, whose integrand has the extra factor \(e(-P\alpha)\), is negligible. The estimate is uniform in the actual interval and in the coefficients with the stated bound.

## Reduced and nonreduced classes

Use ordinary uncentered Liouville Bombieri–Vinogradov in reduced classes at level \(\sqrt X/(\log X)^D\), with \(D\) allowed to depend on the requested log saving. For the input and the removal of the coprime mean see [the genuine near-square-root Liouville argument](SmallRadicalShiftedHighChambers.md), using [Granville–Shao](https://arxiv.org/abs/1706.05710). If working from the fixed-endpoint version, a grid of step \(X/(\log X)^J\) reduces maximal prefix bounds to finitely many grid endpoints. Apply the fixed-endpoint bound with additional log savings there. The intervening prefix error at modulus \(q\) is \(O(X/(q(\log X)^J)+1)\); summed over the moduli it is \(O(X(\log X)^{1-J}+Q_X)\). Prefixes before the first endpoint satisfy the same trivial bound. This is harmless with the exponential margin \(Q_X=\sqrt X\exp(-(\log X)^{3/5})\) used here, also after subpower divisor changes below.

For \(X\) between \(P^{1/2}\) and \(P\), this yields
\[
 \sum_{q\le Q_X}\max_{(a,q)=1}\max_{x\le X}
  \left|\sum_{\substack{m\le x\\m\equiv a\bmod q}}\lambda_y(m)\right|
 \ll_A X L^{-A}.
\]
Indeed apply Bonferroni to roughness through \(D_0\log L\) distinct primes at most \(y\), with \(D_0\) fixed large after the requested saving. Each retained squarefree divisor \(d\) is at most \(\exp(O(L^\delta\log L))\), and \((d,q)=1\) in every retained nonempty reduced class. By complete multiplicativity the residual progression applies to \(\lambda\) at scale \(X/d\), whose usable square-root level still exceeds \(Q_X\). The sum of retained reciprocals costs at most a fixed power of \(L\). The first omitted shell majorizes the pointwise truncation error, and its reciprocal mass is arbitrary-log small by the factorial bound \((C_1\log L)^k/k!\). For each \(q,d\) on that shell the integer floor cost is \(O(X/(qd)+1)\); summing floors costs at most \(Q_X\exp(O(L^\delta\log L))\), which is power-small relative to \(X\). This justifies the uniform assertion including its moving endpoints.

Let \(E_q\) be the maximum prefix discrepancy over **all** classes \(a\bmod q\) at the original scale \(P\). If \(g=(a,q)\) and \(h=q/g\), write \(m=gm'\); the residue becomes reduced modulo \(h\) (including \(h=1\)). The function \(\lambda_y\) is completely multiplicative, so this is either zero or a sign times the corresponding reduced sum at scale \(P/g\), with the same cutoff \(y\). Sum over \(g\) to dominate the maximum. Since \(g\le Q\) and
\[
 Q/g\le (P/g)^{1/2}\exp(-(\log(P/g))^{3/5}),
\]
the reduced estimate gives \(\sum_{q\le Q}E_q\ll_A\sum_{g\le Q}(P/g)L^{-A-2}\ll_A PL^{-A-1}\). The harmonic loss is absorbed by choosing the initial saving.

## Phase summation on the literal arcs

Fix \(q\) and \(|\theta|\le H/(qP)\). Group the sequences \(c_ne(n\theta)\) and \(1_I(m)\lambda_y(m)e(m\theta)\) into their \(q\) residue sums \(C_r,Z_r\). The former satisfy \(\sum_r|C_r|^2\le(P/q+1)\sum|c_n|^2\). In each class the latter are at most \(O((1+H/q)E_q)\) by partial summation at the actual interval endpoints. Exact finite Parseval and Cauchy give
\[
 \sum_{a\bmod q}|C(a/q+\theta)Z(a/q+\theta)|
 \le q\Big(\sum_r|C_r|^2\sum_r|Z_r|^2\Big)^{1/2}
 \ll Pq\,L^{C/2}(1+H/q)E_q .
\]
Integrate over an interval of length \(2H/(qP)\); the \(qP\) cancels. Sum over \(q\) (possible overlaps merely overcount a nonnegative integral), and apply the bound just proved for \(\sum E_q\). This proves the assertion.

**Application and limitation.** In the signed singleton and its exact high-gate reduction, all source restrictions are imposed before grouping by the actual \(n=pdt\). The grouped coefficients retain the genuine prime, Möbius, divisor and normalized logarithm weights, with pointwise majorant \(L^{O(1)}\tau(n)^{O(1)}\), and hence the requisite ordinary squared norm. These restrictions need not be harmonically separated for this estimate: they only depend on the source tuple. The actual reflected product is supported on \(m=P-n\) in its central interval. The complementary frequency integral still needs signed cancellation. The result does not apply with the true reflected prime in place of \(\lambda_y\), where there is a main term, and says nothing about a major/minor split in the different determinant-projector argument.
