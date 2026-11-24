# Extension: no two near-square-root factors for a positive proportion of all true prime sources

Research note, 2026-11-24. This extends the thin-band upper sieve in [the companion fixed-angle proof](PrimeOppositeFixedAngleExclusion.md) by keeping the genuinely varying cofactor \(b\). The conclusion here includes many more prime sources but does **not** assert roughness. The companion theorem separately supplies a rough subfamily. No Goldbach representation is asserted.

Fix \(1/3<\rho\le1/2\), \(0<\alpha<\beta<1\), put \(H=N^\rho\), \(L=\log N\), and let \(N\) be even. There is a fixed \(\delta>0\) depending only on these parameters such that a positive proportion of the actual primes \(p\in(\alpha H,\beta H]\) have \((p,N)=1\) and \(N-p\) has at most one prime factor \(>N^{1/2-\delta}\), counting multiplicity. In fact for every sufficiently small fixed \(\delta>0\), the number of prime unit sources which fail this condition is \(\ll\delta^2 H/L+o(H/L)\) with the implied constant independent of the final \(\delta\).

## 1. The genuine cofactor and the modified band

If \(q\le r\) are two such prime factors, define \(b=(N-p)/(qr)\). Then \(1\le b<B=N^{2\delta}\), \(b\) is odd, and \((b,N)=1\) since \(p\) is a unit. For an upper bound sum over every such \(b\). For a fixed \(b\), the smaller factor satisfies
\[
 N^{1/2-\delta}<q\le \sqrt{N/b}.
\]
Cover by at most \(1+\delta L/\log 2\) dyadic shells \(J\subset[Q,2Q]\), truncated at \(\sqrt{N/b}\). Put \(A=\lfloor\alpha H\rfloor+1/2\), \(C=\lfloor\beta H\rfloor+1/2\) as before. The enlarged genuine integer band is
\[
 q\in J,\qquad (N-C)/(bq)<r<(N-A)/(bq),
\]
dropping the ordering and other cutoffs for \(r\) only after restricting \(q\). Its area is \((C-A)b^{-1}\int_J dq/q\ll H/b\). It still has \(r\asymp N/(bQ)\ge cN^{1/2-\delta}\), so all prime variables in the counted triples exceed the upper sieve cutoff.

In residues \(q=a+d j,\ r=a'+d k\), the boundary phases are
\[
 f_c(j)=\frac{N-c}{bd(a+dj)}-\frac{a'}d,\qquad c=A,C,
\]
with second derivative \(\asymp d N/(bQ^3)\). The half-integers still preclude equality at an integer pair, now because \(bqr\) is an integer. Each interval length and monotone-integral main term give area divided by \(d^2\) with error \(O(H/(bdQ))\). At frequency \(h\) the second derivative bound is
\[
 \ll \frac{\sqrt{N/b}\sqrt h}{\sqrt{Qd}}
          +\frac{\sqrt b\,Q^{3/2}}{\sqrt N\,\sqrt{hd}} .
\]
With \(M=\lfloor N^{1/6}\rfloor\), discrepancy sums the first term to at most \(N^{1/3+\delta/2}\) exactly as before (using \(b\ge1\)), and the second to at most \(N^{1/4}/\sqrt d\) because \(Q\le\sqrt{N/b}\). Thus the same per-residue error \(O(N^{1/3+\delta/2})\) is **uniform in the true cofactor**.

Choose the initial bounds \(\delta_0,\lambda>0\) so small that
\[
 1/3+(5/2)\delta_0+2\lambda<\rho
\]
and both are less than \(1/100\), and keep them fixed for \(0<\delta\le\delta_0\). Sieve with \(Z=N^{\lambda/2}\), where least common multiple moduli are \(\le N^\lambda\). The error per \(b\) and per shell from the exact Selberg argument in the companion proof is \(O(N^{1/3+\delta/2+2\lambda+o(1)})\). Multiplying by at most \(N^{2\delta}\) cofactors and \(O(L)\) shells is still \(o(H/L)\), uniformly after the initial restriction above. This choice leaves no hidden \(\delta\) dependence in the main term constant.

## 2. Local factors and the missing-prime cancellation in the cofactor sum

The actual polynomial to sieve is \(q r(N-bqr)\). Since \((b,N)=1\), for each odd prime \(\ell\mid bN\) its local root count is \(2\ell-1\): the two axes only. If \(\ell\nmid bN\), it is \(3\ell-2\). At 2 the local root count is 3 as before (as \(b\) is odd). Thus the uniform main bound per shell is
\[
 \ll \frac{H}{b L^3}\,F_N(y)F_b(y),\qquad
 F_m(y)=\prod_{\substack{3\le\ell\le y\\\ell\mid m}}
                      \frac{\ell-1}{\ell-2},
\]
where \(y=Z^\nu\) for the fixed small \(\nu\) of the Selberg weight argument. Neither \(\lambda\) nor \(\nu\) depends on the final \(\delta\).

The key genuinely paired cancellation is
\[
 F_N(y)\sum_{\substack{1\le b\le B\\(b,N)=1}}\frac{F_b(y)}b\ll\log B.
\]
To verify it, denote \(F_\ell=(\ell-1)/(\ell-2)\) for odd primes. Since every prime factor of \(b\le B\) is at most \(B\), extend its weighted sum to unrestricted powers of the odd primes \(\ell\le B\) not dividing \(N\). For such a prime its local geometric series is at most
\[
 1+\frac{F_\ell}{\ell-1}=1+\frac1{\ell-2}=F_\ell,
\]
whether \(\ell\le y\) or not. Hence the weighted sum is bounded by \(\prod_{3\le\ell\le B,\ell\nmid N}F_\ell\). Multiplication by \(F_N(y)\) fills in previously missing factors at \(\ell\le\min(B,y)\), and only other factors at \(B<\ell\le y\) dividing \(N\) could remain. The latter have product \(\exp(O(\omega(N)/B))=1+o(1)\) for every fixed \(\delta>0\), uniformly in \(N\), because \(B=N^{2\delta}\). All remaining factors are bounded by \(\prod_{3\le\ell\le B}F_\ell\ll\log B\) by Mertens and an absolutely convergent correction. This retains an absolute implied constant independent of \(\delta\); the threshold at which the tail is near 1 may depend on the fixed \(\delta\). In particular, even a highly variable target radical does not exaggerate the upper estimate.

Summing the main term over all these true cofactors and at most \(1+\delta L/\log2\) shells, we get
\[
 \ll \frac{H}{L^3}(1+\delta L)\log B
      \ll \delta^2 H/L + O(\delta H/L^2).
\]
The number of bad source primes is at most the number of prime triples counted, regardless of overcounting. The ordinary prime theorem in the fixed-fraction \(H\)-interval gives \((\beta-\alpha+o(1))H/(\rho L)\) distinct primes, and deleting primes dividing \(N\) costs at most \(O(L)\). By choosing the final fixed \(\delta\) sufficiently small against the uniform constant in the displayed upper bound, a positive proportion survive, as claimed.

## 3. Optional joint removal of much smaller repeated factors

There is a separate elementary exclusion which can be imposed simultaneously without disturbing the positive counts in this theorem or the companion rough theorem. For an arbitrary integer \(p\in(\alpha H,\beta H]\), the condition \(N-p=b y^2\) with integer \(b\le B_0\) gives for each \(b\) an interval for \(y\) of length \(O(H/\sqrt{Nb})\). Summing the corresponding integer bound \(O(1+H/\sqrt{Nb})\) yields
\[
 \#\{p\text{ in the interval}:N-p=b y^2,\ b\le B_0\}
       \ll B_0+H\sqrt{B_0/N}.
\]
With \(B_0=H/L^3\) this is \(o(H/L^2)\) because \(\rho\le1/2\). Consequently the surviving actual roots may also be chosen to have squarefree kernel of \(N-p\) greater than \(H/L^3\). Then *any* square divisor \(y^2\mid N-p\) has \(y<\sqrt{N/B_0}=N^{(1-\rho)/2}L^{3/2}\). In particular for \(\rho=1/2\), repeated prime factors are absent above \(N^{1/4}L^{3/2}\), much below the near-square-root zone. The squarefree kernel means product of primes with odd exponent, so the assertion is stronger than a cap on individual repeated primes. This auxiliary count uses integers, not a heuristic density for primes.

At a hypothetical no-prime-pair target these conclusions supply real composite first steps with the stated exclusions. They do not determine the number of remaining smaller distinct prime factors, ensure a high successor exists, or give a positive Goldbach count.
