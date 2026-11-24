# Squarefree genuine rough roots and an unbalanced range of real three-factor rows

Research note, 2026-11-24. Uses the exact thin-band upper sieve previously derived for genuine prime-opposite rows. It neither assumes nor proves a Goldbach pair, and it does not exclude the three-cube-root-scale rank-three family.

Fix \(0<\alpha<\beta<1\), \(0<\mu<1/8\), and \(\mu<\kappa<1/4\). For even \(N\), let \(H=\sqrt N\), \(L=\log N\), \(z=N^\mu\), and \(F_N(z)=\prod_{3\le\ell\le z,\ \ell\mid N}(\ell-1)/(\ell-2)\) over primes. There is a fixed \(\delta>0\) such that for all sufficiently large even \(N\), at least \(cF_N(z) H/L^2\) actual distinct unit primes \(p\in(\alpha H,\beta H]\) have a complement that is
1. \(z\)-rough and squarefree;
2. never divisible by two prime factors \(>N^{1/2-\delta}\) counting multiplicity;
3. for every prime factor \(q\le N^\kappa\), never divisible by \(q r s\) with two other prime factors \(r,s>\sqrt{N/q}\,N^{-\delta}\).

The last statement involves true factors, not coprime replacement variables or an ordinary random-factor model. (Squarefreeness also makes the multiplicity convention inconsequential on the final retained rows.)

## 1. Remove squareful complements at an integer cost

The genuine positive lower bound for rough prime sources is \(\gg F_N(z)H/L^2\), by the fixed-\(N\) Bombieri–Vinogradov plus lower linear sieve proof in [the preceding fixed-angle proof](PrimeOppositeFixedAngleExclusion.md). For a rough complement, every repeated prime divisor \(r\) is \(>z\). For \(z<r\le N^{1/3}\) count even all integer sources satisfying \(r^2\mid N-p\) on the \(H\)-scale interval. The total is
\[
 O\left(\sum_{z<r\le N^{1/3}}\bigl(H/r^2+1\bigr)\right)
       =O(H/z+N^{1/3}),
\]
where we may sum over integers \(r\). For \(r>N^{1/3}\), switch to the genuine cofactor \(b=(N-p)/r^2<N^{1/3}\). For each \(b\), the possible \(r\)'s lie in an interval of length \(O(H/\sqrt{Nb})\). Counting integers and summing gives
\[
 O\left(N^{1/3}+\frac H{\sqrt N}\sum_{b<N^{1/3}}b^{-1/2}\right)
       =O(N^{1/3}+H/N^{1/3}).
\]
Together this is \(o(H/L^2)\). This particular squarefree removal works in the full earlier range \(H=N^\rho,\,\rho>1/3\); it is not a global density assumption for squareful rows on all prime intervals.

The earlier fixed-angle exclusion of item 2 costs at most \(C_1\delta F_N(z)H/L^2+o(F_N(z)H/L^2)\), with \(C_1\) independent of the final sufficiently small \(\delta\). We now pay for item 3 on the same genuine rows.

## 2. The new rank-three deletion, keeping the first prime factor variable

For a \(z\)-rough root, if \(q\le N^\kappa\) and two other factors \(r,s>\sqrt{N/q}\,N^{-\delta}\) occur, then
\[
 1\le b=(N-p)/(qrs)<N^{2\delta}<z
\]
when \(2\delta<\mu\). Roughness forces \(b=1\), so this really is a rank-three row \(N-p=qrs\). We then use \(z<q\le N^\kappa\), \((q,N)=1\), and sort \(r\le s\). With \(T=N/q\), the range \(T^{1/2}N^{-\delta}<r\le T^{1/2}\) is covered by at most \(1+\delta L/\log 2\) dyadic shells \(r\in J\subset[Q,2Q]\). Work at fixed actual prime \(q\), and sum over all these primes only after a uniform estimate.

Use half-integer source cuts \(A=\lfloor\alpha H\rfloor+1/2\), \(C=\lfloor\beta H\rfloor+1/2\). The integer band is
\[
 r\in J,\qquad (N-C)/(qr)<s<(N-A)/(qr).
\]
It has real area \(\mathcal V_q=(C-A)q^{-1}\int_J dr/r\ll H/q\) and no integral boundary points. The condition \(s\ge r\) may be dropped for the upper bound, because \(s\asymp T/Q\) and all prime variables being counted still exceed the upper small sieve cutoff.

For residue pairs \(r=a+d j,\ s=a'+d k\) modulo \(d\le D=N^\lambda\), the two phases in the interval count are \(f_c(j)=(N-c)/(qd(a+d j))-a'/d\), with \(c=A,C\), second derivative comparable to \(dT/Q^3\) throughout a shell. The length main term is \(\mathcal V_q/d^2+O(H/(q d Q))\) by the same monotone progression integral as in the companion proof. For Fourier frequency \(h\) the second derivative estimate has bound
\[
 \ll \frac{\sqrt T\,\sqrt h}{\sqrt{Qd}}
       +\frac{Q^{3/2}}{\sqrt T\,\sqrt{hd}}
\]
for the endpoint exponential sum. Use Erdős–Turán with \(M=\lfloor T^{1/6}\rfloor\); the length term \(Q/(dM)\) is \(O(T^{1/3})\), the first harmonic term is \(O(T^{1/3}N^{\delta/2})\), and the second is \(O(T^{1/4})\). The extra main term error \(H/(q d Q)\) is absorbed using \(Q\ge T^{1/2}N^{-\delta}\), \(H=\sqrt N\). There is no frequency coprimality condition. Hence the actual thin band in each residue pair has error \(O(T^{1/3}N^{\delta/2})\), with its full \(N/q\) dependence retained, even if individual vertical intervals have length less than one.

Sieve the literal \(r s(N-qrs)\) in this band for primality of \(r,s,p\). For an odd prime \(\ell\mid qN\) there are \(2\ell-1\) forbidden residue pairs (axes); otherwise there are \(3\ell-2\). The even prime has the usual 3. Use \(Z=N^{\lambda/2}\), and the same exact Selberg weights and \(y=Z^\nu\le z\) as in the companion proof. The extra exceptional prime \(q>z\) lies outside \(y\); hence the truncated Euler product supplying the main denominator receives no extra local factor from \(q\), though \(q\) can be below the full sieve \(Z\). The main bound per shell is therefore \(C H F_N(z)/(qL^3)\). Summing by the lcm of the two Selberg divisors gives per-shell total error
\[
 O\bigl((N/q)^{1/3}N^{\delta/2}D^{2+o(1)}\bigr),
\]
using the squarefree residue count \(\le 3^{\omega(l)}l\) for \(l\) and the companion bound \(|\lambda_d|\le5^{\omega(d)}\).

First fix \(\delta_0,\lambda>0\) sufficiently small that
\[
 1/3+2\kappa/3+\delta_0/2+2\lambda<1/2,
\]
and small enough for the earlier fixed-angle result; choose \(\nu\) after them, independently of the final \(0<\delta\le\delta_0\). In the error, summing \(q^{-1/3}\) for \(q\le N^\kappa\) gives \(O(N^{2\kappa/3})\) even over all integers, and \(O(L)\) shells do not use up the power saving. In the main term, summing \(1/q\) only over actual primes \(z<q\le N^\kappa\) gives \(O_{\mu,\kappa}(1)\) by the standard prime harmonic estimate (log–log difference \(\log(\kappa/\mu)\)). Thus the new bad rows cost at most
\[
 C_2\delta F_N(z)H/L^2+o(F_N(z)H/L^2),
\]
uniform in final fixed \(\delta\); overcounting a row through several triples can only help the upper bound. Choose additionally \(2\delta<\mu\) and \((C_1+C_2)\delta<c_0/2\) where \(c_0\) is the rough cloud lower constant. Subtract both deletion costs and the squareful integer count to get all three simultaneous conditions.

## 3. Consequences at a putative no-pair target and the true remaining gap

Then every survivor is a genuine composite complement, and every factor \(>z\). If it has exactly two prime factors \(r\le s\), these are distinct, \(r\le N^{1/2-\delta}\), and \(s\ge (1-o(1))N^{1/2+\delta}\). This is a unique high arc above \(\sqrt N\); since the source \(p<\sqrt N<s\), distinct semiprime source rows give distinct high labels, each with globally unique smaller predecessor \(p=N\bmod s\). In a higher-arity row there are at least two distinct factors \(\le N^{1/2-\delta}\). A prime factor \(>N^{1-2\mu}\) would automatically force arity exactly two (the remaining rough cofactor is below \(N^{2\mu}\)); we do not prove such a factor exists.

For a genuine rank-three row with smallest factor \(q\le N^\kappa\), its other factors \(r\le s\) must satisfy
\[
 r\le \sqrt{N/q}\,N^{-\delta},\qquad
 s\ge(1-o(1))\sqrt{N/q}\,N^\delta .
\]
If instead its least factor is \(>N^\kappa\), this last exclusion does not apply. Nor does it give a lower bound for the number of rank-two survivors or force a contradiction in the rank at least three branch. Chen results for a prime source substantially smaller than \(N\) do not supply a rank-two lower bound at the present \(\sqrt N\) source scale.

For the genuinely balanced three-factor box \(q,r,s\asymp N^{1/3}\), the same one-variable calculation yields per-\(q\) discrepancy \((N/q)^{1/3}\asymp N^{2/9}\); even before residue moduli, summing \(N^{1/3}\) values of \(q\) gives \(N^{5/9}\), worse than the true thin source size \(N^{1/2}\). To use this method one needs a genuinely two-variable discrepancy saving \(O(N^{1/2-\eta})\), uniform for modular residue classes and the two real endpoints, for phases
\[
 (j,k)\longmapsto
 \frac{N-c}{d(a+d j)(b+d k)}-\frac{a'}d .
\]
A two-dimensional Poisson analysis without cancellation of dual terms suggests size \(hN^{1/3}\) at \(d=1\) at Fourier frequency \(h\), and optimizing the one-dimensional discrepancy cutoff only gives \(N^{1/2}\) at \(h\asymp N^{1/6}\), not a power saving. A stationary-phase transform to a dual \((mn)^{1/3}\)-type phase with higher-derivative cancellation is a possible route, not a proved estimate here. This is the specific missing Type II/III input. No general contradiction to an all-composite closure follows.
