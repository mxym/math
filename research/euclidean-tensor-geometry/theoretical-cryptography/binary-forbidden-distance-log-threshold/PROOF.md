# The threshold of the Jiang–Yang binomial criterion

All logarithms below are natural, except binary entropy \(H_2\).

## 1. The known extremal implication and the new threshold

For integers \(t\ge3\) and \(N\ge t\) with \(N\equiv t\pmod2\), put
\[
 r=(N-t)/2,\quad V_N(j)=\sum_{i=0}^{j}\binom Ni,\quad
 B(N,t)=2^{-N}V_N(r)\frac{V_N(t-2)}{V_N(t-3)}.
\]
The original cube has dimension \(n=N+1\), and \(n-t+1=2r+2\) is the even forbidden distance. Jiang–Yang [JY, Corollary 4.5, Eq. (4.10)] proves that \(B(N,t)>1\) suffices for the two-consecutive-distance avoidance problem in the \(N\)-cube to have optimum \(V_N(r)\) and all its extremizers to be radius-\(r\) Hamming balls. The parity splitting and lifting of [JY, Lemma 3.2 and Proposition 3.3] then give the original \(n\)-cube optimum \(2V_N(r)\); its extremizers are obtained by appending the even-parity bit to one such ball and the odd-parity bit to another. The ball centers may be independent. Their sufficient estimate [JY, Proposition 5.3] assumes \(n\ge(t+1)^2\).

**Theorem.** For each \(t\ge3\) there is a unique first admissible integer \(N_*(t)\) at which \(B(N,t)>1\), and every larger admissible integer still satisfies that strict inequality. Its asymptotic expansion is
\[
 \frac{t^2}{2N_*(t)}
   = \log t-\frac32\log\log t-\log(4\sqrt\pi)+o(1).
 \tag{1}
\]
Consequently the exact optimum and all extremizers just described hold for every admissible \(n\ge N_*(t)+1\). In particular they hold for \(n\ge(\tfrac12+\eta)t^2/\log t\) for every fixed \(\eta>0\) and all sufficiently large \(t\). On the other side \(n\le(\tfrac12-\eta)t^2/\log t\) makes the **criterion** fail for all large \(t\); it makes no such assertion about the original optimum.

## 2. Strict monotonicity and the parity boundary

Write \(a_N=2^{-N}V_N((N-t)/2)\) for fixed \(t\). If \(X\) is \(\mathrm{Bin}(N,1/2)\), the \((N+2)\)-dimensional probability at its corresponding radius \(r+1\) is obtained by adding an independent \(\mathrm{Bin}(2,1/2)\). Thus
\[
 a_{N+2}=a_N+\frac14\bigl(\Pr[X=r+1]-\Pr[X=r]\bigr)>a_N.
\]
The strict inequality holds because \(\binom N{r+1}/\binom Nr=(N-r)/(r+1)>1\) when \(N-2r=t>1\).

For \(k=t-3\), the second factor is
\[
 \frac{V_N(k+1)}{V_N(k)}=1+\left(\sum_{j=0}^k\frac{\binom Nj}{\binom N{k+1}}\right)^{-1}.
\]
Each summand equals \((k+1)!/(j!\prod_{h=j}^{k}(N-h))\), which strictly decreases as \(N\) increases in its range. Therefore both positive factors increase. At the first admissible \(N=t\) we have \(a_N=2^{-t}\), and \(V_t(t-2)<2^t\) while \(V_t(t-3)\ge1\), so the product is below one. For fixed \(t\), \(a_N\to1/2\) by binomial symmetry and \(O(N^{-1/2})\) maximal mass, and the second factor is asymptotic to \(N/(t-2)\) by leading terms of the two finite binomial sums. Hence the product tends to infinity. This proves the first claim, including cases where an admissible integer has exact equality: the threshold is defined by strict \(>\).

## 3. A two-sided binomial estimate in the crossing window

Let \(t\to\infty\) through integers and \(N\) be admissible with \(N\sim t^2/(2\log t)\). Put \(u=t/N\) and \(z=t^2/(2N)\). Then \(u\to0\), \(N u^2\to\infty\), \(N u^4\to0\), and \(r=N(1-u)/2\). Stirling's formula at \(N,r,N-r\), all tending to infinity, gives the point mass \(b_r=2^{-N}\binom Nr\) as
\[
 b_r=(1+o(1))\sqrt{\frac{2}{\pi N(1-u^2)}}\,\exp[-N I(u)],\qquad
 I(u)=\tfrac12[(1-u)\log(1-u)+(1+u)\log(1+u)] .
\]
Since \(I(u)=u^2/2+O(u^4)\) as \(u\to0\), it follows that \(b_r=(1+o(1))\sqrt{2/(\pi N)}\,e^{-z}\). The error in the exponent tends to zero, not merely to \(o(z)\).

For the mass below \(r\), let \(\rho=r/(N-r+1)\). The backward ratios satisfy
\[
 \frac{a_N}{b_r}
  =\sum_{j=0}^{r}\prod_{i=0}^{j-1}\frac{r-i}{N-r+i+1}
  \le\sum_{j\ge0}\rho^j=\frac1{1-\rho}.
 \tag{2}
\]
Here \(1-\rho\sim 2u\). For a lower bound, fix a positive real \(A\) and restrict to \(0\le j\le J=\lfloor A/u\rfloor\). For large \(t\), \(J<r\). The logarithm of the ratio of the product in (2) to \(\rho^j\) equals
\[
 \sum_{i=0}^{j-1}\left[\log(1-i/r)-\log(1+i/(N-r+1))\right].
\]
The two arguments perturb \(1\) by \(O(J/N)\); the sum has absolute value \(O(J^2/N)=O_A(N/t^2)=o(1)\), uniformly for \(j\le J\). Thus the truncated sum is at least
\((1-o(1))(1-\rho^{J+1})/(1-\rho)\). Since \(\rho^{J+1}\to e^{-2A}\), the liminf of \((1-\rho)a_N/b_r\) is at least \(1-e^{-2A}\). Let \(A\to\infty\) and use (2). We obtain the **relative-error** formula
\[
 a_N=(1+o(1))\,\frac{\sqrt N}{t\sqrt{2\pi}}e^{-z}.
 \tag{3}
\]
A central limit approximation with only absolute CDF error would not justify (3) in this tail.

For \(j=t-2\) or \(t-3\) the same backward-ratio upper bound gives
\(1\le V_N(j)/\binom Nj \le (1-j/(N-j+1))^{-1}=1+o(1)\), because \(t=o(N)\). Hence \(V_N(t-2)/V_N(t-3)=(1+o(1))\,N/t\). Multiplying by (3),
\[
 B(N,t)=(1+o(1))\,\frac{t\,e^{-z}}{4\sqrt\pi\,z^{3/2}}.
 \tag{4}
\]
All these statements apply along any sequence with the indicated scaling; no approximation at a fixed \(t\) is used to obtain the threshold.

## 4. Locate the unique crossing and transfer the conclusion

Write
\[
 z_0(t)=\log t-\tfrac32\log\log t-\log(4\sqrt\pi).
\]
For each fixed real \(c\), choose admissible \(N\) by rounding \(t^2/(2(z_0(t)+c))\) to a nearest integer congruent to \(t\) modulo 2; for large \(t\) it exceeds \(t\). This changes \(z\) by \(O(t^2/N^2)=o(1)\). We have \(\log z=\log\log t+o(1)\), so (4) implies
\[
 B(N,t)\longrightarrow e^{-c}.
 \tag{5}
\]
For every fixed \(\varepsilon>0\), setting \(c=+\varepsilon\) and \(c=-\varepsilon\) gives values strictly below and above one, respectively, for all sufficiently large \(t\). Monotonicity brackets the first crossing between those admissible integers. Since \(\varepsilon\) is arbitrary, this proves (1). It also computes the limiting coefficient in the known bound [JY, Proposition 4.4]: if \(z=z_0(t)+c+o(1)\), then their \(\kappa=B-1\) tends to \(e^{-c}-1\).

We use only the known sufficient criterion and parity lifting for the extremal conclusion. We do not show the ball formula to be false whenever \(B\le1\), nor do we identify the exact extremal threshold. For example, at \(t=3\), the first two admissible \(N\) are \(3,5\); \(B(3,3)=1/2\) and \(B(5,3)=36/32>1\), so the stated equality result applies at every even original dimension \(n\ge6\). At \(n=4\) the four words \(0000,1111,0001,1110\) avoid distance \(2\), exceeding the ball formula \(2\). This particular exception is not a converse to the criterion.

## 5. A simple range where the ball optimum really fails

For additional separation of the two questions, let \(\delta\in(0,1/8)\) be fixed and consider admissible even forbidden distances \(d=n-t+1\) with \(d/n\to\delta\). The graph on the binary cube connecting pairs at distance \(d\) has maximum degree \(\binom nd\), so iteratively selecting one vertex and removing its neighbors gives an avoiding code of size at least \(2^n/(1+\binom nd)\). By Stirling its exponential rate is at least \(1-H_2(\delta)\). The rate of the ball formula is \(H_2(\delta/2)\), as follows by bounding the volume between one binomial coefficient and \(n\) times that coefficient. The former rate exceeds the latter: monotonicity of binary entropy on \([0,1/2]\) and
\[
 H_2(1/8)+H_2(1/16)<1
\]
suffice. The last inequality is equivalent to \(7^{14}15^{15}>2^{96}\), directly checked by integer multiplication. Thus in this linear-in-\(t\) regime the ball optimum fails for all sufficiently large dimensions. This elementary contrast does not turn (1) into the true threshold, since there remains a wide gap between the two regimes.
