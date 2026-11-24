# Three actual first-step factor thresholds

Research note, 2026-11-24. These concern literal prime inputs and prime divisors of \(N-p\), not synthetic rows or angular scores. None guarantees a prime close in size to the whole complement or supplies a Goldbach prime pair.

We use [H. M. Stark, *Effective estimates of solutions of some diophantine equations*, Acta Arith. 24 (1973), 251–259](https://matwbn.icm.edu.pl/ksiazki/aa/aa24/aa2433.pdf), Theorem 1: for every \(\eta>0\), integer solutions to \(Y^2=Z^3+K\) with nonzero integer \(K\) satisfy \(\log\max(|Y|,|Z|)\ll_\eta |K|^{1+\eta}\), with effective constant independent of the sign and value of \(K\).

## 1. Two high factors close to the square-root threshold at \(N=2^{2t}\)

Fix \(0<\varepsilon<1/8\). Let \(N=2^{2t}=X^2\), \(X=2^t\), and let \(p\) be an actual odd prime with \(p=t^{o(1)}\) uniformly in a chosen family of roots. For all sufficiently large \(t\), it is impossible for \(N-p\) to have two prime factors counted with multiplicity both exceeding
\[
 H=X-X^{1/2}t^{1/8-\varepsilon}.
\]
For example, the hypothesis holds for any fixed root, or uniformly for \(p\le\exp((\log t)^a)\) with fixed \(0<a<1\); this includes the previously constructed genuinely selectable polyloglogarithmic Linnik roots. A generic root \(p\le\sqrt N\) is **not** within the stated \(p=t^{o(1)}\) range for the Stark height argument.

Indeed, suppose \(q\le r\) are such factors, so \(qr\mid N-p\). Then \(qr>H^2>N/3\) for large \(t\), and the quotient \((N-p)/(qr)\) is odd. If it exceeded 1 it would be at least 3, which is impossible. Hence \(qr=X^2-p\). The smaller factor \(q<X\), since otherwise both are above \(X\); also \(r>X\), since otherwise their product is at most \((X-1)^2\), which is smaller than \(X^2-p\) when \(p\le X\) and \(X>1\). Put
\[
 u=(q+r)/2-X,\qquad d=(r-q)/2.
\]
These are integers, and
\[
 d^2=2^{t+1}u+u^2+p.
\]
If \(u=0\), then \(d^2=p\), impossible. If \(u<0\), write \(v=-u\), where \(1\le v<X\) because \(q+r>0\). Then \(d^2=p-v(2X-v)\le p-(2X-1)<0\) under \(p\le X\). Thus \(u\ge1\).

Suppose \(u\le T=t^{1/4-2\varepsilon}\). Write \(t+1=3j+r_0\), \(r_0\in\{0,1,2\}\), and put \(A=2^{r_0}u\), \(Z=A2^j\), \(Y=Ad\). The equation becomes
\[
 Y^2=Z^3+K,\qquad K=A^2(u^2+p)>0.
\]
We have \(Z\ge2^j\), so \(\log Z\gg t\). But \(K\ll T^4+T^2p\ll t^{1-8\varepsilon}\) since \(p=t^{o(1)}\). Choose Stark's \(\eta=4\varepsilon>0\): \((1-8\varepsilon)(1+\eta)<1\), so \(\log Z=o(t)\), a contradiction. Therefore \(u>T\). Also
\[
 X-q=\sqrt{u^2+2Xu+p}-u
\]
is increasing in \(u\ge0\), since \(X^2>p\). Thus \(X-q\ge\sqrt{2XT}-T\ge\sqrt{XT}=X^{1/2}t^{1/8-\varepsilon}\) for large \(t\) because \(T=o(X)\). This contradicts \(q>H\). This is an exclusion across a whole true two-factor window, not only a list of fixed values of \(u\), but its window still shrinks in relative terms and does not reach a fixed angular gap.

## 2. The squarefree kernel cannot be too small

For \(N=2^k\), or more generally in the previously studied regime \(R=\operatorname{rad}(N)\ll(\log\log N)^d\) for fixed \(d\), assume the actual unit prime root satisfies \(\log p=O((\log\log N)^a)\) for fixed \(a<1\). Let \(L=\log N\). For any fixed \(0<\varepsilon<1/6\), and all sufficiently large \(N\), there is no expression
\[
 N-p=b y^2,\qquad 1\le b\le L^{1/3-2\varepsilon},\quad y\in\mathbb Z_{\ge1}.
\]
This excludes **every** repeated prime factor \(q>\sqrt N/L^{1/6-\varepsilon}\), with no smoothness or fixed support requirement on the remaining cofactor: put \(y=q\) and \(b=(N-p)/q^2<L^{1/3-2\varepsilon}\). It in fact also excludes a square of any composite base above the same threshold.

Write \(N=A X^3\) with \(A\le R^2\) by reducing target prime exponents modulo 3. Set \(Z=AbX\), \(Y=Ab^2y\). Both are integers and
\[
 Y^2=Z^3-A^2b^3p.
\]
The negative constant \(K=-A^2b^3p\ne0\) is covered by Stark. Here \(\log Z\ge\log X=(L-\log A)/3\sim L/3\), and \(A^2p=L^{o(1)}\) since \(\log(A^2p)\ll\log\log\log N+(\log\log N)^a=o(\log\log N)\). Thus \(|K|\le L^{1-6\varepsilon+o(1)}\). Choose Stark's \(\eta=3\varepsilon\), so \((1-6\varepsilon)(1+\eta)<1\). The theorem would give \(\log Z=o(L)\), contradiction. Equivalently the squarefree kernel, the product of primes of odd exponent in \(N-p\), exceeds \(L^{1/3-2\varepsilon}\) in this range.

This near-\(\sqrt N\) threshold for a repeated factor is different from the rough exponent-gcd theorem. It allows the cofactor to have primes above the old tiny cutoff. It does not exclude a repeated prime far below \(\sqrt N/L^{1/6-\varepsilon}\), or an arbitrary squarefull complement with large squarefree kernel.

## 3. A truly selectable low root with a fixed angular threshold, via planted mass

For a different regime, let \(N=2^k\), \(C_{\rm Lin}\) be an absolute exponent in [Linnik's least-prime theorem, Part II](https://www.mathnet.ru/links/bb88ec18ed21db0f8a9239aee7741f6f/sm6202.pdf), and fix \(0<\theta<1/(4C_{\rm Lin})\). There is an actual odd prime \(p<N^{2C_{\rm Lin}\theta+o(1)}<\sqrt N\) whose true complement \(N-p\) does not have two prime factors counted with multiplicity both exceeding \(N^{(1-\theta)/2}\).

To construct it choose the least initial product \(b\) of odd consecutive primes \(3,5,\ldots\) with \(b\ge N^\theta\). Effective Chebyshev estimates ensure its last factor is \(O(\log N)\), so \(N^\theta\le b\le N^\theta O(\log N)\). It is squarefree and coprime to \(N\). Require the CRT class
\[
 p\equiv N-b\bmod b^2,\qquad p\equiv1\bmod2.
\]
Both conditions are reduced: each odd prime dividing \(b\) sees \(N\) as a nonzero residue. The prime \(p\) provided by Linnik is at most a constant times \((2b^2)^{C_{\rm Lin}}=N^{2C_{\rm Lin}\theta+o(1)}\), and so satisfies \(p<\sqrt N\) for large \(N\) and \((p,N)=1\). It cannot equal any prime planted in \(b\). Also \(b\mid N-p\) with \((N-p)/b\equiv1\bmod b\); every prime of \(b\) occurs in the complement **exactly once**. None of those primes is remotely as large as \(N^{(1-\theta)/2}\). Two factors counted with multiplicity above that threshold would therefore satisfy \(bqr\mid N-p\) but \(bqr>N^\theta N^{1-\theta}=N\), impossible.

For extension to even \(N\) with bounded or polylogarithmic radical, form \(b\) using only odd primes not dividing \(N\), and replace the parity condition by \(p\equiv1\bmod\operatorname{rad}(N)\). No finite place dividing \(N\), including 2, is simultaneously assigned \(N-b\bmod b^2\) or a zero residue. Removing the primes dividing \(N\) from an odd initial prime product removes log mass at most \(\log\operatorname{rad}(N)=O(\log\log N)\), which does not affect the estimates on \(b\); the added CRT multiplier is \(N^{o(1)}\). The same result follows if the radical satisfies that fixed polylog bound.

This fixed-angle threshold is driven by deliberately planted mass \(b=N^{\theta+o(1)}\). The guaranteed \(p\) is polynomial-small in \(N\), **not** in the extremely small fixed-root or polyloglogarithmic range of sections 1–2. Do not combine the two ranges without a new theorem. Also it remains possible for the complement to split into many primes below the threshold. The statement is neither existence of a near-full prime factor nor density in a central Goldbach chamber.
