# Prime-power capacity bounds for the Brocard–Ramanujan equation

**Scope.** A structural partial result for \(n!+1=m^2\), not a larger exhaustive search, and not a solution to the unrestricted equation. A \(K\)-free integer is one divisible by no \(p^K\) with \(p\) prime. All logarithms are natural.

[Makki Naciri, INTEGERS 25 (2025), A71, Theorem 1 and equation (2)](https://math.colgate.edu/~integers/z71/z71.pdf) proves finiteness for any fixed \(K\) when \(m-1\) or \(m+1\) is \(K\)-free, with an upper bound exponential in \(K\), and reports explicit exhaustion for the 7-free subclass. The same work proves finiteness when the number of prime factors of a neighbor is bounded. Here the complete prime-power allocation gives a quadratic bound, as well as a joint threshold for how many large prime powers each neighbor has to carry. Independent [Epstein–Glickman computations](https://github.com/jhg023/brocard/blob/master/README.md) report no further solutions through \(10^{15}\); the experiments accompanying this note do not recheck or extend that search.

## 1. Exact partition and an effective \(K\)-free bound

For any solution with \(n\ge4\), \(m\) is odd, and
\[
a=(m-1)/2,\qquad b=(m+1)/2,\qquad ab=N:=n!/4,\qquad \gcd(a,b)=1.
\]
Let \(E\) denote the even one of \(a,b\) and \(O\) the odd one. Every odd prime power \(p^{v_p(n!)}\) goes wholly to exactly one of the two, and \(2^{v_2(n!)-2}\) goes to \(E\). Both factors satisfy \(\log a,\log b<\tfrac12\log(n!)\) and \(\log a,\log b=\tfrac12\log N+o(1)\) as \(n\to\infty\).

**Finite theorem.** For any solution with \(n\ge10^6\):

* \(O\) contains an odd prime at most \(\lfloor2\sqrt n\rfloor\) and \(E\) contains an odd prime at most \(\lfloor4\sqrt n\rfloor\).
* Both \(m-1\) and \(m+1\) are divisible by a prime to exponent at least \(\lfloor\sqrt n/2\rfloor\) (the even normalized neighbor can use 2). If only odd primes are allowed, both still have an exponent at least \(\lfloor\sqrt n/4\rfloor\).

In particular, if either neighbor \(m\pm1\) is \(K\)-free for \(K\ge2\), then
\[
\boxed{\ n<\max\{10^6,4K^2\}.\ } \tag{1}
\]
Together with the published range \(n<10^9\) of [Berndt–Galway (2000)](https://link.springer.com/article/10.1023/A:1009873805276), this exhausts the subclass in which at least one neighbor is **15,811-free**: its positive solutions remain \((4,5),(5,11),(7,71)\). Using instead the larger range reported in the Epstein–Glickman repository gives the same conclusion for the **15,811,388-free** subclass. The underlying range certifications are cited inputs, not rerun here.

**Proof.** For integer \(u\le n\) and \(Q=\lfloor n/u\rfloor\), the factorial block \((u!)^Q\) divides \(n!\). This follows from the multinomial coefficient \(n!/((u!)^Q(n-Qu)!)\). If \(O\) has no odd prime up to \(u=\lfloor2\sqrt n\rfloor\), then \((u!)^Q/4\) divides \(E\). If \(E\) has no odd prime up to \(u=\lfloor4\sqrt n\rfloor\), then the odd part of \((u!)^Q\) divides \(O\).

In the first case set \(\sigma=0\); in the second case set \(\sigma=1\). The logarithms of the forced divisors are at least
\[
Q u(\log u-1-\sigma\log2)-\log4
\]
by \(\log(u!)\ge u(\log u-1)\) and \(v_2(u!)\le u\). The harmless subtraction of \(\log4\) covers both cases. Write \(s=\sqrt n\). Then \(u/2^\sigma\ge(19/10)s\), \(u\le4s\), and \(Qu\ge n-u\). The logarithmic factor is positive and at most \(\log n\). Since \(\log(19/10)>18/29\) (the first term of the logarithm's arctanh series) and \(u\log n/n\le 7/125\) (using \(s\ge1000\), \(\log(10^6)<14\), and monotonicity of \(\log n/\sqrt n\)), this lower bound is strictly greater than
\[
n(\tfrac12\log n-\tfrac12+1/20)-\log4.
\]
It exceeds \(\tfrac12\log(n!)\le \tfrac12(n\log n-n+1+\log n)\) for every \(n\ge10^6\), a contradiction. This proves the small-prime bounds. The full exponent at either such prime is at least \(\lfloor n/p\rfloor\), and \(v_2(E)=v_2(n!)-2\ge\lfloor n/2\rfloor-2\). These give the stated exponent bounds and (1).

## 2. Asymptotic prime-power mass

Put \(e_p=v_p(n!)\), \(w(p)=\log p/(p-1)\), and
\[
S_n(y)=\sum_{p\le y}e_p\log p .
\]
For \(p\le\sqrt n\), Legendre's digit-sum formula gives \(0\le nw(p)-e_p\log p\le 2\log n\). For \(p>\sqrt n\), \(e_p=\lfloor n/p\rfloor\) and the lost weight is at most \(3\log p\). Therefore
\[
S_n(y)=n\sum_{p\le y}w(p)+O\big(\sqrt n\log n+\vartheta(y)\big).
\]
In particular, for \(y\to\infty\), \(y=o(n)\), the prime number theorem gives
\[
S_n(y)/n=\log y-\gamma+o(1), \tag{2}
\]
where \(\gamma\) is Euler's constant. To see the constant without assuming a numerical approximation to a prime sum, apply the factorial identity at integer \(t\) to the difference
\[
t\sum_{p\le t}w(p)-\log(t!)
 =\sum_{p\le t}\{t/p\}\log p+O(\sqrt t\log t).
\]
For \(p\le\sqrt t\) one can absorb both terms in the error. For \(p>\sqrt t\), subtracting the fractional part leaves \(t\log p/(p(p-1))\), whose sum is \(O(\sqrt t\log t)\). Weighted prime Riemann sums, using \(\vartheta(t)\sim t\), give the limiting sum divided by \(t\) as
\[
\int_0^1\{1/u\}\,du
 =\lim_{j\to\infty}\sum_{i=1}^j\big(\log(1+1/i)-1/(i+1)\big)=1-\gamma.
\]
The integrand is bounded and Riemann integrable; convergence follows first away from zero, and then by a small-interval bound at zero. Stirling's formula gives \(\sum_{p\le t}w(p)=\log t-\gamma+o(1)\), extended to real \(t\) by rounding. This proves (2).

As a consequence, set \(c_0=\exp(\gamma-1/2)\). For all sufficiently large solutions, in asymptotic form
\[
P^-_{\rm odd}(O)\le(c_0+o(1))\sqrt n,\qquad
P^-_{\rm odd}(E)\le(2c_0+o(1))\sqrt n. \tag{3}
\]
Here \(P^-_{\rm odd}\) is the smallest odd prime factor. Indeed, the total weight of primes \(p\le c\sqrt n\) is \(n(\tfrac12\log n+\log c-\gamma+o(1))\), while either neighbor's logarithm is \(n(\tfrac12\log n-\tfrac12+o(1))\). If no odd such prime belongs to \(O\), all of this weight except the harmless normalization \(\log4\) lies in \(E\); this is impossible for any fixed \(c>c_0\). If none belongs to \(E\), remove the \(2\)-weight \(n\log2+O(\log n)\); the remainder still exceeds \(\log O\) when \(c>2c_0\).

In particular \(O\) has some prime exponent at least \((c_0^{-1}-o(1))\sqrt n\), whereas \(E\) has an odd prime exponent at least \(((2c_0)^{-1}-o(1))\sqrt n\), in addition to its exponent of 2. Along any large solutions for which either \(m\pm1\) is \(K\)-free, one has \(n\le(c_0^2+o(1))K^2\). The finite bound (1) is independent of this asymptotic.

## 3. How many large exponents must occur?

For \(D\in\{E,O\}\), let \(R_K(D)=\#\{p\text{ odd}:v_p(D)\ge K\}\). The total logarithmic weight available from odd primes below exponent \(K\) in the whole factorial is
\[
L_K(n)=\sum_{\substack{p\ {\rm odd}\\e_p<K}} e_p\log p .
\]
Introduce \(\sigma=1\) for \(D=E\), \(\sigma=0\) for \(D=O\), and let \(p_1=3,p_2=5,p_3=7,\ldots\) be the odd primes. The capacity principle is
\[
\frac{\log D}{n}\le
 \frac{L_K(n)}n+\sigma\log2+\sum_{i=1}^{R_K(D)} w(p_i). \tag{4}
\]
This follows by assigning all low-weight blocks to the chosen factor, then using \(e_p\log p\le n w(p)\) and the decrease of \(w\) on \(p>1\) to bound its high blocks by the largest allowable weights. The exact finite capacity, if needed, is obtained by sorting the actual block sizes \(p^{e_p}\) within the high set, not by assuming they are ordered by \(p\). This reflects allocation of whole prime powers rather than independent choices of exponents.

### Subcritical exponents

For every integer choice \(1\le K=o(\sqrt n)\), let \(H_K=\sum_{j=1}^K1/j\) and \(s=\sqrt n\,\exp(\gamma+1/2-H_K)\). Then \(s\asymp\sqrt n/K\to\infty\), and
\[
R_K(E)\ge(1-o(1))\,s/\log s,\qquad
R_K(O)\ge(2-o(1))\,s/\log s. \tag{5}
\]
In particular at \(K=1\) the respective odd-prime counts are at least \((2c_0-o(1))\sqrt n/\log n\) and \((4c_0-o(1))\sqrt n/\log n\), strengthening the fixed-number-of-primes results.

For the proof, \(e_p\ge K\) is guaranteed for \(p\le n/K\) and implies \(p\le 1+n/K\). For \(K\) fixed and \(n\) large, the low primes are exactly \(p>n/K\); by the prime number theorem the total weight from \(p/n\in(1/(j+1),1/j]\), after weighting with exponent \(j\), is \(n/(j+1)+o(n)\). Thus \(L_K(n)/n=H_K-1+o(1)\) for fixed \(K\). If \(K\to\infty\) in the indicated range, use (2) at \(n/K\), noting that the possible boundary block has weight \(o(n)\). Subtraction from \(\log(n!)/n\) gives \(\log K+\gamma-1+o(1)=H_K-1+o(1)\). The same statement for varying \(K\) follows by taking subsequences that are either constant or tend to infinity. In (4) the resulting required high mass grows as \(\log(\sqrt n/K)\), so \(R_K(D)\to\infty\). Using \(\sum_{p_i\le y}w(p_i)=\log y-\gamma-\log2+o(1)\) and the prime number theorem for the resulting lower bound on \(p_{R_K(D)}\) yields (5).

### Critical exponents

For \(K/\sqrt n\to\kappa>0\), the same computation gives
\[
\frac{L_K(n)}n=\tfrac12\log n+\log\kappa+\gamma-1+o(1).
\]
For any fixed \(r\ge0\), if
\[
\boxed{\quad \tfrac12-\gamma-\log\kappa>\sigma\log2+\sum_{i=1}^{r}w(p_i),\quad} \tag{6}
\]
then eventually the indicated neighbor contains **more than \(r\)** odd prime powers of exponent at least \(K\). The criterion is stated with a strict inequality; the equality case is not determined here. This is a quantitative analogue of restricting the number of high-exponent factors, rather than only bounding the single highest exponent.

## 4. Sharpness for size-balanced coprime divisors, not for consecutive neighbors

For clarity, call a pair of full-block factors \(A B=N\) log-balanced when \(\log A,\log B=\tfrac12\log N+o(n)\); it need not satisfy \(B-A=\pm1\).

* To attain either bound (5) separately in this model, assign all low odd blocks to the designated side \(D\), give it 2 precisely when \(\sigma=1\), and then append the high odd blocks in increasing order of their primes until its logarithm first reaches \(\tfrac12\log N\). At any fixed multiple of \(s\) those primes are high, because \(n/K\asymp s\sqrt n\). By (2) and the formula for \(L_K\), the crossing lies at \((1+o(1))s\) for the even side or \((2+o(1))s\) for the odd side. The crossing block has size \(o(n)\) in logarithmic weight, so the split is log-balanced and the high count has the claimed asymptotic. At \(K=1\), the other factor's least odd prime is the next prime beyond the cut, so these examples also exhibit both constants in (3), separately.
* If the strict reverse of (6) holds, assign the designated factor all low odd blocks and its first \(r\) high odd blocks, plus 2 as required. Its logarithm then exceeds the half target by a positive multiple of \(n\), using \(e_p/n\to1/(p-1)\) for each fixed high prime. The selected low mass is of order \(n\log n\), and each low block has logarithmic weight \(o(n)\) since its prime is at least on the \(\sqrt n\) scale. Remove low blocks until first crossing below the target. The resulting split is log-balanced, with at most \(r\) high odd blocks and the designated parity.

This proves that the leading constants in (5) and the strict threshold in (6) cannot be improved from size and coprime block allocation alone on this scale. Nothing here replaces the exact difference \(b-a=1\). In particular the computation and asymptotic argument do not extend the unconditional exhaustive range in \(n\).

## Reproduction

Run the adjacent Node.js verifier (no dependencies). It uses exact integer arithmetic to check the cutoff comparisons, factorial block divisibility, exponent threshold tests, and the tight finite capacity on small complete subset enumerations. The small direct square controls are not the cited global range search. The analytic steps use the stated prime number theorem and the displayed proofs, not numerical fits.
