# Prime indices with no debut divisor-prefix sum (Erdős #468)

**Result.** For infinitely many primes \(p\), the only element of \(D_p\) already occurs at an earlier index; no Schinzel hypothesis is needed. In fact \(f(p)/p\) tends to zero on a subsequence of primes, with a quantitative saving involving \(\log\log\log p\). There are also arbitrarily many distinct squarefree earlier witnesses for a single such prime. These are partial results about the first question of [Erdős #468](https://www.erdosproblems.com/468), not a general description of its debut counts.

## Definition and precise statement

Let \(D_m\) be the set of partial sums of the increasing list of divisors of \(m\) *strictly greater than 1*, and let
\[
f(N)=\min\{m:N\in D_m\},\qquad E_m=D_m\setminus\bigcup_{v<m}D_v.
\]
For prime \(p\), \(D_p=\{p\}\); thus \(E_p=\varnothing\) if and only if \(f(p)<p\). The final sum in \(D_m\), for \(m>1\), is \(\sigma(m)-1\).

Write \(\log_1 x=\log x\), \(\log_{j+1}x=\log(\log_j x)\). Fix a positive integer \(r\). There is an integer \(k=k(r)\ge r+1\) with the following property. For every fixed \(B\ge2\), \(M\ge1\) an integer, and \(0<\delta<1\), all sufficiently large \(X\) have
\[
\gg_{r,B,M,\delta}\frac{X}{(\log X)^{k+\delta}}
\]
distinct primes \(p\) in \([X/(4(\log X)^\delta),X]\), congruent to \(-1\bmod M\), such that **at least \(r\) distinct squarefree integers** \(m\) with no prime factor at most \(B\) satisfy
\[
 \sigma(m)-1=p,\qquad
 m\ll_{r,B,M,\delta}\frac{p}{(\log_3 p)^{1/(k-1)}}.
\]
For at least one of these witnesses the exponent can be increased to \(r/(k-1)\). In particular all the witnesses are smaller than \(p\) for sufficiently large \(X\), every such \(E_p\) is empty, and
\[
 \liminf_{\substack{p\to\infty\\ p\ {\rm prime}\\ p\equiv -1\bmod M}}\frac{f(p)}p=0.
\]

## Proof

**1. A multiplicative chain converts any pair of prime values to a witness.**
Let \(b_1,\ldots,b_{k-1}>1\) be pairwise coprime squarefree integers. Define
\[
 A_1=M,\qquad A_j=M\prod_{\ell<j}\sigma(b_\ell),
 \qquad L_j(u)=A_j(u+1)-1\quad(1\le j\le k).
\]
These forms are distinct, with positive slopes and nonnegative constant terms. For every prime \(\ell\), the choice \(u=-1\bmod\ell\) gives all their values congruent to \(-1\); hence they are admissible.

For \(i<j\) put \(b_{ij}=\prod_{i\le \ell<j}b_\ell\), and suppose both \(q=L_i(u)\) and \(p=L_j(u)\) are prime, with \(q\) larger than every prime factor used in the \(b_\ell\). With \(D=A_j/A_i=\sigma(b_{ij})>1\), multiplicativity gives
\[
 \sigma(b_{ij}q)-1=D(q+1)-1=A_j(u+1)-1=p.
\]
Its witness \(m=b_{ij}q\) is squarefree, and \(p=Dq+(D-1)>Dq\) implies
\[
 \frac{m}{p}<\frac{b_{ij}}{\sigma(b_{ij})}
   =\prod_{i\le \ell<j}\frac{b_\ell}{\sigma(b_\ell)}.
\]
For a tuple with at least \(r+1\) prime entries, fix \(p\) as its largest prime and use the smallest \(r\) prime entries as the \(q\)'s. The resulting witnesses are distinct: each has exactly one prime factor larger than every block prime, namely its own \(q\). The index distance between the largest and smallest prime entries is at least \(r\).

**2. Grow the chain slowly enough for the uniform linear-form sieve.**
Apply Maynard's [Theorem 3.4](https://arxiv.org/pdf/1405.2593) with target \(r+1\) and, for example, \(\epsilon=1/12\). It supplies \(k=k(r)\) linear forms. For each sufficiently large \(T\), the theorem counts \(\gg_r T/(\log T)^k\) integers \(u\in[T,2T]\) with at least \(r+1\) prime values for any admissible \(k\)-tuple whose slopes are positive and \(\ll(\log T)^{12}\) and whose constant terms are nonnegative and \(\ll T\). The length here is \(T\), inside the theorem's stated range. Uniformity in the admissible tuple matters below.

Set \(z=(\delta/2)\log_2 X\) and use all primes \(s\) in \((B,z]\), assigning weight \(w(s)=\log(1+1/s)\). Their total weight is
\[
 W=\sum_{B<s\le z}w(s)=\log\log z+O_B(1)
\]
by the Mertens prime sum and convergence of \(\sum_s 1/s^2\). In increasing order, partition these primes into \(k-1\) consecutive blocks by cutting after the first prefix whose weight reaches \(jW/(k-1)\) for each \(1\le j<k-1\). Since each overshoot is at most \(\log(3/2)\), and \(W/(k-1)\to\infty\), all blocks are nonempty for large \(X\), and each weight is at least \(W/(k-1)-\log(3/2)\). Taking \(b_\ell\) to be the product in block \(\ell\) gives
\[
 \frac{\sigma(b_\ell)}{b_\ell}
    \gg_{r,B,\delta}(\log z)^{1/(k-1)}
    \asymp_{r,\delta}(\log_3 X)^{1/(k-1)}.
\]
The prime number theorem and the displayed bound on \(W\) give
\[
 \log A_k
 =\log M+\sum_{B<s\le z}\log(s+1)
 =(1+o(1))z .
\]
In particular \(A_k\le(\log X)^\delta\) for all sufficiently large \(X\). Choose \(T=\lfloor X/(3A_k)\rfloor\). Then \(T\ge X/(4(\log X)^\delta)\), \(\log T\sim\log X\), and the forms meet the coefficient conditions of the sieve. Their values for \(u\in[T,2T]\) are at least \(T>z\) and at most \(A_k(2T+1)-1<X\) for large \(X\).

**3. Count different primes.**
Choose the largest prime value from every successful \(u\). Each prime can be chosen at most \(k\) times, since for each \(j\) the equation \(L_j(u)=p\) fixes \(u\) uniquely. Thus at least \(\gg X/(\log X)^{k+\delta}\) distinct primes are selected. They are \(-1\bmod M\), and \(\log_3 p\sim\log_3 X\) throughout the displayed range. Step 1 gives \(r\) witnesses, with the extra exponent \(r/(k-1)\) for the witness constructed from the smallest prime value. This proves the theorem. \(\square\)

There is also a fixed-cofactor version. For any fixed \(R>1\), use \(k-1\) fixed disjoint blocks of primes above \(B\) such that each \(\sigma(b_\ell)/b_\ell>R\); their existence follows from divergence of the reciprocal-prime sum. Applying the same sieve and count with constant \(A_k\) gives \(\gg X/(\log X)^k\) primes with \(r\) witnesses \(m<p/R\) and with \(m/q\) in a fixed finite set. The growing construction trades a small power of \(\log X\) in the lower count for a saving that improves with \(p\).

## Prior work and limits

* Erdős and Graham ask about \(|E_m|\) in *Old and New Problems and Results in Combinatorial Number Theory*, 1980, p. 93; see [the problem and source information](https://www.erdosproblems.com/468) and [OEIS A387502](https://oeis.org/A387502). [Kovač's discussion](https://www.erdosproblems.com/forum/thread/468) notes a conditional infinitude example: prime \(p=uv+u+v\) for prime \(u,v\) is \(\sigma(uv)-1\) and has \(E_p=\varnothing\). The chain above keeps the same divisor-sum identity but guarantees that *whichever* two forms give primes lead to one of the required identities. The [working report for #468](https://erdosproblemaday.com/report/468) also lists the Schinzel approach as conditional.
* The sieve is James Maynard, *Dense clusters of primes in subsets*, Compos. Math. **152** (2016), 1517–1554, [Theorem 3.4](https://arxiv.org/abs/1405.2593). Kevin Ford uses pairs of prime linear forms of shape \(au-1,bu-1\) and multiplicativity to construct equal divisor sums for two composite inputs, in [*Solutions of \(\varphi(n)=\varphi(n+k)\) and \(\sigma(n)=\sigma(n+k)\)*](https://academic.oup.com/imrn/article/2022/5/3561/5896974), Theorem 5. Here the divisibility chain instead makes the **common sum minus one itself a prime**, and growing disjoint blocks control the ratio of that prime to its earlier witnesses.
* This proves unconditional infinitude, not positive density of empty debut sets among integers or even among primes. It does not prove that \(|E_m|\) is unbounded, determine its distribution, or resolve a new version of the second question about \(f(N)\) on all or almost all integers. For that second question see Tao and [Kovač](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_1054.pdf) and the [November 2026 manuscript of Chae, Fraiture, Hou, Kovač, Kudeba, Shakov and Vidal](https://www.ehou.me/assets/erdos-1054-prefix-sums-of-divisors.pdf), Sections 1 and 4. Those authors include the divisor 1, so the present f(p) is their f(p+1). Their positive-density lower tail for general integer arguments does not imply the result on shifted primes here.

Finite algebra checks: run the companion verifier with Node.js. It checks the prime-pair identity and exact witness inequalities in small numerical examples. The infinitude proof uses the analytic theorem, not the finite run.
