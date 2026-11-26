# Four higher even exponents in any odd perfect number coprime to 3

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review or priority claim.

**Theorem.** If an odd perfect number \(N\) is not divisible by \(3\), then at least four distinct primes other than its Euler prime have exponent at least \(4\).

This strengthens the coprime-to-\(3\) case of [Ochem–Zelinsky, arXiv:2607.19746 §2](https://arxiv.org/html/2607.19746v1#S2), which treats just one such exponent. The approach below uses their divisor-sum support reduction and a finite exact arithmetic certificate with uniformly bounded large-prime contributions. No conclusion is asserted about the branches where \(3\mid N\).

## Factor support

By Euler's theorem \(N=P^e m^2\), with prime \(P\equiv e\equiv1\bmod4\) and \(P\nmid m\). Since \(P+1\mid\sigma(P^e)\mid 2N\), coprimality with \(3\) implies \(P\equiv1\bmod12\). Call a prime other than \(P\) notable if its exponent is at least four, and ordinary if its exponent is two. Suppose at most three are notable. Pad this distinguished list, consisting of \(P\) and the notable primes, to length four by arbitrary unused primes \(1\bmod3\) if necessary, treating extra factors as increasing an upper bound only.

Every ordinary prime \(s\) is \(5\bmod6\), since otherwise \(3\mid s^2+s+1\). Every prime \(r\mid s^2+s+1\) is \(1\bmod3\): \(r\ne3\), and \(s\) has order three modulo \(r\). Because \(r\mid 2N\), it is not ordinary and belongs to the distinguished list. Write \(T\) for the subset of that list congruent to one mod three, with \(t=|T|\) between one and four. Then \(\operatorname{supp}(s^2+s+1)\subseteq T\) for every ordinary prime \(s\).

## Small ordinary primes and distinguished primes

Set \(X=1000\), \(Y=10000\). The verifier factors \(s^2+s+1\) for primes \(5\bmod6\) up to \(Y\), discarding support sets of size greater than four. Let \(U\) be the union of the support sets of the actual ordinary primes at most \(X\). Generate all possible unions by adding one support set at a time and discarding unions of size greater than four, or of size four with no element \(1\bmod12\). These restrictions are inherited by all subsets of a feasible union. The verifier counts 86 small roots, 525 medium roots, and 22,851 candidate unions (including the empty set).

For a candidate \(U\) and \(t\ge |U|\), consider first each fixed Euler prime in \(U\), and, if \(t>|U|\), the first four primes \(1\bmod12\) outside \(U\) as surrogate choices for Euler prime outside \(U\). If the actual Euler prime is not among the first four, at least one surrogate is not a fixed notable prime nor any other distinguished prime: there are only three others. Replacing the actual Euler upper factor \(P/(P-1)\) by the surrogate's larger factor preserves the upper bound. The surrogate is used only numerically; the medium calculation needs only whether \(P\in U\), not the value of an outside Euler prime. Now fill the remaining \(1\bmod3\) distinguished slots with the smallest available primes in that residue class, since \(r/(r-1)\) decreases in \(r\). These cannot overlap any ordinary prime.

Let \(A\) consist of all small roots \(s\) whose support is contained in \(U\), not just actual ordinary primes. Include every exact squared-component factor \((s^2+s+1)/s^2\) in a provisional product. The \(4-t\) distinguished slots in residue two mod three can overlap \(A\). If such a slot uses \(s\in A\), use an additional gain of \(s^3/(s^3-1)\), so the resulting factor is exactly \(s/(s-1)\), rather than double counting. If its prime \(s\notin A\), the gain is \(s/(s-1)\). To maximize the product upper bound choose the \(4-t\) largest gains among the first \(|A|+3\) primes \(5\bmod6\). At least three of these primes are outside \(A\); each has greater gain than any later prime, since even a later in-set gain is at most its \(s/(s-1)\). This constructs the rational baseline \(B\). It bounds the joint contribution of all distinguished and all actual ordinary primes up to \(X\).

## Large-prime tail

For a cutoff \(Z\), the logarithmic contribution of ordinary primes \(s>Z\) is bounded in terms of \(t\) only. Write \(m_i\) for the \(i\)-th smallest prime congruent to one mod three: \(7,13,19,31\). A nonzero vector of exponents \(\alpha\in\mathbb N^t\) in \(T\) determines at most one root \(s\) by strict monotonicity of \(s^2+s+1\). Its log-factor is at most
\[
 \frac{1}{\max\{Z-1,\lfloor\sqrt{\prod_{i=1}^{t}m_i^{\alpha_i}}\rfloor-2\}},
\]
since \(\log(s/(s-1))\le 1/(s-1)\) and \((s+1)^2>s^2+s+1\). Sum the terms with total degree at most \(20\) by rounding each upward to multiples of \(10^{-9}\). For degree \(k\ge21\) the sum is bounded by \(2\binom{k+t-1}{t-1}(2/5)^k\), from \(s-1>\sqrt{7^k}-2\). Successive such terms have ratio at most \(1/2\), so scaling and rounding \(4\binom{20+t}{t-1}(2/5)^{21}\) bounds the unsummed tail. The resulting convenient rational upper bounds, indexed by \(t=1,2,3,4\), are
\[
 L_X=(.008,.033,.086,.173),\qquad
 L_Y=(.001,.006,.017,.039).
\]
All displayed decimals denote exact rationals.

## Medium roots by outside support

If \(B<2(1-L_X)\), the case is closed because \(e^z\le 1/(1-z)\) for \(0\le z<1\). Exactly 48 cases survive this test, two with \(t=3\) and 46 with \(t=4\).

For a medium root \(X<s\le Y\) let \(V\) be its support. Discard it if \(|V\setminus U|>t-|U|\). If equality holds and Euler lies outside \(U\), require that \(V\setminus U\) contain some prime \(1\bmod12\), because then \(U\cup V\) must exhaust \(T\), including the Euler prime. Assign each remaining root a log-factor upper bound by rounding \(1/(s-1)\) upward to multiples of \(10^{-9}\). Group these bounds by the least prime of \(V\setminus U\), assigning the empty difference to a separate group. Every ordinary medium root with nonempty difference belongs to one of at most \(t-|U|\) groups indexed by primes of \(T\setminus U\). The empty group plus the \(t-|U|\) largest remaining group sums is therefore a valid upper bound \(D\) for the medium log-contribution, without guessing the missing target primes.

For all 48 survivors the attached verifier proves the exact rational inequality
\[
 \sigma(N)/N \ \le B/(1-D-L_Y) <197/100<2.
\]
All other cases closed by the initial test. This contradicts \(\sigma(N)=2N\).
