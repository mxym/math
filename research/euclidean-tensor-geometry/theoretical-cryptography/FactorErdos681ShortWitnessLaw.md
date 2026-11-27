# Many nearby rough composites, with a stretched-exponential exceptional set

For \(a>1\) an integer, write \(p^-(a)\) for its least prime factor. The [question posed by Erdős, p. 74](https://static.renyi.hu/~p_erdos/1979-23.pdf), recorded as [#681](https://www.erdosproblems.com/forum/thread/681?embed=1), asks if every sufficiently large \(n\) has some \(k\ge1\) with \(n+k\) composite and \(p^-(n+k)>k^2\). Erdős also asked there about replacing \(2\) by other exponents. The all-start question is not settled here. Taking \(k=1\) works whenever \(n+1\) is composite, so a density-one statement at an unspecified shift would be trivial. The result below takes an explicitly growing shift range and supplies many certified composites even for almost all prime predecessors.

## Results

**Theorem.** Fix \(d>1\) and \(0<\eta<1/2\). There are positive constants \(\kappa,c_0,c_1,C\), depending only on \(d,\eta\), such that for all sufficiently large \(X\) and integers \(K\) satisfying
\[
 K_0(d,\eta)\le K\le\kappa\log X,
\]
all but at most
\[
 C X\exp\left(-c_1 K^\eta/(\log K)^2\right)
 \tag{1}
\]
integers \(n\in[X,2X)\) have at least \(c_0K/\log K\) distinct integer shifts \(K/2<k\le K\) such that:
- every prime factor of \(n+k\) exceeds \(K^d\);
- at least one prime factor of \(n+k\) is at most \(K^{d+1}\).

In particular these values \(n+k\) are composite, since \(K^{d+1}<X\) in this range; their least prime factors exceed \(k^d\). The choices \(d=2\) and \(K=\lfloor\kappa\log X\rfloor\) give an exceptional count \(O(X\exp(-c(\log X)^\delta))\) for any fixed \(0<\delta<1/2\), by taking \(\eta>\delta\). Since this count is \(o(X/\log X)\), the same result holds for all but a vanishing fraction of the starts \(n=p-1\) with \(p\) prime. The version with \(K\) about \(\sqrt{\log X}\) instead gives any \(\delta<1/4\). In particular choosing \(K=\lfloor(\log\log X)^{2+\varepsilon}\rfloor\), for any fixed \(\varepsilon>0\) and \(\eta>1/(2+\varepsilon)\), still gives an error \(o(X/\log X)\).

**Prime-predecessor version.** For \(K_0\le K\le\log\log X\), the same two-factor conclusion holds with exceptional count at most
\[
 C\frac{X}{\log X}\exp\left(-c_1 K^\eta/(\log K)^2\right)
 \tag{1'}
\]
among the \(n\in[X,2X)\) for which \(n+1\) is prime. In particular \(K\) may tend to infinity arbitrarily slowly, so this gives a nontrivial density-one statement *inside* the prime predecessors even when (1) is too weak to divide by their density.

**Worst-case comparison.** For every fixed \(d\ge1\) and \(c<1/5\), there exist arbitrarily large \(n\) for which none of \(1\le k\le c\log n\) gives a composite \(n+k\) with \(p^-(n+k)>k^d\). Thus one cannot replace the eventual existence question by a uniform \(o(\log n)\) cutoff.

**Literature and scope.** [Gafni–Tao, *Rough numbers between consecutive primes*](https://arxiv.org/abs/2508.06463) gives strong almost-all results inside successive prime gaps for the related #682; in particular their Theorem 1.1, Lemmas 2.1 and 3.1, and Remark 2.1 are pertinent. Here the ranges are prescribed for *any starting integer*, the exception estimate is stretched exponential for \(K\) near \(\log X\), and an additional factor proves compositeness without counting how often the outputs themselves are prime. The companion [long-window estimate](FactorErdos681RoughCompositeExceptions.md) in this repository uses related growing-order sieve comparison at \(K=(\log X)^B\), \(B>2\), and gives a stronger exception exponent there. This note concerns the shorter range down to arbitrary slowly growing \(K\) on prime predecessors, the associated first-witness limit law, and the logarithmic worst-case obstruction. This does not assert that the witnesses lie inside the prime gap following \(n+1\), does not sharpen #682's maximal or exceptional prime-gap assertions, and does not prove #681 for all sufficiently large starting integers. The inputs are the classical dimension-one lower sieve, Mertens and the prime number theorem, and a bounded-differences inequality.

## 1. Freezing small primes

Put \(z=K^\eta\), \(I=(K/2,K]\cap\mathbb Z\), and \(Q=\prod_{p\le K}p\). The prime number theorem gives \(Q\le \exp(2K)\) for large \(K\). First consider a **uniform residue** \(a\bmod Q\), giving independent uniform choices for \(a\bmod p\) for \(p\le K\). Let
\[
 I_z(a)=\{k\in I:p\nmid a+k\text{ for every }p\le z\}.
\]
Uniformly for all choices of residues at \(p\le z\), there are at least \(c_\eta K/\log K\) elements of \(I_z(a)\). Here is the dimension-one sieve application: for every squarefree \(\ell\) made of primes at most \(z\), the congruences \(\ell\mid a+k\) cut out exactly one class of \(k\bmod\ell\); the count in \(I\) is \(|I|/\ell+O(1)\). Use the lower linear sieve with bounded weights, level \(D=K^\gamma\) for fixed \(2\eta<\gamma<1\), local density \(1/p\), and \(s=\log D/\log z=\gamma/\eta>2\). Mertens verifies the dimension-one product hypothesis and \(\prod_{p\le z}(1-1/p)\asymp_\eta1/\log K\); the standard lower sieve function \(f(s)>0\) for \(s>2\), and total remainder \(O(D)=o(K/\log K)\). For a published statement of the weights and main-term estimate see [Wu, Lemma 3.1](https://doi.org/10.1017/S144678871800023X), citing the original [Rosser–Iwaniec sieve](https://www.impan.pl/shop/publication/transaction/download/product/102606).

Fix the residues at \(p\le z\). Expose the independent residues at \(z<p\le K\), and let \(R\) be the number of elements of \(I_z(a)\) surviving those primes. Its conditional mean is
\[
 |I_z(a)|\prod_{z<p\le K}(1-1/p)\ \gg_\eta\ K/\log K
\]
because the product tends to \(\eta\). Changing one residue class for a prime \(p\) changes \(R\) by at most \(2(K/p+1)\). The sum of squares of these bounds is \(O(K^2/z)\): for \(p\le K\), compare \(1+K/p\) with \(2K/p\) and sum \(p^{-2}\) over all integers above \(z\). By [McDiarmid's inequality](https://doi.org/10.1017/CBO9781107359949.008), for a sufficiently small fixed \(b=b(\eta)>0\), the event \(R< r:=\lfloor bK/\log K\rfloor\) has probability
\[
 \ll_\eta\exp\left(-c_\eta K^\eta/(\log K)^2\right)
 \tag{2}
\]
under the uniform residue model, also after averaging over the small primes. Take \(K_0\) large enough that \(r\ge1\) and \(r\asymp_\eta K/\log K\). Call a class \(a\bmod Q\) *good* if \(R\ge r\); for a good class fix any \(r\) surviving offsets \(S\subset I\). The distribution of \(n\bmod Q\) for uniform \(n\in[X,2X)\cap\mathbb Z\) differs from the uniform law by \(O(Q/X)\) in total variation, by division with remainder. This will be negligible.

## 2. The large-prime occupancy model

Use the two disjoint ranges of primes
\[
 {\cal P}_2=\{K<p\le K^d\},\qquad {\cal P}_3=\{K^d<p\le K^{d+1}\}.
\]
In the artificial model, independently for each such \(p\) choose a uniform residue of \(n\bmod p\). Since the difference of any two offsets in \(S\) has absolute value less than \(p\), each \(p\) hits at most one offset by divisibility, and hits each specified offset with probability \(1/p\).

We will use the following two product inequalities for any one range. For any subset \(A\) of the offsets, the probability that **all** offsets of \(A\) are unhit is at most the product of their individual nonhit probabilities: the expression is \(\prod_p(1-|A|/p)\le\prod_p(1-1/p)^{|A|}\). For all offsets of \(A\) **hit**, the analogous upper product bound also holds. In fact, condition on one offset \(i\) being unhit. At each prime this independently removes just the outcome hitting \(i\). One can couple by resampling outcomes that previously hit \(i\), leaving all other draws unchanged. This can only increase the collection of hit offsets other than \(i\). Thus the conditional probability that all remaining offsets of \(A\) are hit is at least its unconditional value. By total probability, conditioning instead on \(i\) being hit can only decrease that probability. Multiplying by \(\Pr(i\text{ hit})\) and using induction yields the product inequality.

Either family of indicators \(W_k\) (all hit or all unhit, respectively) therefore obeys the corresponding independent Bernoulli *upper* Chernoff bound for its sum: for \(t\ge0\), expand \(\prod_k[1+(e^t-1)W_k]\) and bound each subset term by the product of marginals. In \({\cal P}_2\) the nonhit probability at each offset tends by Mertens to \(1/d\). Applying the bound to **hits**, with probability at least \(1-e^{-c_d r}\) at least \(c'_d r\) offsets are unhit in this range. Now condition on the surviving offsets. For \({\cal P}_3\), which is independent of the \({\cal P}_2\) choices, the probability of a hit at each specified offset tends to \(1/(d+1)\). Applying the bound to **nonhits** gives, except with probability \(O(e^{-c''_d r})\), at least \(c'''_d r\) offsets that are unhit in \({\cal P}_2\) and hit in \({\cal P}_3\).

## 3. Transferring the two-range result to actual integers

It is not valid here to take the full primorial up to \(K^{d+1}\) as a period and neglect it against \(X\). Instead, fix a good \(a\bmod Q\), and write a uniform integer in that class as \(n=a+Qt\), with \(t\) uniform in a consecutive interval of \(H_a\ge X/(2Q)\) integers. For each of the chosen \(r\) offsets there are two binary nonhit indicators, one for each large-prime range. We compare the distribution of these \(2r\) bits with the independent-prime model of Section 2 (the *bits themselves* are not independent there).

Take any subset of these bits. The event that all its bits equal \(1\) is an avoidance event: for each prime \(p\) in the two large ranges, avoid \(\nu_p\le r\) specified residues of \(t\bmod p\). We used \(p\nmid Q\) and distinctness of the offsets modulo \(p\). In the model the event has independent-prime probability \(\prod_p(1-\nu_p/p)\). For a set \(J\) of primes, the probability that **all** of their forbidden events occur for \(t\) in the consecutive interval is
\[
 \prod_{p\in J}\frac{\nu_p}{p}
       + O\left(\frac{\prod_{p\in J}\nu_p}{H_a}\right).
 \tag{3}
\]
Indeed the CRT gives exactly \(\prod_{p\in J}\nu_p\) distinct residue classes modulo \(\prod_{p\in J}p\), each with counting error at most one.

Take an even integer \(T\) nearest above \(A_d r\) for a sufficiently large constant \(A_d\). Bonferroni at orders \(T\) and \(T-1\) brackets the avoidance probability. In the model the gap between these brackets is at most
\[
 \sum_{|J|=T}\prod_{p\in J}\frac{\nu_p}{p}
 \le\frac{(\sum_p\nu_p/p)^T}{T!}
 \le e^{-20r},
 \tag{4}
\]
where \(\sum_p\nu_p/p\ll_d r\) by Mertens and \(T!\ge(T/e)^T\). The errors in both brackets in (3), summed over all terms through order \(T\), are bounded by
\[
 O\left(\frac{(T+1)K^{(d+3)T}}{H_a}\right)
 \tag{5}
\]
since the number of primes is at most \(K^{d+1}\) and \(\nu_p\le r\le K\). The numerator here is \(\exp(O_d(K))\), since \(T=O_d(K/\log K)\). Choose \(\kappa>0\) small enough that (5) is \(O(X^{-1/2})\) uniformly in \(a\) and \(K\) (use \(1/H_a\le 2e^{2K}/X\)). This is \(O(e^{-20r})\) for large \(X\), uniformly, since \(r=o(\log X)\). Equations (4)–(5) compare each all-ones moment with error \(O(e^{-20r})\), regardless of the chosen subset of bits.

For clarity on converting those moments to probabilities, for any binary vector with occupied set \(B\),
\[
 \Pr(B=A)=\sum_{J\subseteq [2r]\setminus A}(-1)^{|J|}\Pr(A\cup J\subseteq B).
\]
Summing the absolute errors over \(A\) thus costs at most \(3^{2r}\) times the largest moment error. The actual distribution of bits on the good class differs from the model by \(O(e^{-c r})\) in total variation for an absolute \(c>0\). This proves that the success count of Section 2 holds for all but an \(O(e^{-c_d r})\) fraction of the integers in each good class \(a\).

Finally combine (2), the \(O(Q/X)\) change in the distribution of residue classes, and the bound for good classes. With \(r\asymp_\eta K/\log K\) and \(K\le\kappa\log X\), both \(e^{-c_dr}\) and \(Q/X\) are absorbed by the right-hand rate in (1) after division by \(X\). Survivors have no factor \(p\le K\), no factor in \({\cal P}_2\), and a factor in \({\cal P}_3\) at most \(K^{d+1}<n+k\), so their compositeness and the claimed strict lower bound on prime factors both follow. This proves the theorem.

## 4. Conditioning on \(n+1\) prime

Here \(K\le\log\log X\). Let \(P_X\) denote uniform sampling among the integers \(n\in[X,2X)\) with \(n+1\) prime. Under this law \(n\bmod Q\) is close in total variation to a uniform class \(a\bmod Q\) with \(\gcd(a+1,Q)=1\): the [Siegel–Walfisz theorem](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf), Theorem 12.1, applies to \(n+1\) modulo \(Q\le e^{2K}\). The error is \(O(\varphi(Q)\log X\,e^{-c\sqrt{\log X}})\); a shift of the endpoints by one is absorbed. For such uniform classes the residues \(a\bmod p\) are independent and uniform with \(-1\) excluded. The dimension-one lower sieve of Section 1 still applies for every configuration up to \(z\). In its bounded-differences step, at a medium prime \(z<p\le K\) a given offset is removed with probability at most \(1/(p-1)\), rather than exactly \(1/p\). The conditional mean is still \(\gg_\eta K/\log K\), since \(\prod_{z<p\le K}(1-1/(p-1))\to\eta\); the differences bound is unchanged. Thus the same bad-class probability (2) applies.

For \(p>K\) and \(k\in I\) we have \(k\not\equiv1\bmod p\) when \(K\ge4\), so each forbidden class \(-k\bmod p\) leaves \(n+1\) a unit. Use the model where the large-prime residues are independent, uniform among the \(p-1\) classes other than \(-1\). The occupancy inequalities hold verbatim with \(p-1\) in place of \(p\), and Mertens gives the same two asymptotic marginal probabilities: the difference of reciprocal sums beyond \(K\) is \(O(1/K)\). To transfer, in (3), for each \(|J|\le T\) the modulus \(Q\prod_{p\in J}p\le \exp(O_d(K))\le(\log X)^{A_d'}\). Its \(\prod_{p\in J}\nu_p\) relevant classes of \(n+1\) are reduced. Apply Siegel–Walfisz to each and normalize by the prime count in the fixed good class \(a+1\bmod Q\), which is \((1+o(1))(\operatorname{li}(2X)-\operatorname{li}(X))/\varphi(Q)\). The main term in (3) becomes \(\prod_{p\in J}\nu_p/(p-1)\), and its error is bounded by
\[
 O_d\left(\prod_{p\in J}\nu_p\ \varphi(Q)\log X\,e^{-c_d\sqrt{\log X}}\right).
\]
The error from this normalization is covered by the same bound; if a \(\nu_p\) is zero the term is simply zero. The bracket error from summing all such products is at most their former bound's numerator times \(O_d(\varphi(Q)\log X\,e^{-c_d\sqrt{\log X}})\), hence \(O(e^{-20r})\) since that numerator is \(\exp(O_d(K))\). The product tail and moment inversion now proceed as before. Multiplying the resulting exceptional probability by the number of prime starts \(O(X/\log X)\) proves (1').

**Limit law for the first shift on prime predecessors.** Fix \(d>1\). Let \(M_d(n)\) be the least \(k\ge1\) with \(n+k\) composite and \(p^-(n+k)>k^d\), or \(\infty\) if there is none. Take independent \(R_p\) uniform in \(\mathbb Z/p\mathbb Z\setminus\{-1\}\), and let \(M_d^\ast\) be the least \(k\ge2\) such that \(R_p+k\not\equiv0\bmod p\) for all \(p\le k^d\). As \(X\to\infty\), the law of \(M_d(n)\) under \(P_X\) converges in total variation to that of \(M_d^\ast\). Indeed, for fixed cutoff \(K\), the roughness conditions at \(2\le k\le K\) are decided by the residues up to \(K^d\), which approach the stated independent law by the prime number theorem in fixed progressions. The restriction to composites makes a difference of vanishing probability: for each fixed \(k\ge2\), the fraction of prime starts \(p=n+1\) where \(p+k-1\) is also prime tends to zero. To see this last fact, impose avoidance of \(-(k-1)\) on \(p\) modulo every prime \(\ell\le W\) with \(\ell\nmid k-1\), use the prime number theorem for their fixed product, then let \(W\to\infty\); the limiting upper bound \(\prod_{\ell\le W,\ \ell\nmid k-1}(1-1/(\ell-1))\) tends to zero, possibly already vanishing at \(\ell=2\). Thus the distribution functions converge at every fixed \(K\). By (1') their limiting tail satisfies
\[
 \Pr(M_d^\ast>K)\ll\exp(-c K^\eta/(\log K)^2).
\]
It follows both that the limit law has no mass at \(\infty\) and has all moments finite. Convergence on the finitely many atoms through \(K\), followed by this tightness bound, gives total variation convergence, with no assertion of moment convergence of \(M_d(n)\). For a complementary lower bound on the model tail, the event \(R_p=0\) for all \(p\le K\) occurs with probability \(1/\varphi(\prod_{p\le K}p)=\exp(-(1+o(1))K)\) and spoils all the shifts \(2\le k\le K\).

## 5. A logarithmic lower obstruction

For each integer \(J\) tending to infinity set \(Q_J=\prod_{p\le J}p\). By [the Linnik bound with exponent 5](https://doi.org/10.22405/2226-8383-2018-19-3-80-94), there is a prime \(P\equiv1\pmod {Q_J}\) with \(P\ll Q_J^5\). Put \(n=P-1\), which is at least \(Q_J\) and so tends to infinity. The shift \(k=1\) gives a prime. For \(2\le k\le J\), a prime divisor \(p\mid k\) also divides \(Q_J\) and hence \(n+k\); therefore \(p^-(n+k)\le p\le k\le k^d\). No shift through \(J\) works. By the prime number theorem, \(\log n\le5\log Q_J+O(1)=(5+o(1))J\), which gives the stated obstruction.

## Finite checks

Run `node verify_erdos681_rough_composites.js`. It checks both occupancy product inequalities on exact finite sample spaces, the CRT intersection and Bonferroni inequalities for arithmetic samples with genuine endpoint effects, and exact probability reconstruction from all-ones moments. These finite checks are not a substitute for the analytic estimates or an experiment with any actual cryptographic target.
