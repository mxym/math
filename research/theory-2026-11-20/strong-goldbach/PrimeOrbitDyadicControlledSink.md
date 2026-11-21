# Reachable Goldbach pairs with a controlled loss and recovery of dyadic order

Write \(x\longrightarrow y\) if the prime \(y\) divides \(N-x\). Its contribution is the entire prime power \(y^{v_y(N-x)}\). For \(a=v_2(N)\ge4\) use the signed local group \((\mathbb Z/2^a)^\times/\{\pm1\}\), of order \(2^{a-2}\). A contribution loses at most \(g\) bits if its signed order is at least \(2^{a-2-g}\).

**Theorem.** There is an absolute \(c>0\) such that for large \(X\) and every integer \(4\le a\le c\sqrt{\log X}\), each of the following lower bounds holds for the number of distinct \(N\in[X,2X]\) of exact dyadic depth \(a\):

* \(\gg X/(2^a(\log X)^{1/4})\) if at most **one bit** may be lost on the entire path;
* \(\gg X/2^a\) if at most \(g=\max(1,\lceil\log_2(\log\log X)\rceil)\) bits may be lost (here \(\log_2\) means logarithm to base two).

In both bounds there is a strictly increasing prime path from 3 through 7 to a genuine Goldbach pair \(Q,P=N-Q\), with \(X^{1/20}\le Q\le X^{1/12}\). Every chosen edge, including the final \(Q\longrightarrow P\), has contribution exponent **exactly one**. The first edge loses exactly one bit, the edge into \(Q\) restores full order if not already restored, and both \(Q,P\) have full order. All prior input complements are composite. The fraction in the first bound is of the indicated order, not just a lower bound, for the particular bounded-product path family constructed below. No such upper bound is asserted for unrestricted paths.

This allows a real order decrease and later visits a genuine prime complement. It neither asserts that those same paths occur on the specially constructed centers with an exact maximal-order trap, nor proves a pointwise or a density-one result.

## 1. Distribution input on a growing dyadic progression

There is \(c_0>0\) and, for each large \(X\), either \(B=1\) or a prime \(B\to\infty\), for which at each fixed \(u=X,3X/2\)
\[
 \sum_{\substack{D\le X^{1/5}\\(D,B)=1}}\max_{(b,D)=1}
 \left|\theta(u;D,b)-u/\varphi(D)\right|
       \ll X\exp(-c_0\sqrt{\log X}).                         \tag{1}
\]
Here \(\theta\) sums \(\log P\) over primes. We include the details of this classical exceptional-prime deletion to distinguish the scale in (1) from ordinary logarithmic-error Bombieri–Vinogradov. [Ford–Green–Konyagin–Maynard–Tao, *Long gaps between primes*, Corollary 6 and (7.2)](https://ford126.web.illinois.edu/wwwpapers/primegaps2.pdf) give such \(B\) and a fixed \(\kappa>0\) so that for \(1<d<\exp(2\kappa\sqrt{\log X})\) coprime to \(B\) the primitive-character sum of \(|\psi(u,\chi)|/\varphi(d)\) is \(O(X e^{-3\kappa\sqrt{\log X}})\) at our two endpoints. Corollary 6 gives \(B\gg\log\log(\exp(c_1\sqrt{\log X}))\) unless \(B=1\). Passage from characters modulo \(D\) to their conductors costs \(O(\log D\log X)\) per modulus after division by \(\varphi(D)\); the prime-power contribution in passing from \(\psi\) to \(\theta\) is \(O(\sqrt X\log^2 X)\) per modulus. The principal contribution follows by the classical prime number theorem with its zero-free-region error. Interchange the conductor and modulus sums and use \(\sum_{d\mid D,\,D\le X^{1/5}}1/\varphi(D)\ll(\log X)/\varphi(d)\), by \(\varphi(dj)\ge\varphi(d)\varphi(j)\). The sum over \(1<d\le R=\exp(\kappa\sqrt{\log X})\) thus costs \(O(R X e^{-3\kappa\sqrt{\log X}}\log X)\).

For the remaining dyadic intervals \(U<d\le2U\), \(R/2\le U\le X^{1/5}\), [Sedunova, Proposition 1.6](https://www.numdam.org/item/PMB_2018____101_0.pdf) bounds the sum of the primitive absolute character sums divided by \(\varphi(d)\) by
\[
 \ll (\log X)^{5/2}(X/U+U X^{1/2}+U^{1/2}X^{2/3}+X^{5/6}).
\]
Sum the intervals and absorb logarithms. This proves (1) with a possibly smaller \(c_0\). It is not necessary to know \(B\). Set \(m=3\cdot49\cdot2^{a+1}\). Take the absolute constant \(c>0\) in the theorem sufficiently small that \(m<\exp((c_0/3)\sqrt{\log X})\). For large \(X\), \(B=1\) or \(B\nmid m\).

## 2. Actual paths, mass and absence of square divisors

Impose \(N=2^a\bmod 2^{a+1}\), \(N=10\bmod49\) and \(N=1\bmod3\). Thus \(v_7(N-3)=1\). Put \(\gamma=1/1000,\ \alpha=1/20,\ \beta=1/12,\ Y=X^\gamma\). Use terminal primes \(X^\alpha\le Q\le X^\beta\) with \(Q=3\bmod8,\ Q=1\bmod7,\ Q=2\bmod3,\ Q\ne B\). Both \(Q\) and the prospective \(P=N-Q\) are then units modulo \(m\). This is only one **fixed** progression for \(Q\) (modulo 168); no sparsity factor depending on \(a\) occurs.

Fix a sufficiently large absolute cutoff \(U_0>7\). In the one-bit case let \({\cal A}\) consist of primes \(\ell>U_0,\ \ell\ne B,\ \ell\not\equiv\pm1\bmod16\). In the growing-budget case replace 16 by \(2^{g+3}\). Write \(E(y)=\prod_{\ell\le y,\,\ell\in{\cal A}}(1+1/\ell)\). For each squarefree \(s\le Y\) made from \({\cal A}\), list its primes in increasing order after 7, then append \(Q\). At every listed target \(\ell\) impose \(N=x_\ell\bmod\ell\), where \(x_\ell\) is its predecessor. The path is strict and its labels are units since \(0<x_\ell<\ell\). For each \(\ell\mid s\), discard the path if \(Q=x_\ell\bmod\ell\); these are precisely the remaining failures of reduction for the prime class \(P=N-Q\bmod m sQ\).

Uniformly in \({\cal A}\), the squarefree harmonic mass before this discard satisfies \(\sum_{s\le Y}1/s\asymp E(Y)\): in the product truncated at \(Y^{1/10}\), the mean logarithm of the product is at most \(\sum_{\ell\le Y^{1/10}}\log(\ell)/(\ell+1)\le \tfrac1{10}\log Y+O(1)\), so Markov keeps a fixed proportion below \(Y\). The product from \(Y^{1/10}\) to \(Y\) is bounded absolutely by Mertens. The reciprocal sum of the chosen \(Q\)'s is bounded below by a positive constant by the prime number theorem in the fixed progression (discarding the possible \(B\) costs \(O(X^{-\alpha})\)). Brun–Titchmarsh and partial summation show \(\sum_{Q=x_\ell\bmod\ell}1/Q\ll1/(\ell-1)\) per fixed \(s,\ell\mid s\), even ignoring the fixed progression, since \(\gamma<\alpha\). Thus removed pair mass is at most
\[
 C E(Y)\sum_{\ell>U_0}1/(\ell(\ell-1)).
\]
Take \(U_0\) large. The admissible pair mass \(\sum_{s,Q}1/(sQ)\) is now \(\asymp E(Y)\) with absolute lower constant independent of \(U_0\) and of the chosen sets of intermediate primes. Also \(\sum_s1/\varphi(s)\le C E(Y)\): the ratio of the two untruncated Euler products is bounded by \(\prod_{\ell>2}(1+O(1/\ell^2))\).

Count \(P\in[X,3X/2]\) in the forced prime class modulo \(m sQ\), with weight \(\log P\). Each modulus occurs only once since \(Q>Y\). Formula (1) gives lower main term \(\gg (X/m)E(Y)\) with an \(O(Xe^{-c_0\sqrt{\log X}})\) total error, and the same order upper bound since \(m/\varphi(m)\) is bounded absolutely.

We can simultaneously discard **every** path for which any target \(\ell\mid sQ\) has \(\ell^2\mid N-x_\ell\). Each marked event lifts the existing forced class to one class modulo \(m sQ\ell\); its prime class remains reduced. These marked moduli are all distinct: outside \(m\), the unique squared prime specifies the mark, and the largest prime specifies \(Q\). Their size is at most \(mX^{\gamma+2\beta}<X^{1/5}\). Consequently (1) again bounds their combined error, rather than multiplying an error by the number of labels. Their total main weight is
\[
 \ll (X/m)E(Y)\left(\sum_{\ell>U_0}1/(\ell(\ell-1))+X^{-\alpha}\right).
\]
Indeed the extra modulus factor costs \(1/\ell\); for an interior mark the reciprocal-\(\varphi\) mass of products divisible by it costs a further \(1/(\ell-1)\). For mark \(Q\), use \(1/Q\le X^{-\alpha}\). Enlarging \(U_0\) once and taking \(X\) large suffices. No primality of \(N-x_\ell\) before reaching \(Q\) is assumed; in fact it is much larger than its forced prime factor. Let \(Z(N)\) count the surviving paths. Converting the weights (all \(\log P\asymp\log X\)) gives
\[
                 \sum_N Z(N)\asymp {X E(Y)\over m\log X}.       \tag{2}
\]

## 3. Distinct centers and order

For the one-bit case \({\cal A}\) has six of the eight odd classes modulo 16, hence \(\delta=3/4\), and Mertens in those fixed progressions gives \(E(Y)\asymp(\log X)^\delta\); removing one \(B\) changes this by a bounded factor. For completeness we sharpen the shared-prefix bound from [the fixed-seed path theorem](PrimeOrbitCommonGoldbachSink.md). At fixed \(N\) two increasing paths sharing any vertex share the entire prefix through it (the smaller predecessor is necessarily \(N\bmod\ell\)). Thus distinct paths have distinct terminal primes \(Q,Q'\). Write their interior products as \(sv^{-1}=s'w^{-1}=c'\), where \(c'\) is the product of the shared prefix after 7 and all extra prime factors in \(v,w\) exceed \(P^+(c')\), taken as 1 for empty prefix. The compatible joint congruence has modulus \(J=m c'vwQQ'\). For \(\Delta=|Q-Q'|\), \(F(j)=\prod_{\ell\mid j}(1+6/\ell)\), the count with both shifted numbers prime is
\[
                 \ll {X F(J\Delta)\over J\log^2 X}.
\]
This is the two-form large-sieve bound in §§2–3 of the linked theorem: the index interval has length \(X/J\gg X^{4/5}\), since \(2\gamma+2\beta<1/5\) and \(m=X^{o(1)}\); sift at \(\ell\nmid 2J\Delta\), where there are exactly two forbidden residues, and charge all removed factors in \(F\). Here \(F(m)\) is constant, independent of \(a\). The same proof there gives \(\sum_{Q\ne Q'}F(\Delta)/(QQ')\ll1\) even before the fixed congruence restriction. We may ignore the additional no-square requirements for this upper bound.

For each suffix use the restricted product
\[
 \prod_{\substack{t<\ell\le Y\\\ell\in{\cal A}}}(1+F(\ell)/\ell)
    \ll\left({\log(2Y)\over\log(2t)}\right)^\delta
       \quad(1\le t\le Y).
\]
It follows from Mertens in the fixed classes, with the fully unrestricted six-class product as an upper bound over any interval. The common prefix costs
\[
 \sum_{c'}{F(c')\over c'\log^{2\delta}(2P^+(c'))}\ll1:
\]
the \(c'\) with largest prime \(\ell\) cost at most \(C(\log(2\ell))^\delta/\ell\) before division, and \(\sum_\ell1/(\ell\log^\delta(2\ell))\) converges. This proves
\[
 \sum_N Z(N)(Z(N)-1)\ll (X/m)(\log X)^{2\delta-2}.
\]
It is \(o(\sum_N Z(N))\) by (2). The first claim (and the matching order of magnitude for this path family) follows by the elementary first two Bonferroni bounds.

For the growing budget the unrestricted version of the same pair argument, with the unrestricted prime set and \(\delta=1\) just for this upper bound, gives \(\sum_N Z(N)^2\ll X/m\) including the diagonal. To get the corresponding lower bound in (2), set \(D=2^{g+3}\asymp\log\log X\). The primes removed in the two classes \(\pm1\bmod D\) have reciprocal mass \(O(1)\): up to \(D^2\) sum the two elementary progressions starting at \(D-1\) for \(O(\log(2D)/D)\), and from \(D^2\) to \(Y\) apply Brun–Titchmarsh and partial summation to get \(O((1+\log\log Y)/\varphi(D))\). Thus \(E(Y)\gg\log Y\) by Mertens, with \(U_0\) fixed. Cauchy–Schwarz proves the second claim.

Finally, choose the sign of any odd label \(y\) so \(y^*=\pm y\equiv1\bmod4\). If \(v=v_2(y^*-1)\), its signed order modulo \(2^a\) is \(2^{\max(0,a-v)}\), by elementary lifting the exponent. The intermediate exclusion \(\ell\not\equiv\pm1\bmod 2^{g+3}\) gives \(v\le g+2\), with \(g=1\) in the first case. The signs for \(3,7\) give \(v=2,3\), respectively; \(Q=3\bmod8\) has \(v=2\), and \(P=-Q\bmod8\) has \(v=2\). All contributions have exponent one by construction. The estimates count centers with these full directed trajectories, not just congruence incidences of endpoints.