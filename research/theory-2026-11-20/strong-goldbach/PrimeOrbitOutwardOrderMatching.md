# A pointwise outward prime-factor matching at centres with a large fixed-prime power

Let \(N\) be even, let \(l\) be any fixed prime, and write \(a=v_l(N)>0\), \(L=\log(3+\log N)\), \(T=\log(a/L)\). Our asymptotic hypothesis is **\(T\to\infty\)**. For a unit \(z\bmod l^a\), write \(\lambda(z)\) for the \(l\)-adic valuation of the order of its image in \((\mathbb Z/l^a)^\times/\{\pm1\}\). A factor edge \(x\to q\) has multiplicity \(e=v_q(N-x)\); its order contribution means \(\lambda(q^e)\), not just \(\lambda(q)\). The statements are unconditional at the indicated centres and use the actual prime factorization of each row.

**Outward matching.** Fix \(0<\delta<1/2\). The following two conclusions hold for each sufficiently large centre in the stated regime, uniformly in the seed:
1. Put \(y=(1-\delta)T\). For **every** odd prime \(x\le y\) coprime to \(N\), there is a prime \(q>y\) dividing \(N-x\) with \(\lambda(q^{v_q(N-x)})\ge(1-o(1))a\).
2. For the much larger \(Y=\exp(\exp(T^{1/2-\delta}))\), the same conclusion with \(Y\) in place of \(y\) holds for every odd unit prime \(x\le Y\) except a set of size \(O_\delta(\pi(Y)T^{-\delta/2})\). In either assertion the selected prime factors are **distinct for different inputs**: \(q\) exceeds the entire seed interval and \(N\bmod q=x\).

Nonunit seeds are not counted as successes. For the second assertion a general lower bound for the size of the matching is \(\pi(Y)-1-\omega(N)-O_\delta(\pi(Y)T^{-\delta/2})\), possibly vacuous when \(a\) grows too slowly. For \(N=2^a\), or more generally \(a\ge(\log N)^\epsilon\) for a fixed \(\epsilon>0\), it is \((1-o(1))\pi(Y)\). There \(Y\) exceeds every fixed power of \(\log N\) but remains \(N^{o(1)}\). The factors' individual signed orders have \(l\)-part at least \(l^{(1-o(1))a}\), even after taking their actual edge multiplicities into account.

**Fixed taboo and simple paths.** Fix a finite set \(S\) of primes containing a fixed odd seed \(x_0\nmid N\). Even without taking \(T\to\infty\), when \(a>C_{l,S}L\) there is a factor \(q\notin S\) of \(N-x_0\) with \(\lambda(q^{v_q(N-x_0)})\ge a-C_{l,S}L\) (large \(N\)). Further, fix \(m\ge2\) and \(0<\beta<1/(m-1)\). In the regime \(T\to\infty\) there is a simple path starting at \(x_0\), with subsequent labels outside \(S\), all its edge contributions satisfying \(\lambda(q^e)\ge(1-o(1))a\), and ending in one of the following ways:
* it has already reached a prime \(x\) with \(N-x\) prime;
* it has made \(m\) distinct-vertex steps;
* in at most \(m\) steps it has reached a prime \(q\ge\exp((a/L)^\beta)\).

Here \(m,\beta,S,l\) are fixed before varying \(N\); the path is one actual directed path, not a count in the whole forward closure. In the dyadic case the third scale is \(\exp((\log N/\log\log N)^\beta O_{l,\beta}(1))\), not claimed to be a fixed power of \(N\).

## Local escape with all logarithmic heights displayed

For any finite prime set \(U\) containing the unit input \(x\), put \(N-x=P V\), \(P=\prod_{r\in U} r^{v_r(N-x)}\). The prime \(x\) does not divide \(P\), and no prime dividing \(N\) divides \(PV\). The rational \(u=x/P>0\) is not 1 by unique factorization. Put \(h=2\) if \(l=2\) and \(h=l-1\) otherwise. Then \(V^h\equiv u^h\bmod l^a\). To estimate \(v_l(u^h-1)\), use [K. Yu, *p-adic logarithmic forms and group varieties II*, Acta Arith. 89 (1999), 337–378, Theorem 1 and its displayed consequence on p. 337](https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8944.pdf), [DOI](https://doi.org/10.4064/aa-89-4-337-378), [alternate full text](https://bibliotekanauki.pl/articles/1390501.pdf). Only this ordinary, unnormalized bound is required; no strengthened coefficient hypothesis is being assumed.

Specifically let \(D=\{x\}\cup\{r\in U:r\mid P\}\), \(s=|D|\). The bases are these distinct rational primes (all \(l\)-units), exponents \(h\) on \(x\) and \(-h v_r(P)\) on the others, all bounded absolutely by \(O_l(1+\log N)\). The form is nonzero. Take \(K=\mathbb Q(\zeta_3)\) at 2 or \(\mathbb Q(i)\) at odd \(l\); these satisfy Yu (1.2), degree 2, unramified at the selected place, residue degree at most 2, with valuation restricting to \(v_l\). His p. 337 bound therefore gives
\[
 v_l(u^h-1)\ \le L\, C_l(s)\prod_{r\in D}\max(\log r,\log l),\qquad
 \log C_l(s)\le (s+1)\log(s+1)+O_l(s+1).                 \tag{1}
\]
Indeed the dimension factor displayed there is \((20\sqrt{s+1}\,[K:\mathbb Q])^{2(s+1)}\), times a logarithmic factor and constants polynomial or fixed in \(l\); absorb the harmless absolute factor in \(\log B\ll_l L\) in \(C_l\). In particular this is uniform for moving labels, but the **product** of all their heights must be retained. Denote the right side by \(E\).

If \(E<a\), then \(v_l(V^h-1)=v_l(u^h-1)=v<a\), and \(V>1\). For odd \(l\), the \(l\)-part of the order of \(V\) modulo \(l^a\) is \(l^{a-v}\) by the elementary lifting-the-exponent identity applied to \(V^{l-1}\equiv1\bmod l\). Taking the quotient by signs does not change this part. For \(l=2\), \(v=v_2(V^2-1)\ge3\); one of \(V\pm1\) has valuation 1 and the other \(v-1\). The representative of its sign class that is 1 modulo 4 has order \(2^{a-v+1}\) when \(v<a\), by the same elementary power valuation. Thus in either case \(\lambda(V)\ge a-v\). Since the order of a product in an abelian group divides the lcm of the factor orders, some \(q^e\parallel V\) has
\[
 q\notin U,\qquad \lambda(q^e)=\max(0,\lambda(q)-v_l(e))\ge a-E.       \tag{2}
\]
All can be read as bounds on integer orders (with the evident real-to-integer rounding). This proves the fixed-\(S\) assertion directly.

For the simple path apply (1)–(2) at \(x_i\) to \(U=S\cup\{x_1,\ldots,x_i\}\). If no previous stopping alternative occurred, \(i\le m-1\), and every moving label has log less than \((a/L)^\beta\). Hence \(E\ll_{l,S,m} L(a/L)^{(m-1)\beta}=o(a)\); the omitted factors of fixed or absent primes can only alter the constant. The next edge goes outside all visited vertices. Inputs \(<N-1\) are automatic while complements are composite: their prime factors are at most \((N-3)/3\); one stops if the complement is prime. This proves the path statement by induction.

## From single escape to an outward matching

For all seeds put \(U=\{r:r\le y,\ r\text{ prime}\}\). By the prime number theorem \(s\le\pi(y)=(1+o(1))y/\log y\), so
\[
 \log(E/L)\le (s+1)\log(s+1)+O_l(s+1)+s\log\max(\log y,\log l)
 \le (1+o(1))y .
\]
With \(y=(1-\delta)T\) this gives \(E/a=o(1)\). This proves the all-seed claim.

For the almost-all claim we need the following **pointwise** support bound, uniform in \(N\), where \(Z\to\infty\):
\[
 \sum_{\substack{x\le Z\\ x\ {\rm prime},\ (x,N)=1}}
 \#\{r\le Z:r\text{ prime},\ r\mid N-x\}
 \ \ll\ \pi(Z)\log\log Z.                                      \tag{3}
\]
For \(r\mid N\) there are no contributions. For \(r\le\sqrt Z,\ (r,N)=1\), the Brun–Titchmarsh bound for the reduced class \(N\bmod r\) is \(\ll Z/(r\log Z)\) and the prime reciprocal sum is \(O(\log\log Z)\). For \(\sqrt Z<r\le Z/2\), split into \(Z/2^{j+1}<r\le Z/2^j\), \(j\ge1\); the reciprocal mass of each (possibly cut) band is \(O(1/\log Z)\) by the elementary prime-count upper bound, and \(\log(Z/r)\ge j\log2\). Brun–Titchmarsh gives in all \(O((Z/\log Z)\sum_{j\ll\log Z}1/j)\). For \(Z/2<r\le Z\) there are at most two inputs in the given residue class. This proves (3). See [Montgomery–Vaughan, *The large sieve*, Theorem 2](https://doi.org/10.1112/S0025579300004708) for the uniform Brun–Titchmarsh inequality.

Use (3) at \(Z=Y\). With \(U\) now all primes up to \(Y\), outside \(O(\pi(Y)T^{-\delta/2})\) unit inputs the number \(s\) is at most \(1+(\log\log Y)T^{\delta/2}\) by Markov's inequality. Therefore (1) gives
\[
 \log(E/L)\ll_l s\,\big(\log(2s)+\log\log Y+1\big)
      \ll_{l,\delta} 1+T^{\,1-3\delta/2}=o(T).
\]
This gives \(E/a=o(1)\), uniformly for these inputs; (2) proves the matching. If \(a\ge(\log N)^\epsilon\), then \(T\ge(\epsilon+o(1))\log\log N\), so \(Y\gg(\log N)^K\) for every fixed \(K\) and \(\omega(N)\ll\log N=o(\pi(Y))\).

## What has and has not escaped

A single binary character can get stuck for ever even at a represented dyadic centre where the full orbit does reach a genuine pair. For example, at \(N=131072=2^{17}\) take the even character \((2/\cdot)\) and the negative seed 3. Since \(N-3=53\cdot2473\) and \(N-53=3\cdot7\cdot17\cdot367\), the negative odd-multiplicity edges from 3 and 53 give only the cycle \(3\leftrightarrow53\): 2473, 7, 17 and 367 are \(1\) or \(7\bmod8\). But \(3\to2473\) is an actual edge and \(131072-2473=128599\) is prime. Even multiplicities can matter too: \(248-3=5\cdot7^2,\ 248-5=3^5,\ 248-7=241\) prime, so from 3 the same single-character restriction misses the route via 7. These examples can be checked by trial division up to the integer square roots. The theorem permits a small *relative* loss of high-order bits in order to escape a finite taboo; it does not guarantee a path of full maximal order, or that a genuine pair is reached in general.

[The prior dyadic rank theorem](PrimeOrbitDyadicRank.md) uses Yu on row-space minors in a whole closed set and concludes independence or many closure labels. [The general Smith condition](PrimeOrbitCyclicSmith.md) constrains feedback sets and the group generated by cyclic components. Neither asserts a single outward factor of high order, the injective matching of actual factors at prescribed inputs, or the simple-path alternative above. The divisor graph itself is due to [Bożek](https://arxiv.org/abs/1909.09900); this note makes no priority claim about the underlying logarithm or sieve estimates.