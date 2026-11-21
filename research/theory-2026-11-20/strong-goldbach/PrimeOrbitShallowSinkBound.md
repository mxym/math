# A genuine Goldbach endpoint is rarely within two factor steps of a small seed

For even \(X\le N\le2X\) put a directed edge \(u\to v\) between odd unit primes if \(v\mid N-u\), with labels \(<N\). A genuine endpoint is a prime \(r\) with \(N-r\) prime. Distance is the number of factor edges to the *first endpoint*, not the extra step to the opposite member of the prime pair. Let \(L=\log\log X\).

**Theorem.** Uniformly for odd primes \(p\le\log X\), the number of even \(N\in[X,2X]\), \(p\nmid N\), having a genuine endpoint at distance at most two from \(p\) is
\[
 \ll X\, L^{3/4}(\log X)^{-1/4}.
\]
Consequently, outside \(O(X/L^{1/4})\) centres, **no** odd unit prime \(p\le(\log X)^{1/4}\) reaches any genuine endpoint in two or fewer factor steps.

The positive-proportion accessible-sinks theorem in [the dominant core note](PrimeOrbitDominantCore.md) is compatible with and complementary to this: on a positive proportion of its admissible centres, a fixed seed reaches a growing number of genuine prime pairs, but none is reached in the first two steps, even from any of the above small unit seeds. This concerns distance among actual represented centres, not an obstruction to longer paths, a Goldbach counterexample or a lower bound on the number of unrestricted exceptions. A positive proportion in any fixed admissible progression with a common reachable sink as in [the common-sink note](PrimeOrbitCommonGoldbachSink.md) can likewise be intersected with the simultaneous density-one conclusion.

## Uniform short sieve

For \(1\le d\le3\) integer affine forms \(A_i n+B_i\) on an interval of length at most \(H\), take
\(\Delta=\left|\prod A_i\prod_{i<j}(A_i B_j-A_j B_i)\right|\ne0\).
If \(H\gg1,\ H\le 10X,\ \Delta\ll X^{O(1)}\) (absolute constants), the count with all form values primes \(>H^{c_d}\), for a sufficiently small fixed \(c_d>0\), is
\[
  \ll_d H\left({L\over\log H}\right)^d. \tag{1}
\]
Use the arithmetic large sieve in Montgomery and Vaughan, *The large sieve*, Corollary 1 ([original article](https://doi.org/10.1112/S0025579300004708), [author PDF](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)). At primes \(d<\ell\le H^{c_d}\) outside \(\Delta\) the forms remove \(d\) distinct residue classes. In the squarefree denominator with weights \(w_\ell=d/(\ell-d)\), truncate the Euler product at squarefree integers \(h\le\sqrt H\). Under the product probability, \(\mathbb E\log h=\sum(d/\ell)\log\ell\ll_d c_d\log H\), so taking \(c_d<1/10\) sufficiently small keeps at least half the full mass. That mass is \(\prod(1-d/\ell)^{-1}\gg_d(\log H)^d/\prod_{\ell\mid\Delta}(1-1/\ell)^{-d}\), using Mertens and the convergent higher-order corrections (ignore finitely many small primes). The excluded product is \(\ll_d L^d\): split at \(\log(3+\Delta)\), and use Mertens below the split and the bound on the number of distinct divisors above it. The numerator of the sieve is \(O(H)\). No assumption on reduced forms at primes dividing \(\Delta\) is needed.

## Distance zero and one

Distance zero costs \(O(X/\log X)\) by the prime count. Write \(N=p+a q\) for an edge to \(q\). The case \(a=1\) is distance zero, and \(q=p\) cannot occur since \(p\nmid N\); otherwise \(a\ge3\) is odd. If \(q\le\sqrt{2X}\), fix \(q\) and sieve the one linear form \(N-q\) in its progression of length \(O(X/q)\). Its value is \(\gg X\). If \(q>\sqrt{2X}\), fix \(a\le\sqrt{2X}\) and sieve \(q,(a-1)q+p\), whose determinant is \(p\ne0\), in length \(O(X/a)\). Both primes sought are large. Summing the prime reciprocal \(q\)-sum \(O(L)\) or the integer harmonic \(a\)-sum \(O(\log X)\) bounds distance at most one by \(O(X L^2/\log X)\).

## Two steps: ignore a thin middle for the first divisor

Take \(p\to q\to r\) with \(P=N-r\) prime; put
\[
 N=p+a q=q+b r.
\]
If \(a=1\), \(b=1\) or \(r=p\) a shorter hit has occurred; hence take \(a,b\ge3\), both odd, and \(p,q,r\) pairwise distinct. In fact \(r=q\) would give \(q\mid N\) and then \(q=p\). In this nontrivial case \(q,r<N/3\) and \(P>2N/3\). Fix
\(\eta=(L^3/\log X)^{1/4}\). The centres with *any* prime divisor \(q\mid N-p\) in \([X^{1/2-\eta},X^{1/2+\eta}]\) cost \(O(\eta X)\), independently of \(p\): sum \(2X/q+1\) over the indicated primes and use Mertens with error \(O(1/\log X)\) for the reciprocal-sum difference, whose main term is \(\log((1/2+\eta)/(1/2-\eta))=O(\eta)\). The \(+1\) total is \(O(X^{1/2+\eta})\). This is an unweighted union over centres, not a bound on multiplicity of later paths.

In the remaining cases fix the small choice from the first split: \(q<X^{1/2-\eta}\), or else \(a\le2X^{1/2-\eta}\). For the second split, either \(r\le\sqrt{2X}\) or \(r>\sqrt{2X}\) and \(b<\sqrt{2X}\). The product of the two fixed variables is \(O(X^{1-\eta})\). Thus every upper-sieve interval length used below can be taken at least \(c X^\eta\) even if an actual dyadic subinterval is shorter. Parameterize over the full relaxed interval. All variable primes tested are \(>\sqrt{2X}\) or \(P>2N/3\) (and on the large-first side \(q>X^{1/2+\eta}\)); hence all exceed \(H^{c_d}\). All slopes and intercepts may be chosen \(O(X^{O(1)})\) by using least nonnegative residues, so the same holds for \(\Delta\). In the surviving cases with reduced progression unavailable there is no solution as detailed below.

* **Fix \(q,r\).** By CRT \(N\equiv p\bmod q,\ N\equiv q\bmod r\). The single prime form \(P=N-r\) has slope \(qr\) and an interval of length \(O(X/(qr))\).
* **Fix \(q,b\).** We have \(br\equiv p\bmod q\), whence \((b,q)=1\). Write \(r=r_0+q n\); sieve \(r,P=q+(b-1)r\) over length \(O(X/(qb))\). The two slopes are nonzero and their determinant has absolute value \(q^2\).
* **Fix \(a,r\).** We need \((a-1)q\equiv-p\bmod r\); since \(r\ne p\), \(r\nmid a-1\). With \(q=q_0+rn\) sieve \(q,P=p-r+a q\) over length \(O(X/(ar))\). The absolute determinant is \(r|p-r|>0\).
* **Fix \(a,b\).** Here \(b r=p+(a-1)q\) and \(g=(a-1,b)\mid p\). If consistent, take \(q=q_0+(b/g)n,\ r=r_0+((a-1)/g)n\). Sieve \(q,r,P=q+(b-1)r\) over length \(O(gX/(ab))\). Slopes are positive; the three absolute determinants for \((q,r),(q,P),(r,P)\) are respectively \(p/g,(b-1)p/g,p/g\). The interval bound includes the integer endpoint error since \(X/(ab)\gg X^\eta\). Although \(g\) can equal the *moving* seed \(p\), its harmonic cost is uniform. The extra \(p\)-weighted mass occurs only for \(p\mid a-1,\ p\mid b\); after \(a=1\) was removed, each corresponding harmonic sum is \(\ll(\log X)/p\). Hence \(\sum_{a,b}g/(ab)\ll(\log X)^2\) over the consistent assignments.

With \(\log H\gg\eta\log X\), the reciprocal sums over fixed prime variables are \(O(L)\) and those over fixed integer variables \(O(\log X)\). Thus the four line-sieve contributions are bounded respectively by a constant times
\[
 {XL^3\over \eta\log X},\quad {XL^3\over \eta^2\log X},\quad
 {XL^3\over \eta^2\log X},\quad {XL^3\over \eta^3\log X}.
\]
Adding \(O(\eta X)\) proves the one-seed assertion. Finally \(\pi((\log X)^{1/4})\ll(\log X)^{1/4}/L\) gives the claimed simultaneous conclusion by a union bound. No independence of any prime events was assumed.

The factor-graph convention reverses [Bożek's original arrows](https://arxiv.org/abs/1909.09900). [Kelanemer's related 2026 abstract](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) concerns terminal-component methods; its full text could not be consulted. No priority claim is made.
