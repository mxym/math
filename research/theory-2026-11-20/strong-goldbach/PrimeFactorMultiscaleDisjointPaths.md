# Many disjoint decreasing paths in the Goldbach factorization graph

Written research note. This is an application of the classical Bombieri–Vinogradov theorem, not a priority claim. No Goldbach representation, strongly connected component, or restriction to largest factors is asserted.

For an even integer \(N\) put an edge \(q\to r\) between prime vertices when \(r\mid N-q\). This is the forward-divisor orientation, the reverse of [Bożek's Goldbach factorization graph](https://arxiv.org/abs/1909.09900). Here all constructed edges use proper divisors and so are present regardless of whether one also includes prime complements as edges.

**Theorem.** Fix a depth \(h\ge1\), and exponents \(a_0=1/2\) and \(0<a_i<a_{i-1}/2\) for \(1\le i\le h\). For each sufficiently large even \(N\), there are
\[
 (1+o(1))\,\frac{N^{a_h}}{a_h\log N}
\]
pairwise vertex-disjoint directed paths \(p_0\to p_1\to\cdots\to p_h\) with \(N^{a_i}<p_i\le 2N^{a_i}\). For each \(i\) all but \(O_A(N^{a_i}/(\log N)^A)\) primes in layer \(i\) can be kept in sets \(G_i\), for any fixed \(A>0\), so that every \(r\in G_i\), \(i\ge1\), has \(\gg N^{a_{i-1}-a_i}/\log N\) parents in \(G_{i-1}\). Implied constants and the sufficiently large threshold may depend on the fixed parameters.

**Proof.** Write \(L=\log N\) and \(X_i=N^{a_i}\). Retain as \(G_0\) the primes in \((X_0,2X_0]\) not dividing \(N\). At most \(O(L)\) prime divisors of \(N\) are ever excluded on this account, so this is negligible at every polynomial layer. For a step with \(X=X_{i-1}\), \(R=X_i\), and a prime \(r\in(R,2R]\) not dividing \(N\), its raw incoming count is
\[
 \pi(2X;r,N)-\pi(X;r,N)
 = \frac{\operatorname{li}(2X)-\operatorname{li}(X)}{r-1}+E_r.
\]
The residue argument denotes the reduced class of \(N\). By maximal-residue [Bombieri–Vinogradov](https://personal.science.psu.edu/rcv4/Bombieri.pdf), followed by partial summation or its prime-count version, \(\sum_r |E_r|\ll_B X/L^B\) for each fixed \(B\). The hypothesis \(2R\le X^{1/2-\eta}\) holds with fixed \(\eta>0\), so the full logarithmic loss in the theorem is harmless. Every main term is \(\gg X/(RL)\). Excluding moduli whose error exceeds one quarter of its main term costs \(O_B(R/L^{B-1})\) primes.

Now restrict parents to \(G_{i-1}\). Every deleted prime \(q\) in the parent interval has at most \(1/a_i\) distinct prime factors \(r>R\) in \(N-q\), since the product of those factors divides \(N-q<N\). Thus deleting \(O_S(X/L^S)\) parents deletes only \(O_S(X/L^S)\) total incidences into the present layer. Moduli losing more than one quarter of their main term therefore number \(O_S(R/L^{S-1})\). Remove these too. The surviving \(G_i\) has the required incoming degree. Taking \(B=A+h+3\) throughout and retaining a decreasing savings exponent \(A+h+2-i\) allows all \(h\) steps with at least the advertised exponent \(A\).

At each step a child subset \(S\subseteq G_i\) sends at least \(d_i|S|\) incidences to its parents, where \(d_i\gg X/(RL)\) tends to infinity. A parent receives at most \(1/a_i\) such incidences, so the parent neighborhood has size at least \(|S|\) for large \(N\). Hall's theorem supplies an injection \(G_i\to G_{i-1}\) following reversed edges. Composition gives one path from a distinct top vertex to every bottom vertex, disjoint across all layers since the injections are injective and the intervals do not overlap. The prime number theorem and \(A>1\) give \(|G_h|\sim N^{a_h}/(a_hL)\). For all edges, \(r\le 2\sqrt N<N-q\) eventually; they are proper divisors. This proves the result.

**Scope.** For any fixed \(h\) the bottom exponent may approach \(2^{-h-1}\) from below. The theorem permits primes in the selected bands only as divisors; it does not require \(r=P^+(N-q)\), does not make the first complement an almost prime, and cannot replace the [genuine largest-first-step path bound](PrimeFactorDisjointDepthTwoPaths.md). In particular, disjoint decreasing paths alone do not constrain the number or separation of terminal components.
