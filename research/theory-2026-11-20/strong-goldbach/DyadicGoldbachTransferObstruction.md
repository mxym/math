# Off-dyadic Goldbach counts do not force dyadic positivity by deterministic transfer

There is a single subset \(\mathcal P_*\) of the actual primes with **no** pair summing to a power of two, yet for every even nonpower \(M\) only
\[
 O\bigl(M\log\log(3M)/\log^3(3M)\bigr)
\]
of the ordered genuine-prime pairs summing to \(M\) are lost. For the ordered log-weighted pair count the loss is thus \(o(M)\), uniformly in these targets. This is a limitation of transfer arguments that use only the other targets' counts. It is not a counterexample for the actual primes; nor does it assert that the subset satisfies Dirichlet-GRH-scale errors.

Delete 2. For every odd prime \(p\), let \(N\) be the unique power of two for which \(N/2<p<N\). Delete \(p\) exactly when \(N-p\) is prime. Any odd-prime pair summing to a power of two has different terms and has its larger term deleted. For even \(M\) not a power of two, a lost pair can be counted by ordering a deleted \(p\) first, with an overall factor at most 2. The deletion of 2 gives \(O(1)\) pairs. Otherwise \(N<2M\) and the three linear forms
\[
 p,\qquad M-p,\qquad N-p
\]
are all prime. Powers \(N\le\sqrt M\) cost \(O(\sqrt M)\) positions in total since \(p<N\).

For \(\sqrt M<N<2M\), work in the interval \(1\le p<\min(M,N)\) of length \(L\asymp N\). Its obstruction at a prime \(\ell\) is the set \(\{0,M,N\}\bmod\ell\), of size \(\nu(\ell)\). If it covers all residues, a forced prime value equal to \(\ell\) gives at most three positions, so assume admissibility. For \(\ell\ge5\), \(N\) is invertible; hence \(\nu(\ell)=3\) ordinarily and \(\nu(\ell)=2\) exactly when \(\ell\mid M(M-N)\). The factors at 2 and 3 in the admissible case are bounded absolutely.

For clarity, the elementary Selberg upper bound here has main bound \(L/J\): with \(R=L^{1/10}\), sieve primes up to \(z=R^{1/20}\), and put \(g(\ell)=\nu(\ell)/\ell\). Then \(J\) is the sum over squarefree \(d\le R\) composed of these primes of the multiplicative weights with prime values \(g(\ell)/(1-g(\ell))\). The Selberg weights are bounded by \(\prod_{\ell\mid d}(1-g(\ell))^{-1}\le d\). The CRT remainder, summed over two divisors \(\le R\), is at most \(R^6\) since the number of relevant residues modulo their lcm is at most that lcm. Inputs for which one of the three forms is itself at most \(z\) cost \(O(z)\) positions. The product giving the sum of the weights with no condition \(d\le R\), normalized to a probability measure, has independent prime factors of inclusion probabilities \(g(\ell)\). Its mean \(\log d\) is at most \(3\sum_{\ell\le z}\log\ell/\ell=(3+o(1))\log z\), so Markov's inequality shows \(J\) is at least half this unrestricted product for large \(L\). The upper bound for admissible \(N\) is therefore
\[
 \ll L\prod_{\ell\le z}(1-\nu(\ell)/\ell)+R^6+z
 \ll \frac{N}{\log^3 M}\log\log(3M).
\]
Indeed the generic dimension-three product is \(O(\log^{-3}M)\) by Mertens' estimate; the exceptional correction at \(\ell\ge5\) is \(1+1/(\ell-3)\). Its product is bounded by a constant times \(\prod_{\ell\mid M(M-N)}(1-1/\ell)^{-1}\ll\log\log(3M)\): split at \(\log(3M)\), apply Mertens below the split, and use the number of large prime divisors of an integer of size \(O(M^2)\) above it. Sum the upper bound over the powers \(N<2M\) using their geometric spacing. Multiplication by at most \(\log^2 M\) gives the stated weighted result.
