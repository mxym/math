# A strictly positive mixed correlation of signed polynomial halves at every even target

Use \(A_j,H_j,O_j,I,X,L,\mathfrak S(P)\) from
[the critical polynomial parity-halves theorem](../midpoint_halves/Proof.md).
For each fixed integer \(j\ge2\) there is \(c_j>0\) such that, for every
sufficiently large even \(P\),
\[
               \langle O_j,O_2+O_3\rangle \ \ge c_j X\mathfrak S(P).      \tag{1}
\]
This is a **natural-scale signed lower bound**, not just the nonnegative
limiting lower bound for individual entries. This proof combines both
degrees 2 and 3 on the second side; it gives no individual positive lower bound. The calculation below is an
ordinary one-dimensional almost-prime lower sieve followed by the
parity-halves theorem, not a parity-breaking assertion about one row.

Indeed, that theorem reduces (1), with uniform \(o_j(X\mathfrak S(P))\)
error, to the nonnegative quantity \(\langle H_j,H_2+H_3\rangle\).
For odd \(j\) choose source \(r\in I\) prime; for even \(j\) choose
\(r=ab\in I\), where \(a,b\) are primes and
\(r^{.45}<a<r^{.46}\). The second prime then has exponent in
\((.54-o(1),.55+o(1))\); factorization with this labeling is unique.
In both cases every factor exceeds \(P^{.44}\), for large \(P\).
Take source weight \(W(r)=\log r\) on the chosen set and zero otherwise.
We have \(H_j(r)\ge c'_j W(r)\): on primes it is equality, and on the
chosen semiprimes this follows from the positive polynomial (2) of the
parity-halves theorem since the two exponents lie in fixed compact subsets
of \((0,1)\). The total source mass \(\mathcal M=\sum_I W(r)\) is
asymptotic to a positive constant times \(X\), by PNT (or the prime-simplex
calculation). The source has ordinary maximal-prefix convolution
Bombieri–Vinogradov at any fixed power below \(1/2\), by
[Motohashi, Theorems 1–2](https://doi.org/10.3792/pja/1195518296);
the factor window is in the variable \(r\), as in Theorem 2. The central cut
and logarithmic weight follow from the maximal-prefix form by partial summation.

**Lower sieve.** For \(0<\delta<.005\) fixed put
\(z=P^{1/4-\delta}\), \(D=P^{1/2-\delta}\), and sieve \(n=P-r\) by
the primes \(p<z,\ p\nmid P\). For squarefree \(d\) supported on these
primes the exact reduced-residue reference is \(\mathcal M/\phi(d)\):
every source \(r\) is coprime to every \(d\). The remainders for
\(d\le D\) have total absolute size \(O_{\delta,A}(PL^{-A})\) for all
fixed \(A\). The omitted \(p<z,\ p\mid P\) cannot divide \(n\) because
they cannot divide \(r\). In particular 2 is correctly omitted.

The dimension-one upper product condition for local densities \(1/(p-1)\)
is uniform in \(P\): deleting target primes only decreases the inverse
Mertens product. Its full product to \(z\) is
\[
 \prod_{\substack{p<z\\p\nmid P}}\left(1-\frac1{p-1}\right)
   =(1+o(1))e^{-\gamma}\mathfrak S(P)/\log z .
\]
The factors at odd target primes larger than \(z\) cost \(1+o(1)\)
uniformly, since \(O(1)\) of them can divide \(P\). The standard lower
linear sieve (for instance
[Matomäki and Teräväinen, *Weighted sieves with switching*, Lemma 2.5](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C))
has lower multiplier \(f(s)=2e^\gamma\log(s-1)/s\) in \(2<s<4\).
Here \(s=\log D/\log z=2+\delta/(1/4-\delta)\), so \(f(s)\gg\delta\)
with an absolute constant. Consequently the physical weight of
\(P^-(n)\ge z\) is at least \(c\delta X\mathfrak S(P)/L\)
for sufficiently large \(P\) at fixed \(\delta\). This is an actual
lower count of the chosen source, not the product of two independent
marginals. The constant \(c>0\) can be taken independent of
\(0<\delta<.005\) (the large-\(P\) threshold may depend on \(\delta\)).

**Four factors and nearly unbalanced triples.** Such \(n\) have at most
four prime factors counted with multiplicity. Delete squareful \(n\):
on this rough set they have total \(W\)-weight
\(O(L(P/z+\sqrt P))=o(P/L)\). If \(n\) has four prime factors then all
are in \([P^{1/4-\delta},P^{1/4+3\delta}]\). Open any three of them
\(p_1,p_2,p_3\) and put \(d=p_1p_2p_3,\ m=n/d\).
Here \(P/d\gg P^{1/4-9\delta}\ge P^{.205}\).
If \(p_i\mid P\), it would divide \(r=P-n\) and would have exponent
at most \(.265<.44\), impossible. Thus \((d,P)=1\).

For fixed \(d\) we bound the number of \(m\in[P/(3d),2P/(3d)]\)
such that both \(m\) and \(P-dm\) are free of primes below
\(P^{1/1000}\), a necessary condition on the indicated support.
A dimension-two upper sieve on this integer interval gives
\[
                  O\!\left(\frac{P\mathfrak S(P)}{dL^2}\right).             \tag{2}
\]
In detail the two forms have two roots at \(p\nmid dP\) and one at
\(p\mid dP\), including just one at 2. Their local product to the fixed
sifting power is \(O(\mathfrak S(P)L^{-2}d/\phi(d))\); here \(d/\phi(d)=1+o(1)\).
The inverse-product dimension bound is uniform. One may use the [beta-sieve fundamental lemma, Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136) at level \(P^{.05}\), whose elementary interval errors
sum to \(O(\sum_{e\le P^{.05}}2^{\omega(e)})=O(P^{.05}L)\), negligible
compared with \(P/(dL^2)\). Its sieve parameter is a fixed 50; no
small relative error is required. The same argument works for two opened
factors when the last prime and the reflected source are both polynomially
rough. The absolute constant in (2) is independent of \(\delta\).

Since \(W\le L\), summing (2) over three prime labels costs at most
\[
 C\frac{P\mathfrak S(P)}{L}
 \left(\sum_{P^{1/4-\delta}\le p\le P^{1/4+3\delta}}\frac1p\right)^3
 \ \ll\ \delta^3 P\mathfrak S(P)/L.
\]
Here the reciprocal sum is
\(\log((1/4+3\delta)/(1/4-\delta))+o_\delta(1)=O(\delta)\)
by PNT; constants in the limiting bound are independent of \(\delta\).
Overcounting orderings only increases this nonnegative upper bound.

One can also discard triprimes \(n\) with largest factor
\(\ge P^{1/2-\delta}\). Their two other primes both lie in
\([P^{1/4-\delta},P^{1/4+2\delta}]\). Open these two and use (2)
on the remaining prime and \(P-dm\), with even longer \(m\)-interval,
at weight cost \(O(\delta^2 P\mathfrak S(P)/L)\). This prices actual
tuples without using sign cancellation. It certifies an interior
balanced triple, when the surviving \(n\) has rank three; it does
not show many survivors have rank three.

Choose a fixed \(\delta>0\) so small that these \(O(\delta^2+\delta^3)\)
upper costs use less than half of the lower \(c\delta\) above. The
remaining actual squarefree \(n\) have rank 1, 2, or 3. All their prime
factors exceed \(P^{.24}\). On rank 1, \(H_3(n)=\log n\); on rank
2, \(H_2(n)=4(\log n)\prod_i\log_n p_i\); on rank 3,
\(H_3(n)=24(\log n)\prod_i\log_n p_i\). Hence \(H_2(n)+H_3(n)\gg L\)
on all these rows, with an absolute implied constant. Multiplying by the
positive remaining \(W\)-mass and by \(c'_j\) proves (1).

Even for the odd-\(j\) source, the prime, semiprime and triprime
possibilities on the other side are pooled. Neither (1) nor the
nonnegative finite-rank comparison separates the pure prime term.

## Scope and comparisons

The positive argument is an application of the classical almost-prime sieve, not a new almost-prime representation theorem or a claim of priority. What transfers here is strict positivity for the specified *signed polynomial correlation*. The repository's [smooth-midpoint reservoir](../midpoint_reserve/Proof.md) uses a different weight and obtains a subscale bound from a squareful and a squarefree input. The [quadratic comparison](../QuadraticUpperAndSwitchingScope.md) puts quantitative bounds on a different low-rank combination, rather than on these opposite halves. Among recent parallel work, [Pham, October 2026, v1, Appendix D](https://www.preprints.org/manuscript/202610.3061) controls benchmark rough pairs in overlapping rows, while [Arneth, October 2026, v1](https://zenodo.org/records/23504447) leaves a fixed-target signed Möbius–prime parity-separation input open. Neither is used as an input here. The isolated prime-prime lower bound remains outside this result.
