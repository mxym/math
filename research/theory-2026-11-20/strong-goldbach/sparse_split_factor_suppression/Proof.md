# Sparse split-factor suppression for an actual reflected-prime moment

Fix \(J_0\), a closed nondegenerate subinterval of \([1,3/2]\), and a fixed smooth real \(g\) on \([0,\infty)\) with \(g=1\) near zero and \(g=0\) on \([\theta,\infty)\) for some \(\theta<1/2\). For even \(N=2x\), write \(J=xJ_0\), \(L=\log x\), and put
\[
 S_g(y)=\sum_{d\mid y}\mu(d)\,g(\log d/L).
\]
Choose distinct primes \(\ell_1,\ldots,\ell_k\ge5\) with \(\sum_j1/\ell_j\le1\), let \(M=\prod_j\ell_j\), and set \(\delta=2^{-k}\), with \(k\ge4\). Let \(\mathcal E\) be the primes \(q\nmid M\) with \((q/\ell_j)=+1\) for every \(j\). Let \(b_{\mathcal E}(y)\) indicate that \(y\) is squarefree and all its prime factors belong to \(\mathcal E\). Define the **actual** signed moment
\[
 \mathcal M_{\mathcal E,g}(N)=
 \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}
       \log P\,b_{\mathcal E}(y)S_g(y).
\]
The contribution from composite \(y\), even in absolute value term by term, satisfies
\[
 \sum_{\substack{y\in J\ {\rm composite}\\P=N-y\ {\rm prime}}}
      \log P\,b_{\mathcal E}(y)|S_g(y)|
 \ \le C_g\delta^2\frac{x\mathfrak S(N)}{L}                    \tag{1}
\]
for all sufficiently large even \(N\). Here \(\mathfrak S(N)\) is the usual Goldbach singular series, and \(C_g\) may also depend on \(J_0\) but is independent of \(k,M,N\). The lower threshold for \(N\) can depend on \(M,k,g,J_0\).

## Conditional target, not a proved lower bound

For prime \(y\in J\) one has \(S_g(y)=1\) for sufficiently large \(N\). Thus (1) gives an unconditional necessary bound \(|\mathcal M_{\mathcal E,g}(N)|\le C_g\delta^2 x\mathfrak S(N)/L\) at every large center with no prime pair in this split bank. In particular, given any fixed \(\nu>0\), choose \(k\) so large that \(C_g\delta\le\nu/2\). A genuinely arithmetic lower bound
\[
 \mathcal M_{\mathcal E,g}(N)\ge
       \nu\delta\,\frac{x\mathfrak S(N)}{L}                    \tag{2}
\]
on the same actual prime-opposite moment would then imply at least
\(\nu\delta x\mathfrak S(N)/(4L^2)\) such prime pairs. This is a single shifted signed-moment target, not itself an assertion about which \(y\) are prime. For example, a squarefree semiprime with two factors in \(\mathcal E\) both of size \(x^{1/2+o(1)}\) also has \(S_g(y)=1\); the discrimination uses the size of the total, not the sign of an individual row. An estimate at this precision is missing. No unshifted calculation, progression main term, or result for \(p-1\) is being used to assert (2).

There is no local zero for the prime part at the chosen conductors. If \(\ell_j\mid N\), the proportion of eligible pair residues on which the second prime has \((q/\ell_j)=+1\) is \(1/2\). Otherwise it is
\[
 \frac{(\ell_j-1)/2-\mathbf 1_{(N/\ell_j)=+1}}{\ell_j-2}
      =\tfrac12\big(1+O(1/\ell_j)\big).
\]
Thus their product is comparable to \(\delta\) with absolute bounds. This is only a local calculation, not a shifted-prime estimate.

## Proof of (1)

Choose a fixed \(\sigma>0\) after \(k\), small enough that \(\sqrt{\sigma}\le\delta^2\). The published [smooth short-score localization estimate](https://github.com/mxym/math/commit/18df7d45), Sections 3–4, bounds the absolute contribution with \(P^-(y)<x^\sigma\) by \(O_g(\sqrt{\sigma}\,x\mathfrak S(N)/L)\). Its statement with the extra \(\log y\) gives this version because \(\log y\asymp L\) on \(J\). It applies after any positive restriction, in particular \(b_{\mathcal E}\). The finitely many prime inputs dividing \(N\) may be discarded at cost \(x^{o(1)}\) using \(|S_g(y)|\ll_g\tau(y)\). We may now take \((y,N)=1\).

For a composite in the retained rows let \(r=\omega(y)\ge2\), \(B=P^+(y)\), and \(H=y/B\). The other \(r-1\) prime factors of \(H\) are distinct, all in \(\mathcal E\) and at least \(x^\sigma\). Since \(B\ge y^{1/r}\ge x^{1/r}\) and \(\log y\le L+O(1)\), the length scale \(Y=x/H\) satisfies \(Y\gg B\), \(\log Y\gg L/r\), and \(r\) is bounded in terms of \(\sigma\). There are exactly \(\delta\varphi(M)\) permissible reduced classes \(a\bmod M\) for \(B\), by the Chinese remainder theorem.

For a fixed \(H\) and such a class put \(B=a+Mt\), so the actual prime forms are
\[
 a+Mt,\qquad N-H(a+Mt),
\]
on an interval of length \(\asymp Y/M\). At any \(\ell_j\mid M\) the first form is nonzero modulo \(\ell_j\). If the second form vanishes there, it cannot be the actual prime being counted (it lies in \(N-J\) and is much larger than the fixed \(\ell_j\)), so omit that class. In particular when \(\ell_j\mid N\) its second residue is \(-Ha\not\equiv0\bmod\ell_j\). For primes \(p\nmid M\) the change of variable \(t\) is invertible. There is one forbidden root at \(2\), two at any odd \(p\nmid HN\), and one at any odd \(p\mid HN\), since \((H,N)=1\) and \(H\) is odd.

The usual two-form upper sieve, with a fixed small power of \(Y/M\) as level and sieve cutoff, therefore gives
\[
 \ll \frac{Y/M}{\log^2(Y/M)}\,\mathfrak S(N)
             \prod_{\substack{p\mid H\\p>2}}\frac{p-1}{p-2}
             \prod_{\ell\mid M}(1-2/\ell)^{-1}
\]
pairs in the given class. This follows from the above root counts and the ordinary upper sieve in an integer interval; its uniformity does not require any theorem about distribution of primes to the modulus \(M\). The last product is bounded by an absolute constant, using \(\ell\ge5\) and \(\sum1/\ell\le1\). The product over \(H\) is \(1+O_\sigma(x^{-\sigma})\). For \(x\) sufficiently large in terms of \(M,\sigma\), \(\log(Y/M)\gg L/r\) with an absolute constant and both true prime forms are above the sieve cutoff. Thus after summing at most \(\delta\varphi(M)\) classes and inserting \(\log P\), the total weight in \(B\) for this \(H\) is at most
\[
 \ll\delta r^2\,\frac{x\mathfrak S(N)}{HL}.                     \tag{3}
\]
The bound includes each possible actual number only through its largest factor.

Pair the divisors forming \(S_g(y)\) by toggling the least prime. The mean value theorem gives
\[
 |S_g(y)|\le 2^{r-1}\|g'\|_\infty\frac{\log P^-(y)}{L}.
\]
For \(r\ge2\) this least label is among the factors of \(H\). Write \(v(q)=\log(L/\log q)\) for these factors. They are less than \(x\), since \(y\le1.5x\) and each has at least one odd complementary factor. In each unit \(v\)-bin meeting \(q\ge x^\sigma\), the prime reciprocal mass of \(\mathcal E\) is at most \(2\delta\) for sufficiently large \(x\): this is the prime number theorem in fixed reduced progressions modulo \(M\) and partial summation. This is uniform in the finitely many bins for fixed \(\sigma\). More precisely a full bin \([j,j+1)\) has limiting reciprocal mass \(\delta\log(e)=\delta\); applying the full-bin bound to either truncated end only enlarges it.

For \(n=r-1\), spread the ordered reciprocal-prime mass in each bin onto Lebesgue measure in its unit interval. To see that ties cause no loss, for occupancy \(m_j\) in bin \(j\) the distinct unordered choices have total mass at most \(\prod_j(2\delta)^{m_j}/m_j!\), while the ordered continuous region for the same occupancy has volume \(\prod_j1/m_j!\). Replacing \(v(q)\) by its bin index in the factor for the least prime costs at most \(e\) once, rather than a factor for every label. Therefore
\[
 \sum_H \frac1H\frac{\log P^-(H)}{L}
 \le e(2\delta)^n
     \int_{0\le v_n\le\cdots\le v_1}e^{-v_1}\,dv_1\cdots dv_n
 = e(2\delta)^n.
\]
The last integral is one, because its section at \(v_1=t\) has volume \(t^{n-1}/(n-1)!\). We enlarge the actual set of \(H\)'s in this harmonic upper bound, which is nonnegative.

Combining with (3), rank \(r\) costs at most
\[
 O_g\!\left(\delta r^2(4\delta)^{r-1}
                 \frac{x\mathfrak S(N)}{L}\right).
\]
The sum over \(r\ge2\) is \(O_g(\delta^2 x\mathfrak S(N)/L)\) since \(4\delta\le1/4\). Restore the removed tiny-label contribution, of the same size. This proves (1). The quantifier order is fixed \(g,J_0\), then \(k\) and all fixed conductors, then \(\sigma\) depending on \(\delta\), then \(x\) sufficiently large in these quantities. We do not let the conductors or the sieve parameters grow with \(x\).

## Why a bounded prime-free reflected model does not supply (2)

In fact the same cap, with a constant proportional to \(C\), holds for a prime-free nonnegative proxy \(a_y\) in place of \(\mathbf 1_{P\ {\rm prime}}\log P\), if for \(y\in J\)
\[
 a_y=0\ (y\ {\rm prime}),\qquad
 a_y\le C\sqrt L\,\mathbf 1_{(y,N)=1}\mathbf 1_{P^-(N-y)>\exp(\sqrt L)}.
                                                               \tag{4}
\]
For \(\sigma\)-truncated rows, keep the same split-prime \(B\) and residue classes as above. Sieve the first form to a small fixed power of \(Y/M\), and the other form only to \(w=\exp(\sqrt L)\). Then the two-form Euler product used above has denominator \(\log(Y/M)\log w\) rather than \(\log^2(Y/M)\): below \(w\) there are the previous two-form factors, and above \(w\) only the prime-\(B\) factors. Multiplying by \(\sqrt L=\log w\) yields a bound no larger than (3) up to an absolute factor, since \(\log(Y/M)\ll L\).

The same tiny-label deletion also applies under (4). Indeed, first without the residue mask, in the largest-factor bound of the cited localization proof, when \(\log(2Y)\le200\sqrt L\) the ordinary prime upper bound for \(B\) gives \(O(C\sqrt L\,Y/\log(2Y))\), at most \(O(C LY/\log^2(2Y))\). When \(\log(2Y)>200\sqrt L\), use the same two cutoffs just described, now without \(M\). This gives the identical bound \(O(C LY/\log^2(2Y))\) times the original singular factors of \(N,H\). The purely divisor and harmonic argument in the localization proof then applies unchanged, so its tiny-factor cost is \(O_g(C\sqrt{\sigma}\,x\mathfrak S(N)/L)\). Thus a fixed proxy of this kind has only \(O_g(C\delta^2 x\mathfrak S(N)/L)\) mass in the signed score and, for small enough \(\delta\), cannot satisfy a lower of order \(\delta x\mathfrak S(N)/L\).

For a concrete comparison, [Aquila, *Hooley’s twisted cancellation below level \(4/15\) does not force primes*, November 2026, §9](https://hexagonmath.org/pdf/2611.00798v1) gives a reflected model which on this interior window is prime-free and satisfies (4) up to absolute fixed changes of the cutoff and a constant for the chosen construction: its displayed baseline \(b'_y\) has \(w=\exp(\sqrt{\log N})\), \(K_w\asymp\sqrt{\log N}\), and a uniformly bounded large-prime Euler correction, and §9.3 gives \(a_y\le Cb'_y\). The coprimality against \(N\) enforces the remaining missing small-prime exclusions in its presieve. This comparison uses the stated pointwise envelope, not undifferentiated Type I/II assertions or any claimed estimate for genuine prime weights.

The lower moment (2) would distinguish true prime weights from this fixed proxy; (1) is not a proof of that lower. Classical weighted norm counts do not give the needed unweighted rank mask, and the current [Jiang–Lau–Lü preprint on \(p-1\) as a sum of two squares, v2](https://arxiv.org/abs/2611.12467) concerns a fixed shift and one quadratic field, not the actual \(N-P\), the short signed score, or simultaneous sparse splitting here.
