# A near-balanced genuine semiprime source with squarefree almost-prime partners

Let \(J\) be a fixed nondegenerate interval contained in \((1/3,2/3)\), let \(N\) be an even integer, and put \(I=NJ\) and \(L=\log N\). Write
\[
\mathfrak S(N)=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)
                    \prod_{\substack{p\mid N\\p>2}}\frac{p-1}{p-2}.
\]
There are fixed \(v_0,c>0\) with the following property. Let \(\mathcal U\) be **any subset** of the primes in \([N^{.4872},N^{.4876}]\), and let \(X_{\mathcal U}\) be the number of pairs of primes
\[
u\in\mathcal U,\quad N^{.5123}\le t\le N^{.5129},\quad
ut\in I,\quad (ut,N)=1.
\tag{1}
\]
For any fixed \(B>0\), uniformly over \(\mathcal U\) with \(X_{\mathcal U}\ge N/L^B\), if \(N\) is sufficiently large in terms of \(B,J\), then at least
\[
 c\, X_{\mathcal U}\frac{\mathfrak S(N)}{L}
\tag{2}
\]
of the partners \(N-ut\) in (1) are squarefree, have at most two prime factors, and have least prime factor \(>N^{v_0}\). The pair \((u,t)\) is determined by \(ut\) since the size bands are disjoint.

In particular, for **every** sufficiently large even \(N\) there are \(\gg_J N\mathfrak S(N)/L^2\) such representations with both labels in the stated narrow bands. More strongly, in every dyadic short-prime interval \((Q,2Q]\subset[N^{.4872},N^{.4876}]\), apart from \(O_{A,J}(Q/L^A)\) prime labels \(u\), each admissible \(u\) has
\[
 \gg_J \frac{N\,\mathfrak S(N)}{u L^2}
\tag{3}
\]
genuine prime partners \(t\) as in (1) with the same rough squarefree conclusion for \(N-ut\). Label primes dividing \(N\) can be included in the exceptional set.

In (2) and (3), the other summand \(N-ut\) may be a prime or a product of two distinct primes. The theorem does not separate these two cases, and \(ut\) is **never prime**. It is not a binary Goldbach theorem.

## Distribution and the local product

Use the independently proved [long-prime-slot dispersion theorem](../prime_slot_dispersion_512/Proof.md) with the macroscopic residue \(a=N\), physical source interval \(I\), short-slot mask \({\bf1}_{\mathcal U}\), and long true prime slot \(t\), deleting source primes dividing \(N\). The bounded short sequence need not obey a Siegel–Walfisz condition, so this mask can depend arbitrarily on \(N\) and on the chosen source labels. Write \(\mathcal A=\{N-ut:(1)\}\), a set of positive integers. For \(D=N^{.512}\) we have, for every fixed \(K,A>0\),
\[
 |\{m\in\mathcal A:d\mid m\}|=X_{\mathcal U}\,g(d)+R_d,\qquad
 \sum_{d\le D}\tau(d)^K|R_d|\ll_{A,K,J} N L^{-A},
\tag{4}
\]
where \(g(d)=1/\varphi(d)\) for \((d,N)=1\) and \(g(d)=0\) otherwise. For \((d,N)>1\), the occurrence part is exactly zero because of the physical unit mask in (1); for the other \(d\), the reduction to the full principal numerator is already part of the dispersion theorem. In particular this is not an application of a distribution theorem with a small fixed residue or only a smooth or factorable set of moduli.

For clarity, take the multiplicative function \(\rho(d)=d g(d)\). In the notation of the weighted sieve, \(0\le \rho(p)/p\le 1/2\) (the prime 2 divides \(N\)), and
\[
 -(C_0+C_1\log\log(3N))<
 \sum_{w\le p<z}\frac{\rho(p)\log p}{p}-\log(z/w)
 \le C_2,\qquad 2\le w\le z,
\tag{5}
\]
for suitable fixed positive constants. Indeed \(\sum_{w\le p<z}(\log p)/p-\log(z/w)=O(1)\) by Mertens' bound, and replacing \(1/p\) by \(1/(p-1)\) costs a uniformly bounded sum. The omitted target primes cost at most \(\sum_{p\mid N}(\log p)/(p-1)\ll 1+\log\log(3N)\), splitting at \(\log(3N)\) and using \(\sum_{p\mid N}\log p\le\log N\) on the upper part. This gives the allowable lower Mertens-deficit parameter \(L_0=O(1+\log\log N)\) of the sieve, while the upper constant is absolute.

The full product over \(p<D\), in precisely this normalization, is
\[
 \prod_{p<D}(1-g(p))
   =(1+o(1))\,\frac{e^{-\gamma}\mathfrak S(N)}{\log D},
\tag{6}
\]
uniformly in even \(N\). Divide each local term by \(1-1/p\): the ratio at 2 is 2, at \(p>2,\ p\nmid N\) it is \(1-1/(p-1)^2\), and at \(p\mid N,\ p>2\) it is \(p/(p-1)\). Apart from the first factor, these are exactly the singular series factors. The truncated tail of the convergent baseline product is \(1+O(1/D)\), and the additional target-prime tail is \(1+O(L/D)\). Mertens' product theorem gives (6), even for targets with unusually many small prime factors.

## The weighted sieve, strict degree margin and squarefree conversion

We use [Greaves, *The weighted linear sieve and Selberg's \(\lambda^2\)-method*, Acta Arith. 47 (1986), 71–96](https://doi.org/10.4064/aa-47-1-71-96), Theorem 1, equation (1.4) and §5. For the precise positive-margin version and dependence on the sieve hypotheses see also the independent original application [Martin, *Uniform bounds for the least almost-prime primitive root*, §3, equations (10)–(12) and (15)–(18)](https://personal.math.ubc.ca/~gerg/papers/downloads/UBLAPPR.pdf). We spell out the point of the weighted formulation rather than assume that distinct-factor and multiplicity counts are automatically interchangeable.

For a set with \(|\mathcal A_d|=X\rho(d)/d+R_d\), Greaves assumes \(0\le\rho(p)/p\le1-1/A_1\) and the two bounds as in (5), with lower deficit \(1\le L_0\le\log D\). For \(a<D^g\) on the set, the numerical input of Greaves gives fixed \(1/2<U<1,\ V<1/4,\ V+2U\ge g\), and an admissible bounded nonnegative weight \(W\) with \(\mathcal M(W)>0\) whenever \(g<2-0.044560\). Here \(W\) may be nondecreasing; it is extended by \(U-V\) for arguments \(>1\). One of its bounds is \(W(t)\le9(U-1/3)t^2\) on \([0,1]\). The theorem lower bounds
\[
 \sum_{\substack{m\in\mathcal A\\\nu_{D,U}(m)\le2}}
 W\!\left(\frac{\log P^-(m)}{\log D}\right)
 \ \ge\
 2e^\gamma X\prod_{p<D}(1-\rho(p)/p)
       \left\{\mathcal M(W)+
                    O\!\left((L_0/\log D)^{1/5}\right)\right\}
 -\sum_{d\le D}\mu^2(d)3^{\omega(d)}|R_d|.
\tag{7}
\]
The count \(\nu_{D,U}\) counts repeated prime factors multiply only for primes at least \(D^U\); it equals \(\Omega\) on squarefree \(m\). The theorem supplies the remainder with a coefficient \(f(d)\le 3^{\omega(d)}\) and \(\mu(d)\), so the last term in (7) is a valid absolute replacement. All choices here depend only on a fixed degree away from the threshold, and the error is uniform in sets with the same upper constants in the local hypotheses.

Take \(g=1.954\). Exactly \(0.512g=1.000448>1\), and \(2-0.044560-g=0.00144>0\), so \(m<N<D^g\) and the strict degree margin holds without using a numerical endpoint equality. The original positive sieve weight may be cut off below a small fixed \(v>0\). More precisely, multiply \(W\) by any continuous monotone factor equal to zero on \((0,v]\), between 0 and 1 on \([v,2v]\), and 1 above \(2v\). The admissibility upper bounds remain true, as does nondecrease if imposed, and \(W(1)\) is unchanged. In Greaves' formula
\[
 \mathcal M(W)=
  -\int_{1/2}^1\frac{W(1)-W(t)}{t(1-t)}\,dt
  +\int_0^{1/2}\frac{W(t)}{t}\left(\frac1{1-t}-h(t,1)\right)dt,
\]
the function \(h\) is nonnegative (a sum of integrals of nonnegative integrands). Therefore the decrease in \(\mathcal M(W)\) is at most
\[
 9(U-1/3)\int_0^{2v}\frac{t}{1-t}\,dt
 \le 16 v^2\quad(0<v\le1/8).
\]
For example \(v=\min(1/8,\sqrt{\mathcal M(W)/100})\) keeps a strictly positive margin. This uses the stated positivity of the published sieve bound, not the provision of an explicit numerical value of \(\mathcal M(W)\). Call the truncated weight \(W_v\), and take \(v_0=.512v\).

Using (4) with \(K=2\) (since \(\mu^2(d)3^{\omega(d)}\le\tau(d)^2\)), choose \(A>B+3\). Then the remainder in (7) is \(o(X_{\mathcal U}/L)\), uniformly for \(X_{\mathcal U}\ge N/L^B\). The error in braces is \(o(1)\) by (5). Together with (6) and boundedness of \(W_v\), this yields \(\gg X_{\mathcal U}\mathfrak S(N)/L\) unweighted terms with \(\nu_{D,U}\le2\) and \(P^-(m)>N^{v_0}\). Before drawing the conclusion about multiplicity, remove all numbers in \([1,N]\) divisible by \(p^2\) for some \(p>N^{v_0}\). There are at most
\[
 \sum_{k>N^{v_0}} N/k^2=O(N^{1-v_0})
       =o(X_{\mathcal U}\mathfrak S(N)/L).
\]
Multiplicity of the map \((u,t)\mapsto N-ut\) is exactly one, so this integer bound is sufficient even in each selected source subset. On the survivors \(\nu_{D,U}=\Omega\), proving (2).

## Source mass and the exceptional-label bound

For any short label \(u\in[N^{.4872},N^{.4876}]\), the physical allowed long interval \(I/u\) is contained in \([N^{.5123},N^{.5129}]\) for large \(N\); the margins are fixed positive exponents. Its length is \(|I|/u\), a fixed positive fraction of the long scale. The prime number theorem gives \(X_u\asymp_J N/(uL)\) uniformly, where \(X_u\) is the raw number of allowed \(t\) for this \(u\) after target-unit deletion. At most \(O(1)\) possible prime labels divide \(N\) in these size ranges. Mertens' theorem for reciprocal primes over the short band implies \(X_{\mathcal U}\asymp_J N/L\) when taking every such unit label, so (2) gives the first unconditional lower bound for every even target.

For the stronger assertion, define the deficient labels as those with fewer than \((c/2)X_u\mathfrak S(N)/L\) credited partners, with \(c\) as in (2). If there were more than \(C_{A,J}Q/L^A\) deficient labels in one of the indicated dyads, their raw source mass would be \(\gg_{A,J} N/L^{A+1}\). Use **that exact set** as \(\mathcal U\) and (2), for instance with \(B>A+2\). It contradicts the definition of deficiency. This proves (3) uniformly in the dyad and \(N\); it is not a conclusion merely for most targets or in a prime model.

## Comparison

The sieve here is classical. [Chen's original fixed-target theorem](https://www.sciengine.com/doi/pdf/8663c8f4bb65481c80325a4101d215ac) has a prime on the source leg and uses a different switching argument; it neither needs nor gives the many near-balanced semiprime source labels in (3). In the same project, the separately proved broad semiprime Chen argument with a smaller prime at least \(N^{.27}\) does not yield (3) on this small harmonic subfamily by a total-count subtraction. The [near-balanced signed giant comparison](../balanced_semiprime_giant_cross/Proof.md) uses a different band of long primes around exponent \(.506\) and establishes a different signed result; its rough-support consequence allows rank three. [Wright, August 2026, Theorem 2.2](https://arxiv.org/html/2608.27732v1#S2) states an overlapping progression estimate in its allowed residue range, as explained in the independent dispersion proof; we do not rely on it. The earlier note [*On Representations of Even Integers as a Sum of Two Semiprimes* (2025 preprint)](https://www.preprints.org/manuscript/202510.2442) claims a different exact-rank asymptotic without these label restrictions; no conclusion or estimate from it is used here. In particular no claim of priority for the sieve, the dispersion ideas, or a fixed-target semiprime result is made.
