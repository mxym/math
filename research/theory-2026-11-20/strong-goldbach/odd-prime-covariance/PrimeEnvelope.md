# Full-product distribution and exact one-sided physical envelopes

Use the central notation in [the criterion](Proof.md). For fixed \(k>0,\ j\ge2\), write \(\Delta_{j,k}=\{x_i\ge k,\ \sum x_i=1\}\), \(dx=dx_1\cdots dx_{j-1}\). Empty faces are omitted. Let \(g\ge0\) be a bounded symmetric Riemann-integrable profile on this face. With \(x_i=\log p_i/\log r\) for the distinct prime factors of \(r\), the following uniform-in-even-target estimate holds:
\[
 \limsup_{P\to\infty}
 \frac{1}{XS}\sum_{\substack{n+r=P,\ n,r\in I\\ \mu^2(r)=1,\ \Omega(r)=j,\ R_{P^k}(r)}}
               V(n)\,L\,g(x_1,\ldots,x_j)
 \ \le\ \frac4{j!}\int_{\Delta_{j,k}}\frac{g(x)}{\prod_i x_i}\,dx .                \tag{A}
\]
If coordinates fall in vanishing neighborhoods of the boundary, extend the bounded profile arbitrarily there, or drop the negligible cells. Unlike peeling \(j-1\) fixed factors and using only the last prime's level of distribution, (A) carries no factor \(1/\max x_i\).

## 1. Why the constant is 4 at the full product scale

Count labeled genuine prime factors in fixed rectangular exponent boxes, then divide the symmetric sum by \(j!\). Repeated primes cost \(P^{1-k+o(1)}+P^{1/2+o(1)}\) with our weights. Take one prime as the first convolution coordinate and group the other \(j-1\) into the second (retaining their box cuts). The whole count has multiplicity at most \(j!\) per integer, and both coordinates have polynomial length at least \(P^{k+o(1)}\). The grouped coefficient obeys the divisor bound; the single prime indicator in a subinterval of a dyad is Siegel–Walfisz, including auxiliary unit conditions, as ordinary SW and removal of at most \(\omega(t)\) primes dividing an auxiliary \(t\) show. Use [Maynard, *Primes in arithmetic progressions to large moduli I*, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733) (also [Polymath8, Theorem 14](https://doi.org/10.1186/s40687-014-0012-7)), on independent fine dyadic subintervals. For any fixed \(\nu>0\) small, the total absolute discrepancy to all \(d\le P^{1/2-2\nu}\) at the reduced target residue \(P\bmod d\) is \(O_A(PL^{-A})\) for any \(A\), relative to \(\phi(d)^{-1}\sum_{(r,d)=1}a_r\) for the box sequence \(a_r\). This is the level of the product, not the level of an individual prime. For \(r\in I\) use meshes of ratio \(1+L^{-J}\) on the first prime and the grouped coordinate. The discarded boundary union has only \(O(PL^{-J}+1)\) physical indices. On progression rows the summed multiplicities are bounded by \(j!\tau(P-r)\); on main rows by \(O(j!L)\). Hölder with global divisor moments gives arbitrary log saving by choosing \(J\) large. There are only log-powerly many boxes and the independent result has any log reserve. Fixed coarse profile boxes are taken in exponents \(\log p_i/L\); conversion to normalization \(\log r\) costs only a vanishing boundary neighborhood since \(r\in I\).

Now upper-sieve \(n=P-r\) on this nonnegative sequence, at primes \(\ell\nmid P\); the prime 2 divides \(P\). All actual central prime \(n\) exceed \(H=P^{1/4-\nu}\). The density of the forbidden unit class is \(1/(\ell-1)\). Use the [Selberg upper bound with remainder](https://people.math.harvard.edu/~elkies/M259.02/sieve.pdf) with squarefree divisor support up to \(H\) in the Selberg weights. The main upper bound is \((\sum a_r)/G_P(H)\) where
\[
 G_P(H)=\sum_{\substack{b\le H\\(b,P)=1}}\mu^2(b)\prod_{\ell\mid b}\frac1{\ell-2}.
\]
For details on replacing the exact coprime means, the summed weight on each modulus \(d\le H^2\) is at most \(3^{\omega(d)}\); for each \(r\) all its factors exceed \(P^k\), so \(\sum_{(r,d)>1,d\le H^2}3^{\omega(d)}\mu^2(d)/\phi(d)\ll_j P^{-k}L^{O(1)}\) by marking one such factor. The weighted absolute BV error is \(O_A(PL^{-A})\) by Cauchy: besides the unweighted BV sum, use \(\sum_{d\le H^2}9^{\omega(d)}|E_d|\ll_j PL^{O(1)}\) by the multiplicity bound and counting integers in a progression, including its unit main. Dropping \(r\)'s with a prime factor dividing \(P\) is optional and negligible, since those factors exceed \(P^k\). Hence no unit residue at a divisor of \(P\) is required.

With only 2 excluded, the harmonic convolution with \(\mu(b)/b\) gives \(G_2(H)=\log H/(2C_2)+O(1)\), as in [rough ranks, §1](../pan-rough-rank/Proof.md). Removing a prime \(\ell>2\) reduces the denominator by at most a factor \((\ell-1)/(\ell-2)\) since the \(\ell\)-part contributes at most the rest divided by \(\ell-2\). Thus \(1/G_P(H)\le (1+o(1))S/\log H\) uniformly in the target.

It remains to normalize by the actual ordinary box mass, not a normalized probability measure. By elementary PNT on the last prime after fixing the preceding \(j-1\), the ordinary profile sum is asymptotic in the additive sense to
\[
 \frac{X}{Lj!}\int_{\Delta_{j,k}}\frac{g(x)}{\prod_i x_i}\,dx ,
\]
with error \(o(X/L)\). Indeed the reciprocal prime measures on compact exponent intervals converge to \(dx_i/x_i\). Away from exponent boundaries, the last prime runs from \((P/3)/\prod_{i<j}p_i\) to twice that value, so PNT supplies \(X/[(\prod_{i<j}p_i)L(1-\sum_{i<j} x_i)]\) with uniform relative error, since this last scale is polynomially large. Boundary cells have vanishing total integral; bounded Riemann profiles follow by upper and lower rectangular sums on the face. Apply the box sieve first to nonnegative upper sums, multiply by \(V(n)L\le L^2\) on the prime support, and let \(P\to\infty\), the coarse mesh size go to zero, then \(\nu\downarrow0\). This proves (A).

## 2. Signs of the physical coefficient, not a model for prime independence

Set \(k=\kappa=333/4000\). At odd squarefree composite rank \(j\) off the midpoint walls \(x_T=1/2\), the total divisor sum \(\sum_{d\mid r}\mu(d)\log d=0\) and the critical short cutoff give
\[
 B(r)/L=F_j(x)+o(1),\qquad F_j(x)=\sum_{x_T>1/2}(-1)^{|T|}x_T
       =\tfrac12\sum_{x_T>1/2}(-1)^{|T|}.
\]
For the last equality, complement the lower sets and use \(\sum_T(-1)^{|T|}x_T=0\). The approximation is uniform outside fixed neighborhoods of the finitely many walls, then send their widths to zero: (A) bounds the weighted mass of such neighborhoods and their integrals tend to zero. This also handles the \(20\log L/L\) wall shift and the central \(\log r/L\) factor. If \(\max x_i>1/2\), \(F_j=0\), since the upper family comprises all subsets containing that coordinate. Off these dominant cells let \(N_m\) count the \(m\)-sets above half. Complementary sets give \(F_3=1,\ F_5=-3+N_2,\ F_7=10+N_2-N_3\). In particular rank three's adverse part is \(o(XS)\), not the opposite sign estimate for Pan's long weight.

At all ranks \(|F_j|\le C_j=\binom{j-2}{\lfloor(j-2)/2\rfloor}\): expand \(x_T\) as a sum over its coordinates, and apply to each coordinate's other \(j-1\) elements the alternating-sum bound for an increasing family. Its member fraction by rank is nondecreasing by random maximal chains, and each alternating binomial tail has size at most the indicated central binomial coefficient. Since \(\prod x_i\ge k^{j-1}(1-(j-1)k)\) by log concavity, the simplex volume gives either orientation of sign in (A) at \(j=9,11\) at most
\[
 T_j=\frac{4C_j(1/k-j)^{j-1}}{j(1-(j-1)k)((j-1)!)^2}.
\]
No other ranks above seven occur in \(J_H\).

## 3. Exhaustive rational upper sums on the simplex

Run **python3 -O verify.py** beside this file (C++17 compiler and GMP/GMPXX required). The checker builds [cubes.cpp](cubes.cpp), reads its exact integer totals, verifies full simplex mass and independently computes rational comparisons. No floating-point tests are used.

Let \(k=c/d=333/4000,\ a=d-jc,\ H'=dK,\ r_i=cK+a b_i\). On each cell write \(x_i=(r_i+a z_i)/H',\ b_i\) nonnegative integers, \(0\le z_i\le1,\ \sum z_i=l=K-\sum b_i\). Ignore boundaries of measure zero; \(1\le l<j\). Enumerate all decreasing bin tuples, multiplying by \(j!/\prod m_b!\) where \(m_b\) are the bin multiplicities. The volume per ordered bin tuple in the first \(j-1\) coordinate chart is
\[
 (a/H')^{j-1}\frac{E(j,l)}{(j-1)!},\qquad
 E(j,l)=\sum_{i=0}^l(-1)^i\binom ji(l-i)^{j-1}.
\]
Indeed enforce \(z_i\le1\) by inclusion–exclusion in a simplex. The integer mass \(\sum {\rm mult}\,E(j,l)=K^{j-1}\) is checked in both engines. This is a partition of all profiles, not a sample of sorted cells.

If \(2r_1\ge H'\) the whole cell has zero weight almost everywhere. Otherwise only the nondominant points within the cell need to be bounded. A subset \(T\) is certainly above half if \(2(\sum_{i\in T}r_i+a\max(0,l-j+|T|))>H'\); it is possibly above half only if \(2(\sum_{i\in T}r_i+a\min(l,|T|))\ge H'\). On this cell upper bound the adverse rank-five profile by \([3-N_2^{\rm certain}]_+\), the adverse rank-seven profile by \([\min(10,N_3^{\rm possible}-10-N_2^{\rm certain})]_+\), and the positive rank-seven by \([\min(10,10+N_2^{\rm possible}-N_3^{\rm certain})]_+\). Here 10 is \(C_7\). A common denominator lower bound is
\[
 \prod_i x_i\ge (r_1+a l)\prod_{i=2}^j r_i/(H')^j
\]
by \(\prod(1+a z_i/r_i)\ge1+al/r_1\). Divide the numerator upper bound by this denominator lower bound, round **up** to an integer, and multiply by the exact cell volume and \(4/j!\) in (A). The three rational numerator/denominator ledgers before simplification are:

| rank, sign | mesh | sorted cells | numerator | denominator |
|---|---:|---:|---:|---:|
| 5, negative |224|3,818,069|1548649460784975336313262500|1856198965985280000000000000|
| 7, negative |64|276,050|6639968841975281434099343180383442248|1021416395487628492800000000000000000000|
| 7, positive |64|276,050|37496824479853097264877986874445249536|1021416395487628492800000000000000000000|

Including \(T_9+T_{11}\) in each corresponding rank-seven tail, the rational checker proves (2) and the combined adverse threshold. No rank-five positive bound is included on the adverse side, no doubling of the orientation is made, and the factor 4 in (1) of [the criterion](Proof.md) is a separate algebraic factor. Generalized BV and the Selberg sieve remain classical; this application bounds true weighted prime rows, not true correlations of two arbitrary composite profiles.
