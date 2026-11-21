# A strict sub-main-term bound on rough, high-rank, prime-versus-composite negative mass in Pan's remainder

Let \(P\) tend to infinity through all even integers, \(L=\log P,\ Q_0=P^{1/2}L^{-20}\) and \(k=333/4000\). Use the [actual Huang–Li (6) / Pan remainder](https://arxiv.org/html/2005.03811v2#S1), with coefficient \(a(r)=\sum_{d\mid r,d>Q_0}\mu(d)\log d\) on the first input, and \(a^*(r)\) on the second, where the latter sum excludes \((d,P)>1\). Put \(\mathfrak S(P)=2C_2\prod_{s\mid P,s>2}(s-1)/(s-2)\) (products indexed by primes), \(C_2=\prod_{s>2}(1-1/(s-1)^2)\), and \([u]_+=\max(0,u)\).

**Theorem.** In the raw, uncentered sum, consider **both orientations** in which one physical input is a true prime and its complement \(r\) satisfies \(P^-(r)>P^k,\ \Omega(r)\ge6\). Sum the absolute magnitudes of the *negative* terms only. The limsup of this quantity divided by \(P\mathfrak S(P)\) is less than \(0.896\); in particular it is less than \(0.9\) for all sufficiently large even targets. The two orientations are disjoint since the other input is composite. This estimates an actual signed leakage term without subtracting the unknown prime-prime atom.

The proof gives the same bound if one adds rough input of rank four, rank three except the balanced triangles, and rank five except the star profiles specified below. The rank-six-and-higher estimate does *not* require these low-rank refinements. The theorem does not treat rough ranks two, balanced three, the rank-five star, small-factor inputs, or both-composite interactions. A [different, selected-modulus theorem](../PanCentralTwelveFactors.md) can restrict a **centered** progression error to rough inputs at this value of \(k\), e.g. for \(v=0.50005\). It is not a reduction of the entire raw remainder to the physical pairs considered here.

## 1. A uniform one-dimensional sieve at the actual reflected target

Fix a product \(A\) of at most eleven primes \(>P^k\), \(Y=P/A\ge P^k\). Uniformly for \((A,P)=1\), the number of primes \(q\le Y\) for which \(p=P-Aq>P^{3/4}\) is also prime is at most
\[
 (4+o(1))\mathfrak S(P)\frac{Y}{(\log Y)^2}.                     \tag{1}
\]
To see the constant, sieve the already-prime indices \(q\) by the odd primes \(s\nmid AP\), each removing one unit residue. For squarefree \(d\) built from these primes the residue is the **single** unit \(PA^{-1}\bmod d\), and the local density relative to the primes is \(1/\phi(d)\). No small prime \(q\mid d\) satisfies this forbidden unit class. If \(s\mid AP\) no such class need be removed; this will be paid for by the local product. With \(z=Y^{1/4}(\log Y)^{-C}\), every counted \(p\) is above \(z\); extending the range of \(q\) to all \(q\le Y\) is an upper bound, never a lower bound on an interval of actual solutions. Apply the [Selberg upper bound, including its remainder](https://people.math.harvard.edu/~elkies/M259.02/sieve.pdf) with main term \(\operatorname{Li}(Y)/G(z)\), where
\[
 G(z)=\sum_{d\le z,(d,2AP)=1}\mu^2(d)\prod_{s\mid d}\frac1{s-2}.
\]
The remainder is bounded by \(\sum_{d\le z^2}3^{\omega(d)} E_d(Y)\), with \(E_d(Y)=\max_{(a,d)=1}|\pi(Y;d,a)-\operatorname{Li}(Y)/\phi(d)|\). The classical Bombieri–Vinogradov theorem with its maximum over the residue class gives this weighted sum \(\ll_H Y(\log Y)^{-H}\) for any fixed \(H\) on choosing \(C=C(H)\). Indeed Cauchy–Schwarz uses ordinary BV and the trivial \(\sum_{d\le\sqrt Y}9^{\omega(d)}E_d(Y)\ll Y(\log Y)^{O(1)}\), by counting the whole progression and divisor moments. This is uniform even though the residue varies with \(d,A,P\).

With only 2 excluded write the denominator as \(G_0(z)\). Deleting one more prime \(s>2\) from the support reduces the current sum by a factor at worst \((s-2)/(s-1)\): the pre-deletion sum is \(J(z)+J(z/s)/(s-2)\le J(z)(1+1/(s-2))\), where \(J\) is the post-deletion sum. This gives a uniform product comparison without any assumption on the target. Moreover,
\[
 G_0(z)=\frac{\log z}{2C_2}+O(1).
\]
For example, convolve the defining coefficients with \(\mu(n)/n\); the resulting multiplicative \(c\) satisfies \(\sum |c(n)|n^{1/4}<\infty\), as its odd prime coefficient is \(1/(s-2)-1/s=O(s^{-2})\) and its prime-square coefficient is \(-1/(s(s-2))\). Its Euler product sum is \(1/(2C_2)\). Convolving back with \(1/n\) gives the formula. The cost of primes dividing \(P\) is precisely the \(\mathfrak S(P)\) factor; the at most eleven additional primes dividing \(A\) contribute \(1+o(1)\) uniformly. Using \(\log z\sim\frac14\log Y\) proves (1).

## 2. Reduction to a finite-dimensional integral

In either orientation, \(p\nmid P\) implies \((P-p,P)=1\) exactly, so the true asymmetric weight equals the symmetric one. The \(O(L)\) exceptional prime labels dividing \(P\) have cost \(P^{o(1)}\). For every fixed small \(\eta>0\) discard \(\min(p,r)<P^{1-\eta}\) at cost \(P^{1-\eta+o(1)}\). On the rest \(a(p)=-\log p\), so the negative magnitude in one orientation is \((\log p)[a(r)]_+\). Nonsquarefree rough integers have count \(\ll P\sum_{s>P^k}s^{-2}\ll P^{1-k}\), negligible under the divisor maximum. The possible ranks are \(j\le12\).

Let \(\Delta_{j,k}=\{x_i\ge k,\ \sum_{i=1}^j x_i=1\}\), with \(dx=dx_1\cdots dx_{j-1}\). Outside its subset-midpoint walls, put
\[
 F_j(x)=\sum_{S\subseteq [j],\ x_S>1/2}(-1)^{|S|}x_S,\qquad x_S=\sum_{i\in S}x_i.
\]
An upper bound for the limsup of the single-orientation, rank-\(j\) negative mass divided by \(P\mathfrak S(P)\) is
\[
 U_j=\frac4{j!}\int_{\Delta_{j,k}}\frac{[F_j(x)]_+}{(\max_i x_i)\prod_i x_i}\,dx.                                  \tag{2}
\]
For proof peel off the smallest \(j-1\) primes in \(r=Aq\), dividing by \((j-1)!\) if they are labeled; \(q\) is the largest. Take \(x_i=\log p_i/L\) for the peeled primes and \(u=1-\sum_{i<j}x_i=\log Y/L\), so \(u\ge\max_{i<j}x_i\). We already discarded \(p\mid P\), and hence \((A,P)=1\). The actual last exponent differs from \(u\) by at most \(\eta\). Divisors of squarefree \(r\) correspond to subsets; the cutoff exponent is \(1/2-20(\log L)/L\). Away from an \(O(\eta+\log L/L)\)-neighborhood of the finitely many walls this gives \(a(r)/L=F_j(x_1,\ldots,x_{j-1},u)+O_j(\eta)\). Use (1) for each fixed \(A\), and \(\log p\le L\); the resulting peeled-prime measure is \(\prod_{i<j}(\sum_{p_i}1/p_i)\), which converges weakly to \(\prod_{i<j}dx_i/x_i\) on this fixed compact exponent box by Mertens/PNT and rectangle approximation. Duplicates may be included for this nonnegative majorant, or omitted with negligible cost. The wall-neighborhood measure tends to zero as \(\eta\to0\), since all \(x_i\ge k>0\), \(u\ge k\), the walls are proper affine hyperplanes, and all weights are bounded for fixed \(j,k\). Taking \(P\to\infty\) first, then \(\eta\to0\), proves the integral over the face where the last exponent is largest, with denominator \(u^2\prod_{i<j}x_i\). Symmetrize over all possible maximal coordinates (ties have measure zero); the Lebesgue face chart is preserved by coordinate permutations. This proves (2).

## 3. Combinatorial bounds for the true signed weight

Put \(C_j=\binom{j-2}{\lfloor(j-2)/2\rfloor}\). For every increasing family of subsets of an \(m\)-set its alternating sum is at most \(\binom{m-1}{\lfloor(m-1)/2\rfloor}\) in absolute value (\(m\ge1\)). Indeed its fractions of members at successive ranks are nondecreasing by sampling a random maximal chain. Sum by parts against the binomial coefficients; the alternating binomial tail starting at rank \(t\ge1\) equals \((-1)^t\binom{m-1}{t-1}\). Expanding \(x_S\) as the sum of its coordinates and applying this to subsets of \(j-1\) coordinates gives \(|F_j|\le C_j\).

For even \(j\ge2\), a set and its complement have equal parity and exactly one lies above the midpoint; the sum of the signs over the upper sets is zero. Consequently
\[
 F_j=\tfrac12\sum_{S\subseteq[j]}(-1)^{|S|}|x_S-1/2|,
 \qquad |F_j|\le C_j\min_i x_i.
\]
For the inequality pair terms differing in a smallest coordinate of length \(b\), and integrate the derivative of the absolute value along that coordinate. At almost every integration position the alternating sum of signs of the arguments is twice an increasing-family alternating sum on \(j-1\) coordinates (the constant term cancels). This proves the displayed bound.

For odd \(j\ge3\), \(\sum_S(-1)^{|S|}x_S=0\) and complementary pairs have opposite parity; hence \(F_j=\tfrac12\sum_{x_S>1/2}(-1)^{|S|}\). In particular, if \(N_b\) counts the \(b\)-sets above half, \(F_7=10-N_1+N_2-N_3\).

As optional low-rank geometry, \(F_3=1\) when all coordinates are less than half and \(F_3=0\) when one exceeds half. With coordinates now sorted decreasingly, \(F_4=0\) for \(x_1>1/2\); otherwise its three large pairs are 12, 13, and the larger of 14 and 23. Subtract the three-fold subsets' total mass and add the four-fold mass to obtain \(F_4=-\min(1-2x_1,2x_4)\le0\). Finally \(F_5=-3-N_1+N_2\). Two above-half pairs intersect, and any intersecting family of four distinct pairs on five points is a star: if a third edge misses the joint vertex of the first two it completes a triangle, which admits no fourth edge meeting all three. Thus \(F_5>0\) holds exactly when \(x_1<1/2<x_1+x_5\), and there it equals one. Shapes tested using the actual exponents \(\log p_i/\log r\) have the same negligible boundary costs as in §2.

## 4. Exact upper cubature, not numerical evidence

For \(8\le j\le12\), take \(c_j=C_j\) for odd \(j\), \(c_j=C_j/j\) for even \(j\). Since \(\max x_i\ge 1/j\), \(\prod_i x_i\ge k^{j-1}(1-(j-1)k)\) (the product attains its minimum at a vertex, by concavity of the sum of the logarithms), and the simplex volume is \((1-jk)^{j-1}/(j-1)!\), (2) yields the rational upper bound
\[
 T_j=\frac{4c_j}{1-(j-1)k}\frac{(1/k-j)^{j-1}}{((j-1)!)^2}.
\]

For \(j=6,7\), use the adjacent standard-library Python program [verify.py](verify.py). It executes the following finite upper bound using integers and exact rational numbers; run `python3 -O verify.py`. With \(K=64\), \(k=c/d\) in lowest terms, let \(a=d-jc,\ H=dK,\ h=a/H\). Write each \(x_i=(r_i+a z_i)/H\), \(r_i=cK+a b_i\), with integers \(b_i\ge0\) and \(0\le z_i<1\). Put \(l=K-\sum b_i\); except for zero-measure boundary cells, \(1\le l<j\). Sort the bins decreasingly and multiply by their exact permutation multiplicity. The volume for each ordered bin vector is
\[
 \frac{h^{j-1}}{(j-1)!} E(j,l),\qquad
 E(j,l)=\sum_{i=0}^{l}(-1)^i\binom ji(l-i)^{j-1}.
\]
This follows by inclusion–exclusion on cube upper bounds in the simplex \(\sum z_i=l\), using its \(j-1\)-coordinate chart. The program checks that the summed volume equals the full simplex volume (in integer units the enclosures sum to \(K^{j-1}\) before multiplication by the common volume factor).

For rank six, cancel the minimum factor in the integrand via \([F_6]_+\le6\min_i x_i\); the kernel on a sorted bin is at most \(6H^6/(r_1\prod_{i=1}^5 r_i)\). Removing the last sorted-bin index is safe even for tied bin endpoints, because the ordered coordinates always dominate their sorted lower endpoints. For rank seven bound \([F_7]_+\) by \(\max(0,\min(10,10+N_2^{\rm possible}-N_3^{\rm certain}))\): a pair sum is at most \((r_i+r_m+a\min(l,2))/H\); a triple sum is at least \((r_i+r_m+r_t+a\max(0,l-4))/H\). The denominator \((\max x_i)\prod x_i\) is at least \((r_1+al)\prod r_i/H^8\), by \(\prod(1+a z_i/r_i)\ge1+al/r_1\) and \(\max x_i\ge r_1/H\). Each kernel bound is rounded UP to an integer before multiplying by the exact volume. There are 106,955 and 276,050 sorted cells respectively. The checker enforces the strict rational comparisons
\[
 U_6^{\rm upper}<0.259,\qquad U_7^{\rm upper}<0.172,
 \qquad \sum_{j=8}^{12}T_j<0.018,
 \qquad U_6^{\rm upper}+U_7^{\rm upper}+\sum T_j<0.448.
\]
The last comparison uses the exact sum, not the three truncated decimal upper bounds. Doubling proves the theorem.

Only the upper bound in the rank-profile integral used asymptotics, with fixed dimension and a fixed positive roughness exponent; the cubature is finite and exact. Neither the divisor-bounded progression transfer nor Pan's first-order main identity is assumed for this signed physical bound. Its remaining gap to a global Goldbach estimate includes all the classes excluded at the start, independently of whether an unusual modulus packet can be estimated.

For comparison, [Arneth's September 2026 Gold-12 preprint](https://zenodo.org/records/23016346) identifies adverse five-factor states for a different prime-filter coefficient and studies compensation at a fixed even target. [Chan's November 2026 preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) integrates sign-sensitive factor regions in a modified Chen weight, rather than in the literal Pan coefficient. Here the explicit constant counts raw prime-versus-composite terms from Pan's cutoff; neither related construction supplies an estimate for the remaining terms of this theorem.
