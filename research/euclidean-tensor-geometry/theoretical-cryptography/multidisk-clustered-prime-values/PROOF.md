# Root-disk bounds for prime polynomial values at clustered arguments

## 1. A length-uniform public promise

For n>=2 write L=bitlength(n). Fix a positive integer r independent of L. A deterministic public rule, evaluated on L alone, supplies:

* a catalogue C_L of monic integer polynomials of positive degree, encoded as dense coefficient lists, with total dense bit size and construction time polynomial in L (in particular every degree is polynomial in L);
* r integer centers A_1,...,A_r of bit length polynomial in L, and nonnegative integers R,W polynomial in L as **values**.

Every complex root of every catalogue polynomial lies in at least one closed disk |z-A_j|<=R. Disks may overlap. This is a public catalogue condition, not information about any hidden prime. Set A_max=max_j A_j.

For the factorization n=prod_i p_i^{e_i}, the promise is that each *distinct* prime p_i has an integer witness x_i with x_i>=2 and x_i>=A_max+R+2, and a polynomial F_i in C_L such that F_i(x_i)=p_i; all witnesses together have max_i x_i - min_i x_i <= W. There is no restriction on reuse of polynomials, on their individual degrees beyond the total encoded size, on the number of prime factors, or on positive multiplicities. No witness or independently supplied information about n is input. Factors equal to values, not merely divisors of values, are required.

**Theorem.** The entire prime factorization of every promised n can be computed deterministically with a number of bit operations polynomial in L. Membership in the stated promise class can also be decided in that time. No claim is made about the difficulty of integers not satisfying the promise.

## 2. A one-sided root envelope independent of factor count

Write a=min_i x_i, b=max_i x_i. For every root z of F_i, including multiplicities, choose one covering disk and denote its center by A_j. An arbitrary choice suffices if more than one disk covers z; no assignment is supplied or computed. As x_i-A_j>=R+2, the triangle and reverse triangle inequalities give

  x_i-A_j-R <= |x_i-z| <= x_i-A_j+R.

Let E_j be the combined count for center j of the chosen assignments, over all F_i and repeated e_i times. Then E=sum_j E_j=sum_i e_i deg F_i is positive. Monicity and positivity give n as the product over the root distances, with the corresponding multiplicities. In particular n>=2^E, so E<=L. For a nonnegative vector E define

  G_E(t) = product_j (t-A_j)^{E_j}.

Then G_E(a-R)<=n<=G_E(a+W+R). Moreover G_E is continuous and strictly increasing for t>A_max because all bases are positive and at least one exponent is positive. For the true vector, the level G_E(z)=n therefore has a unique real root z>A_max in [a-R,a+W+R]. Every true x_i is within R+W of z. Nothing here presupposes that the prime values themselves are close or that the disk centers are small as values.

The fixed r assumption is for enumerating the aggregate counts, not for the number of prime factors. The common right-hand side is essential to this monotone argument; it covers no intervals between disk centers. A separate mirrored left-hand version follows by replacing all coordinates by their negatives and each monic polynomial F(X) by (-1)^deg(F) F(-X), with the corresponding positive absolute-value promise and transformed half-line. No left or interior case is needed below.

## 3. Exact locating windows and verification

Enumerate nonzero vectors of nonnegative integers E_j with sum<=L, at most (L+1)^r. For each use exact integer comparisons of G_E(t) to n to find
  u=max{integer t>A_max : G_E(t)<=n},
skipping an empty set. The search is bounded above by A_max+n+1 since there every base is >=n+1 and the total degree positive. On the true vector the set is nonempty, since a-R>=A_max+2 and G_E(a-R)<=n. Its u satisfies u<=z<u+1. Enumerate all integers in [u-W-R-2,u+W+R+2] that satisfy the public witness lower bounds. Section 2 shows that every true witness occurs among the candidates for one vector. This uses integer binary search, not approximate root finding.

Each search integer and each center has polynomial bit length in L, so a comparison with degree sum<=L uses polynomial bit sizes. There are O((L+1)^r(R+W+1)) candidates. Evaluate every catalogue polynomial at each candidate by exact Horner arithmetic; its degree and coefficient bit lengths and the argument bit length are all polynomial in L. Test only positive values >1 and <=n for primality deterministically, discarding composite, nonpositive, unit and oversized values. Collapse duplicate primes as candidate factors while preserving all their witnessed bases. There is no degree-zero factor. Exact division extracts every multiplicity of all the candidate primes dividing n. If a nonunit residual remains, the input was not promised; if none remains, the factorization obtained is correct, even if the input fails the clustering promise.

For exact membership check, take each retained witnessing base of an actual extracted prime as a candidate left endpoint of an interval of length W. Check whether that interval has at least one retained witness for each extracted prime. A true input has a retained witness at its true minimum, so is accepted. Conversely a passing interval directly supplies witnesses for every prime. There are polynomially many endpoints and bases to inspect. The integer 1, if desired, is an empty factorization and can be kept outside this nonempty promise. The checkers verify finite mathematical examples and do not implement an input-taking recovery procedure.

The public condition on the disks can be checked by standard exact real algebraic decision in two variables: for each F test whether Re F(u+iv)=Im F(u+iv)=0 and (u-A_j)^2+v^2>R^2 for all j has a solution. The equations have polynomial degree and bit sizes (expanding the real and imaginary parts adds only binomial coefficients), and the number of variables is fixed. The proof itself does not even need the assignments of individual roots to disks.

As a single-disk corollary take r=1,A_1=0 and relax the witness promise to all x_i>=2, still clustered. If any true witness is <=R+1, all are in the public interval [2,R+1+W]; include that interval unconditionally in the evaluation candidates. Otherwise the general proof applies as stated. Thus the relaxed one-disk result follows without inferring an invalid degree bound in the small case. For this corollary G_E(t)=t^E and u is the usual exact integer root.

## 4. Cyclotomic indices with no supplied upper bound

Take the same clustered integer-witness promise with F_i=Phi_{m_i} for m_i>=3, except that now *no upper index limit* is specified. Every Phi_m is monic and its roots have modulus one.

For integer x>=2, the standard Mobius product identity gives

  Phi_m(x)/x^{phi(m)} = product_{j|m}(1-x^{-j})^{mu(m/j)} > 1/4.

Indeed negative exponents contribute factors above one, and the rest is bounded below by the full product prod_{j>=1}(1-2^{-j}). This exceeds 1/4: retain j=1,2 separately and use prod_{j>=3}(1-2^{-j}) >= 1-sum_{j>=3}2^{-j} = 3/4. This classical bound, in a stronger two-sided form, is attributed in UPSTREAM.md. It also holds for m=1, and excluding value 1 is part of the arithmetic promise.

Thus log2(p_i) >= phi(m_i)-2 at every true witness including x_i=2. Let Omega(n)=sum_i e_i. From multiplication, E=sum e_i phi(m_i) <= log2 n + 2 Omega(n) <= 3L. Also phi(m)^2/m >= 1/2 for every m: apply the prime-power formula, whose factor at p^a is p^{a-2}(p-1)^2, at least one except when p^a=2, which contributes exactly one half. Therefore m_i <= 2 phi(m_i)^2 <=18 L^2. One may even obtain a smaller individual bound using log2(p_i), but the displayed cutoff suffices. The argument bounds the unseen indices without evaluating phi at n. Now use C_L={Phi_m: 3<=m<=18 L^2}, R=1 (retaining indices 1 and 2 as intermediate factors when constructing the catalogue). The dense catalogue can be constructed by increasing m using exact monic division in the identity X^m-1=prod_{j|m} Phi_j(X). The division is exact by the partition of m-th roots according to their order; all degrees are polynomial, and root modulus one bounds coefficient bit length of all true factors/products by O(m). Long division with those bounded sizes and integer bit arithmetic takes polynomial time. Nothing requires the original values to have known cofactorization.

The single-disk small-argument branch is important: if any x_i=2, each lies in [2,2+W]. We do not claim that the E<=L estimate from the large-argument branch holds there. The weaker E<=3L bound is used only to construct the catalogue cutoff; no enlarged root-search exponent parameter is necessary.

## 5. Examples and boundary of the analogy

A two-disk fixture uses centers -100 and 100 and radius one. The three polynomials X-101, X+100 and X^2-9999 have witness evaluations 3 at 104, 211 at 111 and 1237 at 106, respectively. All three are prime, the true width is seven, and the quadratic uses both disks. With multiplicities (2,1,3) the aggregate counts at (-100,100) are (4,5).

At a common argument x=4, the indices 4,6,8,12,16 give respectively 17,13,257,241,65537. These are distinct primes of multiple degrees and differing scales; anything from an arbitrary subset and arbitrary multiplicities remains a fixed toy instance of the premise. At differing bases (2,3,4) one may use Phi_3(2)=7, Phi_3(3)=13, Phi_8(4)=257, illustrating the width-two case with an actual small endpoint. These examples do not assert infinitude of prime values or densities for the promise.

One may allow indices 1 and 2 in addition without changing the proof: at x=4 they give 3 and 5, and for general x they are simply x-1 and x+1, so the requirement of being an evaluation alone would be trivial without the cluster promise. A one-prime instance can also be a prime power. These boundaries are not the claimed breadth of the corollary, which allows arbitrary mixes of indices >=3 and arbitrary multiplicity.

The method relies on evaluating a known polynomial, then certifying the value is the prime itself. It does not factor a composite catalogue value by examining the polynomial's roots. For example the single monic polynomial X-1 at the unrestricted argument n+1 takes the value of any positive n, so allowing arbitrary composite factors as evaluation values would erase the promise. The theorem is not about arbitrary primes dividing Cunningham integers, nor about a particular cryptosystem. It is a uniform positive complexity result for a specified arithmetic class.
