# The exterior singular spectrum of two complementary Hamming balls

All logarithms here are natural. Write H for the normalized one-bit real Hadamard and Z=diag(1,−1). In the binary n-cube let P_a project onto computational coordinates of weight at most a. The object is the full operator
`M_n(a,b)=P_a H^{⊗n} P_b`. Its norm is also that of the product of the computational and Hadamard ball projectors. Two independently translated ball centers give the same singular values: a computational translation and a modulation implement the row/column translations of the Walsh kernel up to row and column signs. We analyze a central pair without loss.

This note starts from the known Terwilliger blocks and known radial Krawtchouk tail exponent (see [SOURCES](SOURCES.md)). The additions are a sharp norm prefactor, the leading full-cube singular spectrum, and an explicit finite-block refinement of the Beigi–Tomamichel bound. No full-game exponent is inferred.

## 1. Parameters and theorem

For `0<p,q<1/2` with `(1−2p)^2+(1−2q)^2>1`, set

    α=1−2p,  β=1−2q,  Δ=sqrt(α²−4q(1−q)),
    z=2q/(α+Δ),   h(t)=−t log t−(1−t) log(1−t),
    R(p,q)=−log(2)/2+(h(p)−h(q))/2
            +p log(1−z)+(1−p) log(1+z)−q log z,
    A(p,q)= (1/2) log((1−p)/p) + log((1−z)/(1+z)),
    B(p,q)= (1/2) log(q/(1−q)) − log z,
    D(p,q)= (1/2) arcosh(cosh(A)cosh(B)),
    σ²(p,q)=zΔ/(1−z²),   χ(p,q)=[q(1−q)/(p(1−p))]^(1/4).

All A,B,D,σ² are strictly positive. For fixed p,q in this region put a=floor(np), b=floor(nq), p_n=a/n, q_n=b/n; for n large both are positive. Below A,B,D without an argument are evaluated at p,q. Define

    C_n = χ(p_n,q_n) exp(n R(p_n,q_n)) / sqrt(2π n σ²(p_n,q_n)),
    L   = [(1−exp(−2A))(1−exp(−2B))]^(−1/2).

**Theorem.** For any fixed such p,q,

    ||M_n(a,b)|| = C_n L (1+o(1)).                                      (1)

In particular, the floor dependence inside the exponential is retained. More generally, for any fixed integer J≥0, eventually the largest J+1 distinct singular values come from the top singular value in each respective spin-defect sector r=0,…,J. The value in sector r is

    C_n L exp(−2rD) (1+o(1)),   exact multiplicity binom(n,r)−binom(n,r−1).    (2)

The top value is therefore eventually simple and attained in the radial sector only. The reversed, zero-padded block in each fixed r converges after dividing by C_n, in Hilbert–Schmidt norm, to the rank-one matrix with (i,j) entry exp(−2rD−iA−jB), for nonnegative i,j.

Also, for every n≥1 and each strict-exterior cut with 0≤a,b≤n/2,

    ||M_n(a,b)|| ≤ exp(n R(a/n,b/n)).                                   (3)

On an axis use R(0,q)=(h(q)−log 2)/2 and R(p,0)=(h(p)−log 2)/2, with h(0)=0. The sharp prefactor and sector assertions above require strictly positive fixed radii in the strict exterior; the turning circle, interior, and moving approaches to them are not covered.

## 2. Exact block reduction (known; elementary derivation)

On the basis indexed by subsets S of [n], let Raising add one element in all possible ways and let Lowering be its adjoint. The commutator Lowering·Raising−Raising·Lowering equals (n−2k)I on weight layer k. For a unit vector w in the kernel of Lowering on weight r, put m=n−2r. Induction with the commutator gives
`Lowering·Raising^j w=j(m−j+1) Raising^(j−1) w`.
Its normalized ladder spans weights r through n−r and Raising has coefficients sqrt((j+1)(m−j)). Chains starting with orthogonal roots remain orthogonal: for roots at different weights, move the larger starting layer's raising powers to the other factor as lowering powers; the resulting positive power of Raising is orthogonal to a root. For equal starting weights the same calculation gives a scalar times the inner product of the roots. Raising is injective on each layer k<n/2 by the commutator norm identity, so the number of roots in layer r≤n/2 is binom(n,r)−binom(n,r−1), interpreting binom(n,−1)=0. Counting the ladder dimensions on layer k telescopes to binom(n,min(k,n−k))=binom(n,k); hence these ladders exhaust the space.

On each ladder the collective Z and collective X=(Raising+Lowering) act exactly as on the radial subspace of the m-cube, because Z acts there with eigenvalues m−2j and X has the same recurrence coefficients. Since iH=exp(iπ(Z+X)/(2sqrt(2))) on the one-bit space, the tensor power of iH has precisely the same ladder action as its m-bit radial counterpart. Removing i^n gives the harmless scalar (−1)^r. The row and column restrictions on block r are x≤a−r and y≤b−r. Empty blocks are omitted. Up to that sign, each block is a submatrix of the symmetric normalized Krawtchouk transform

    K_m(x,y)=2^(−m/2) sqrt(binom(m,x)/binom(m,y))
                    [w^y](1−w)^x(1+w)^(m−x).                           (4)

Indeed, summing the signed Walsh characters of all subsets of size y against a fixed x-subset gives the coefficient in (4); converting the two uniform weight vectors to unit norm gives the ratio of binomial coefficients in (4).

## 3. Local positive saddle asymptotic

Take x/m=p, y/m=q in a compact subset of the strict positive exterior. The small root z above solves
`q=z(α−z)/(1−z²)`. The two positive roots of (1−q)z²−αz+q=0 have product q/(1−q), so `0<z<sqrt(q/(1−q))<1`.
Also `q<1/2−sqrt(p(1−p))`, which implies
`sqrt(q/(1−q)) < z_c=(sqrt(1−p)−sqrt(p))/(sqrt(1−p)+sqrt(p))`.
In particular A,B>0. Differentiating the saddle objective with z stationary gives R_p=A and R_q=B.

On the circle of radius z the log modulus per coordinate of the numerator in (4) is
`[p log(1+z²−2z c)+(1−p)log(1+z²+2z c)]/2` at c=cos θ.
It is concave as a function of c. Its derivative at 1 is
`z[(1−p)/(1+z)^2−p/(1−z)^2]>0` by z<z_c. On our compact set the derivative at 1 has a common positive lower bound. Thus the modulus divided by its value at θ=0 is bounded by exp(−c₀ m θ²) for |θ|≤π, with c₀>0, using 1−cos θ≥2θ²/π².

For the coefficient integral divide its integrand by its value at θ=0. Choose the analytic logarithms since |z|<1 and subtract i q θ for the coefficient phase. The resulting log per coordinate G has G(0)=G'(0)=0 and
`G''(0)=−z ∂_z[z(α−z)/(1−z²)]=−z Δ/(1−z²)=−σ²`.
For the second equality subtract q inside the derivative and use the numerator αz−(1−q)z²−q, which vanishes at z. On compact sets the Taylor error is uniformly O(|θ|³). Under θ=s/sqrt(m), Taylor on bounded s and the Gaussian modulus bound on the rest give the ordinary real Gaussian integral, uniformly in p,q; the positive leading constant also fixes the eventual sign. Uniform Stirling on the two binomial coefficients in (4) gives

    K_m(x,y) = χ(p,q) exp(mR(p,q)) / sqrt(2πm σ²(p,q)) (1+o(1)).         (5)

In particular |K_m(x,y)|≤C m^(−1/2) exp(mR(p,q)) on each such compact set; finitely many smaller m can be absorbed into C. This is a single-entry result, not yet a statement about a matrix norm.

## 4. One-bit tilt and the exact finite upper exponent

For any A',B'≥0 set E=exp(A'Z/2) H exp(B'Z/2), D'=log||E||. The determinant of EE^T is 1 and its trace is 2 cosh(A')cosh(B'), so D'=(1/2) arcosh(cosh(A')cosh(B')). The diagonal weights on the low-weight spaces give

    ||P_a H^{⊗n} P_b||
      ≤ exp(nD'−(n−2a)A'/2−(n−2b)B'/2).                               (6)

For a single level pair x,y on the m-cube, exactly the same bound applies to each radial entry with n,a,b replaced by m,x,y; the outside diagonal factors are scalars on the individual weight layers. This entrywise bound holds at every x,y, including level zero.

Take A'=A(p,q), B'=B(p,q), and form the positive unit vectors l=(sqrt(1−p),sqrt(p)), v=(sqrt(1−q),sqrt(q)). The ratio of the second to the first component of E v is exp(−A)(1−z)/(1+z)=sqrt(p/(1−p)), since exp(−B)sqrt(q/(1−q))=z. For E^T l, put z'=exp(−A)sqrt(p/(1−p)); then

    (1−z')/(1+z') = (α−z)/(1−αz) = q/[z(1−q)].

The last equality uses α=q/z+(1−q)z. Multiplication by exp(−B) gives sqrt(q/(1−q)), as required. Thus E v=s l and E^T l=s v, with the same scalar s>0 by taking the inner products. The off-diagonal of EE^T is positive (B>0), so its positive eigenvector l has the largest eigenvalue, and s=||E||. In particular D>0. The first component of E v now gives

    D = −(1/2)log 2 + (A+B)/2 + (1/2)log((1−q)/(1−p)) + log(1+z).
    R = D−(αA+βB)/2.                                                   (7)

The second identity follows by substituting A,B, or by expanding h in the defining expression for R. For example the right side is
`−(1/2)log 2+pA+qB+(1/2)log((1−q)/(1−p))+log(1+z)`.
Substitute (7) in (6) with the actual normalized integer cuts to get (3). On an axis the matrix is rank one with norm squared `2^(−n) sum_{k≤max(a,b)} binom(n,k)`, and the ordinary binomial Chernoff inequality yields (3), including the (0,0) endpoint exactly.

Moreover, R(p,q) is the infimum of the right-hand exponent per coordinate in (6) at fixed p,q: it is attained by (7), and applying the single-entry version of (6) to integer x/m→p, y/m→q and then (5) shows R(p,q)≤D'−αA'/2−βB'/2 for *every* A',B'≥0. No minimax exchange or approximate optimizer is needed. The exterior exponent is strictly negative: for example along the trial tilt A'=tα,B'=tβ as t→0, D'=(t/2)sqrt(α²+β²)+O(t³), whereas the subtracted term is t(α²+β²)/2. Their linear difference is negative.

## 5. Uniform localization and full-cube singular hierarchy

In sector r reverse the indices and ignore the scalar (−1)^r, writing
`m=n−2r, x=a−r−i, y=b−r−j`. Zero-pad onto indices i,j≥0. Use the same corner tilt A_n=A(p_n,q_n), B_n=B(p_n,q_n) and D_n=D(p_n,q_n) for **all** r,i,j. Whenever the entry is present, `m−2x=n−2a+2i`, `m−2y=n−2b+2j`. Thus the single-entry bound of §4 gives

    |K_m(x,y)| ≤ exp(nR(p_n,q_n)−2rD_n−iA_n−jB_n).                    (8)

Choose one small fixed η>0. For r+i+j≤η n, the local (x/m,y/m) are inside a compact strict positive exterior neighborhood of (p,q) for all sufficiently large n; also m is at least a fixed positive fraction of n. There (5) gives an extra O(n^(−1/2)) multiplicative factor over exp(mR(x/m,y/m)). By the infimum property in §4, the latter exponential is at most the RHS of (8). For r+i+j>η n, simply use (8); after division by C_n the factor O(sqrt(n)) is absorbed by reducing the common strictly positive exponential decay constant. Consequently there exist C,c>0 depending on p,q only, such that for every sufficiently large n, all r,i,j satisfy

    |K_m(x,y)|/C_n ≤ C exp(−c(r+i+j)),                                 (9)

where absent entries count as zero. In particular tail bounds in r are uniform even when r grows with n.

For fixed r,i,j, as n increases the entry is present, and
`x/m=p_n−[(1−2p_n)r+i]/m`, `y/m=q_n−[(1−2q_n)r+j]/m`.
The linear Taylor expansion of R, with gradient (A_n,B_n), gives

    m R(x/m,y/m)=nR(p_n,q_n)−2rD_n−iA_n−jB_n+o(1)

by (7). The ratio of the two prefactors in (5) and C_n tends to one. Thus the pointwise limit after division by C_n is exp(−2rD−iA−jB). The squared version of (9) is summable in i,j, proving Hilbert–Schmidt convergence to the stated rank-one matrix. Its one nonzero singular value is exp(−2rD)L.

For completeness, the full spectrum follows rather than merely that of a permutation-invariant candidate. Equation (9) gives normalized operator norm ≤C' exp(−c r) uniformly in r, by the Hilbert–Schmidt bound on each block, not on their multiset union. For fixed J pick a larger fixed R₀ such that this bound for r>R₀ is smaller than exp(−2JD)L/2. Among r=0,…,R₀ the leading normalized singular values converge to a strictly decreasing list, and all second and later ones converge to zero in operator-norm comparison to rank one. Thus, for n sufficiently large depending on J,p,q, no value except the respective leading block singular values can reach the first J+1 positions in the list of distinct values. Each such value is simple within a block and repeated across exactly the binomial-difference multiplicity of its sector. This proves (1) and (2).
