# Maximal spread of paired binomial moment bases is nondecreasing

For even k=2m, let Msp(n,k) be the largest difference between the greatest and least *nondistinguished* sites in a basis supported on a positive-length phase as p ranges through (0,1). In the notation of Berend–Ernst–Kontorovich–Kumar, [§5.5, Conjecture 5.12](https://arxiv.org/pdf/2407.18688), Msp(n+1,k)≥Msp(n,k), for all n≥k+1. No basis-by-basis inclusion, fixed-p monotonicity, frequency, or formula for all k is asserted. The case k=2 has constant spread one. If the trivial boundary n=k is appended to the domain, its k nondistinguished sites are consecutive and have the smallest possible spread k−1.

## Proof

Use the [paired basis and interior quadrature characterization](../k-wise-binomial-optimal-bases/PROOF.md): putting N=n−1, a feasible paired support of k nondistinguished grid sites in {0,…,N} carries a nonnegative quadrature for Bin(N,p) through degree k−1, after removing the distinguished site n. A positive-length phase has some interior p with strictly positive weights on every one of its k sites. The finitely many closed phase intervals cover (0,1); thus every p lies in the closure of a positive-length phase with nonnegative quadrature there. We use only these existing facts about the moment problem.

Take m≥2 and any positive-length old phase. Let A and B be the smallest and largest starts among its adjacent pairs; A+1<B and B+1≤N. Let G be the product of (x−a)(x−a−1) over all intermediate starts a (empty product one), and put Q(x)=(x−A−1)(x−B). Write F=GQ, of degree k−2. At integer sites G is nonnegative. For z>0 define

    f_N(z)=Σ_(x=0)^N binom(N,x)F(x)z^x,     D=z d/dz,
    U_N=(D−A)f_N,                           V_N=(D−B−1)f_N.

At odds z₀=p/(1−p) of a strict old phase witness, the degree-(k−1) quadrature gives U_N(z₀)>0, since on its support (x−A)F vanishes except for the strictly positive value at B+1. Similarly V_N(z₀)<0 since (x−B−1)F vanishes except for the strictly negative value at A. In particular (B+1−A)f_N(z₀)=U_N(z₀)−V_N(z₀)>0.

The coefficient of z^x in U_N has sign given by (x−B)(x−A)(x−A−1)G(x), which is nonpositive for x≤B and nonnegative for x>B. Hence z^(−B)U_N is nondecreasing for z>0, term by term. This implies U_N(z)>0 for z≥z₀. For V_N the coefficient sign comes from (x−A−1)(x−B)(x−B−1)G(x), nonpositive for x≤A+1 and nonnegative above. Hence z^(−A−1)V_N is nondecreasing, so V_N(z)<0 for z≤z₀. Now the derivative signs of z^(−A)f_N and z^(−B−1)f_N are the signs of U_N and V_N, respectively. Starting from f_N(z₀)>0 and moving right using U_N or left using V_N yields f_N(z)>0 on all positive reals.

For the very same polynomial F, binomial degree elevation gives

    f_(N+1)(z)=(N+1)∫₀¹ t^N f_N(z/t)dt + F(N+1)z^(N+1).

Indeed coefficientwise the integral multiplies binom(N,x) by (N+1)/(N+1−x). The integral is well defined also at t=0 by continuity of each monomial. The final coefficient F(N+1) is positive (at least nonnegative suffices) since it is above all old nodes. Thus f_(N+1)(z)>0 everywhere on (0,∞).

Choose any c strictly between A and B+1. The function z^(−c)f_(N+1)(z) tends to +∞ at both endpoints of (0,∞): the coefficients at sites A and B+1 are strictly positive and all coefficients at sites below A or above B+1 are nonnegative. Select an interior minimum z*. At that point Df_(N+1)=c f_(N+1), giving U_(N+1)(z*)>0 and V_(N+1)(z*)<0 with the same thresholds as before. In any nonnegative degree-(k−1) quadrature for Bin(N+1,z*/(1+z*)), positivity of U forces a site x>B because its defining polynomial is nonpositive on all integer x≤B; negativity of V likewise forces a site x<A+1. Select a closed positive-length phase whose quadrature works at this parameter. Both witnessed sites belong to its paired support, whose spread is therefore at least B+1−A. This is the old phase's spread. Taking the maximum over the old phases proves the inequality.
