# An unconditional mean-square theorem for the central Goldbach kernel

**Status and scope.** This is a consequence of unconditional linear-forms asymptotics for the actual primes. It concerns the *whole central integral operator*, not merely one quadratic form, and includes an exact variance for every fixed finite local model. It does not estimate the maximum over targets, and it proves neither binary Goldbach nor Li–Liu's full-operator hypotheses S or R. No claim of priority for the underlying almost-all theorem or this formulation.

## 1. Kernel and result

Put J=[log(1/3),log(2/3)]. For s,t∈J write x=exp(s), y=exp(t). If x+y>1 set

    F_{st}(u) = sqrt(u(1−u)) · 1_{[1−y,x]}(u),       m_{st}=∫ F_{st}(u) du.

If x+y≤1 put both equal to zero; this choice on a codimension-one boundary does not affect any operator below. For a bounded Riemann integrable f supported on [1/3,2/3], write

    A_N(f) = (1/N) Σ_{p+q=N} (log p)(log q) f(p/N)       (ordered prime pairs).

Let β_p(N)=p/(p−1) if p|N and β_p(N)=1−1/(p−1)² otherwise. Let S_Y=∏_{p≤Y}β_p and S=∏_p β_p be the truncated and full local densities, with Y≥2. Both vanish for odd N. Define

    W_N(r)=exp(−2r/log N)+exp(−r/4),
    H_N(s,t)=2π sqrt(W_N(log N+s)W_N(log N+t))/(xy),
    H(s,t)=2π exp(−2)/(xy),       C(s,t)=H(s,t)m_{st}.

The H_N are uniformly bounded and converge uniformly to H. For M=S or S_Y, define the symmetric real kernel

    B_N[M](s,t)=H_N(s,t)[ M(N)m_{st} − A_N(F_{st}) ]

on L²(J,ds). For odd N sufficiently large this is identically zero, since there are no central prime pairs then. With Λ and the restriction (p q,N)=1 in place of prime weights, B_N[S] is the central arithmetic kernel obtained from the odd-character projection and the continuous sum model in [Li–Liu](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) by inverse Laplace transformation and restriction to log(N)+J. Equivalently this displayed formula defines the operator without any Dirichlet GRH. The arithmetic normalization can be checked directly: on putting X=Nx, Y'=Ny, the cumulative continuous numerator is S(N)∫_{N−Y'}^X sqrt(v(N−v))dv; the discrete numerator replaces integration by ΣΛ(n)Λ(N−n)sqrt(n(N−n)); division by XY' gives exactly the two terms above before multiplication by the strip factors. Identification with the central compression of the *full* analytically continued Hardy operator is conditional on the construction of that operator, and is not an input here.

Use the all-integer dyadic average E_X h=X^{-1}Σ_{X<N≤2X}h(N), X a positive integer. Write

    V_Y=∏_{p≤Y}(1+(p−1)^(−3)),        V=∏_p(1+(p−1)^(−3)).

**Theorem.** Unconditionally, for each fixed Y≥2,

    lim_{X→∞} E_X ||B_N[S_Y]||_HS² = (V−V_Y) ||C||_HS² ,
    lim_{X→∞} E_X ||B_N[S]||_HS²   = 0.                         (1)

The limits restricted to even N, with the even-target average normalized to one, are respectively twice the first value and zero. Formula (1) also holds for the coprime von Mangoldt kernel on even N. In particular, for every fixed ε>0 the number of even X<N≤2X with positive spectral endpoint larger than ε S(N) is o(X). The conclusion is simultaneous over unit test vectors because the operator norm is dominated by the Hilbert–Schmidt norm. As a pointwise-in-N baseline, standard upper-bound sieving gives ||B_N[S]||_HS ≪ S(N) on all sufficiently large even N (see §4); (1) saves an arbitrary *fixed* constant in density, not on every target.

## 2. The scalar covariance

For each of our test functions f, let m_f=∫f. Then

    lim E_X A_N(f)² = V m_f²,     lim E_X A_N(f) S_Y(N) = V_Y m_f ,
    lim E_X S_Y² = V_Y.                                                (2)

Here f is real. In the square, the forms in the three variables (N,n_1,n_2) are n_1,N−n_1,n_2,N−n_2. They have Cauchy–Schwarz complexity at most one: for a form n_i partition the others into all reflected forms and the other unreflected forms. The linear span of neither class contains n_i. Interchanging reflected and unreflected pairs gives the other cases. Hence the unconditional complexity-one case of [Green–Tao, Linear equations in primes](https://annals.math.princeton.edu/2010/171-3/p08) applies. Weighted prime indicators in place of Λ change the normalized triple sum by o(1), since each proper prime power value admits O(X²) triples and there are O(sqrt(X)log X) such values; the normalization is of order X^3 and the logarithmic weights are harmless.

To see the archimedean factor carefully, write N=Xv and n_i=Xz_i: the factor 1/N² becomes X^(-2)v^(-2). For each v∈(1,2], the integrals of f(z_i/v) both equal v m_f. Thus after the outer average the factor is m_f². Finite-complexity counts over boxes imply the weighted version by upper and lower Riemann step functions on a fixed bounded region (use positivity; split signs if needed). At p, first condition on N=r mod p. A uniform n_i independent of the other n_j survives the two nondivisibility tests with local prime-normalized factor β_p(r). Averaging over r gives the local density E_r β_p(r)² = 1+1/(p−1)^3; this uses E_r β_p(r)=1. The product converges absolutely. This proves the first line of (2) for the square.

For the mixed moment put W=∏_{p≤Y}p, fixed before X→∞. Split (N,n) into residues modulo W, substitute N=Wh+r and n=Wk+a, and apply the same prime-forms theorem to the two nonparallel forms n,N−n. Alternatively use the prime number theorem in each fixed progression independently for the two prime summands and integrate in their sum. For fixed r, after averaging over a, the small-prime factor is S_Y(r). No further local factor remains since the mean of β_p over r is one for p>Y. Thus E_X A_N(f) S_Y(N) → m_f · E_{r mod W} S_Y(r)^2. The last mean is V_Y by the Chinese remainder theorem. The unweighted finite-period mean E_X S_Y² has the same limit, completing (2).

For clarity, use of a residue-r conditional density here does not assert an asymptotic for a *fixed integer* N; it averages N throughout a dyadic interval in the entire residue class.

## 3. Restoring the full local density and integrating the kernels

In the dyadic mean-square seminorm, S_Y tends to S. One elementary justification is to write, for even N,

    S_Y(N)=2 C_Y ∏_{2<p≤Y, p|N}(1+1/(p−2)),
    C_Y=∏_{2<p≤Y}(1−1/(p−1)²),

and similarly for S with Y infinite. To justify convergence, put L_Y=∏_{2<p≤Y,p|N}(1+1/(p−2)), L the full divisor product. The positive square-products L² expand as Σ_{d|N} b(d), supported on odd squarefree d with b(p)=(1+1/(p−2))²−1. Since Σ_d b(d)/d<∞ and E_X 1_{d|N}≤2/d for d≤2X (zero otherwise), the mean-square tail is bounded by

    E_X (L−L_Y)² ≤ E_X [L²−L_Y²] ≤ 2 Σ_{d with some p|d, p>Y} b(d)/d → 0,

uniformly in X. Also E_X L² is bounded, C_Y tends to its positive limit, and the even indicator is bounded. This proves the asserted mean-square convergence. By (2),

    lim E_X |A_N(f)−m_f S_Y(N)|² = (V−V_Y)m_f².
    lim E_X |A_N(f)−m_f S(N)|²   = 0,                           (3)

the latter by the L² triangle inequality and Y→∞. This calculation identifies the *entire* fixed-Y variance, not just an upper bound.

Apply (3) to f=F_st for almost every (s,t)∈J². The averaged integrands are dominated by a constant independent of s,t and X: H_N is bounded, |F_st|≤1_[1/3,2/3], and the averaged square of A_N(1_[1/3,2/3]) is bounded by (2). The averaged squares of S and S_Y are bounded as above. Uniform convergence H_N→H, Fubini, then dominated convergence on J² give (1). The limiting shape C is not the zero kernel.

Finally, there are O(sqrt(N)log N) proper prime powers ≤N, and for each summand at most one partner. Their normalized contribution to any of these interval weights is O(N^(−1/2)log³ N), uniformly in the interval. When both summands are prime, the only case lost to the coprimality restriction is p=q=N/2 prime, costing O(log² N/N). Both estimates vanish even without averaging. For even targets S(N)≥2∏_{p>2}(1−1/(p−1)²)>0, so Markov's inequality and ||B||_op≤||B||_HS finish the stated density consequence.

## 4. What stops the pointwise argument

On individual N use the classical pointwise upper-bound sieve g(N) ≪ S(N)N/log² N for the number of ordered prime pairs, for instance Theorem 1.2 in [Lichtman, Primes in arithmetic progressions to large moduli, and Goldbach beyond the square-root barrier](https://arxiv.org/abs/2309.08522) (the sharp constant is unnecessary). Consequently A_N(1_[1/3,2/3])≪S(N) and the bounded-kernel estimate in §1 follows. This does not suffice for the desired positive margin.

No density-one limit, even for the whole operator, excludes one exceptional target per arbitrarily many scales. More precisely an individual N fixed in §2 changes the independent affine forms n,N−n from a complexity-one averaged system into a pair with proportional linear parts in the remaining variable n. This is exactly where the linear-forms theorem stops applying. Neither the positive limit for a finite wheel nor the zero limiting full variance supplies a quantitative nontrivial pointwise estimate at that step.
