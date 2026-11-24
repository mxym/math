# Tilted two-form Selberg sieve in the true middle strip

Research note, 2026-11-24, for **dyadic targets N=2^k, short cofactor cutoff mu=.02, and .20<=t<=.21**. The bound strictly improves the optimized ordinary two-form affine Selberg bound with the **same** cofactor cutoff. It does not improve the previous .06 or .07 true-rough P3 budget. The t endpoints refer to q at scale N^t, with the marked q kept prime throughout.

## 1. Statement

Let H=sqrt(N), L=log N, fix 0<a<b, I=(aH,bH], X=Li(bH)-Li(aH), and B=2 X S_N/L; for N=2^k, S_N is the standard twin-prime singular factor including 2. Write Q=N^t, with .20<=t<=.21, and use any nonnegative b_q<=1 on the primes Q<q<=2Q. For real powers in the following expressions write

    T=(.5−t)/2, V=(2/3)(.25−t), eta=.0005, mu=.02,
    A=T+(3/2)V−eta=.5−(3/2)t−eta.

Let D(u) denote Dickman's function (D=1 on [0,1], uD'(u)=−D(u−1) for u>1, zero for u<0). Define

    I_tilt= integral_0^infinity (A−(5/2)y)_+ D(y/mu) dy,
    I_aff = integral_0^infinity (T−y)_+ D(y/mu) dy.

Then

    sum_{Q<q<=2Q, q prime} b_q *
      # {p in I prime: p=N−q j, j integer, P^−(j)>=N^mu}
      <= [ 1/(4 I_tilt)+o(1) ] B sum_q b_q/q + O(N^(.5−eps0))

for some fixed eps0>0. In this display p is a true prime and j is the true cofactor, not its model replacement; every real row is covered by the resulting upper bound. The o term is uniform in t and weights, and the power-saving is absolute. One has

    I_tilt >= I_aff + .00019,

and 1/(4 I_aff) is the limiting normalized coefficient from the maximal ordinary affine two-form Selberg square (same true q and genuine j-rough cutoff). Thus the improvement is strict by a fixed positive factor in any dense dyadic block and under subsequent bounded prime-mark weights.

## 2. Allowed square support and actual remainder

Use the weighted row variables p=N−qj, with all integer j in the genuine p window. Corresponding to a divisibility monomial r0|p, s0|j, allow the generator support

    x+(5/2)y <= A, x=log r0/L, y=log s0/L.

The allowed support is downward under deleting primes. Squaring a sum of such generators produces p- and j-side LCM moduli r,s with exponents u,v satisfying

    u+(5/2)v <= 2A = 1−3t−.001.

Later small-prime exact pre-sieving multiplies each side by a factor N^o(1), which retains the fixed saving. For N even dyadic, odd primes cannot divide both p and j, because p+qj=N. Thus expanded monomials with a common odd prime on both sides are **identically zero on the actual sequence**, and are dropped. At 2 use only the p-side zero event, since q is odd and p,j have the same parity. Therefore every retained expanded pair has (r,s)=1 and s odd, in particular (s,N)=1; moduli are squarefree because powers of indicators are idempotent. All generator primes on either side are <=N^A<q uniformly, since A<=.1995<t. This remains true after assigning the tiny pre-sieve primes.

Apply the earlier prime-q Poisson–Weil argument on each dyadic r,s subblock, in its general exponent form. For fixed r,s coprime and q not dividing their product, p=rm and j=s n give exactly m=N r^(-1) mod qs. For a smooth window W(p/H), the mean is H integral(W)/(rqs), and the nonzero Poisson modes have phase e(hN r^(-1)/(qs)) with smooth amplitude H/(rqs)*hat W(hH/(rqs)). Partial summation separates the q,r axes at logarithmic-derivative cost, and the uniform joint remainder on a dyadic block of r~R, s~S is

    N^o(1)[R S Q^(1/2) + R^(1/2) Q^(3/2) S^(5/4)].

For specificity, this is from Cauchy in r and off-diagonal completion over r modulo s q1 q2, with h<q and squarefree odd s. The gcd loss (h(q2−q1),s)^(1/2) averages first over q pairs (q1−q2 divisible by a given divisor) and then h using sum_{h<=Y}(h,s)^(1/4) << Y s^o(1); see [the preceding joint Poisson–Weil proof](PrimeOppositeMiddleJointPoissonWeil.md). This is an absolute sum of q-aggregated errors, so r,s coefficients of either sign and fixed divisor powers are legal. For this application, even the largest u is <=.399+o(1)<.40<=2t, so r lengths are below q1 q2 s. The spectral Poisson scale has exponent u+v+t−.5 <=.5−2t−.001+o(1)<=.099+o(1), so a tiny power tail cutoff still keeps |h|<q. The other hypotheses s<=Q² and (s,N)=1 hold, since v<=.16+o(1)<2t and s is odd. The first output exponent is u+v+t/2<=1−(5/2)t−.001+o(1)<=.499+o(1), the second is (u+3t+(5/2)v)/2<=.4995+o(1). Dyadic blocks touching the support inequality can be rounded to their upper endpoints at an O(1/L) cost, and still power-save. There is no use of a prime upper after its signs have been changed.

One can take W_N to be a nonnegative smooth majorant of 1 on [a,b] by convolution of a lightly enlarged interval with a positive bump of width L^−2. It has integral b−a+O(L^−2), fixed compact positive support and fixed-order derivatives growing only as powers of L. W_N applies to every actual root including the half-open window endpoints.

## 3. Exact small-prime handling and the tilted Selberg polynomial

Let Z=L/(log L)^2, P0=product_{l<=Z} l, and z=N^mu. All small primes are below z. On the actual rows use the exact nonnegative factor

    C0(p,j) = (1−1_{2|p}) product_{2<l<=Z} (1−1_{l|p}−1_{l|j}).

This is the indicator of avoiding both forbidden roots (for l odd, at most one divisibility occurs). Expanding it assigns at most one color per small prime and coefficients are ±1; each new modulus multiplies its respective side by a divisor of P0=N^o(1). The literal expansions have at most 3^pi(Z)=N^o(1) terms, and large primes in the main sieve are disjoint from them. Thus this is not a conditioning step that discards congruence information or introduces an unpriced modulus. Prime 2 only ever enters r.

For l>Z use the p-side divisibility indicator and, when l<z, also the j-side indicator; their expectations in the complete local model are g_l=1/l. They are incompatible if both present; for l>=z only the p-side indicator is used. Marked q exceeds all primes used. Different local primes are independent in the model dictated by the CRT and the h=0 density 1/(rs). For each allowed labelled assignment a=(r0,s0), with squarefree disjoint sides and all primes>Z, let f_a be the product of its centered local indicators normalized to variance 1 (empty product 1). Put v_a=f_a(all local indicators zero), and

    G=sum_{a allowed} v_a^2,
    F=G^(-1) sum_{a allowed} v_a f_a.

Then F(0)=1, so C0 F² is a nonnegative majorant for all true p-prime, j-z-rough rows. The primality guarantee also uses p~H larger than every cutoff. This one square is evaluated by the true Poisson error; no product of unsigned prime-count bounds is inserted into an alternating cofactor sum.

The nonorthogonality correction is small for the **whole quadratic form**. Blocks with different unlabelled prime support are orthogonal, because at a prime appearing in only one support a centered local factor has mean zero. In each same-support block, the permitted labelled assignments form a principal submatrix of the tensor product of local covariance matrices. A one-label local matrix is (1). A two-label matrix has diagonal 1 and off-diagonal −1/(l−1): the shared prime divisibility events are mutually exclusive. Thus the spectrum of every block is between products of \(1-1/(l-1)\) and \(1+1/(l-1)\) for primes in that support. Principal submatrices have the same operator-norm bounds for their quadratic forms by padding coefficients with zeros.

Uniformly for an individual support of size at most N^C, the sum of 1/l over its l>Z primes is o(1). To see this, split at Z2=L(log L)^2: the entire prime sum in (Z,Z2] is o(1) by Mertens (log Z2/log Z→1), and the support-conditioned part l>Z2 is at most O(L/(Z2 log Z2)). Hence the eigenvalue bounds are 1+o(1), uniformly over every block. Summing orthogonal blocks yields for the full quadratic form

    E[F²] <= (1+o(1))/G.

This is not just term-by-term covariance control. Independence from the disjoint small-prime factor gives

    E[C0 F²] <= (1+o(1)) V0/G,
    V0 = product_{l<=Z}(1−nu_l/l),  nu_2=1, nu_l=2 (l odd).

The raw generator expansion is admissible for the arithmetic bound. At each active prime the local factor v_l f_l is exactly (g_l−I_l)/(1−g_l). For a fixed raw monomial whose assignment is b, the magnitude of its coefficient in F is at most product_{l in b}(1−g_l)^−1: after extracting those factors, the remaining positive coefficients of allowed extensions are a subset of the sum defining G by downward closure (delete the primes in b). Thus coefficients are <=2^omega(r0 s0). After squaring, the number of assignments of primes of any retained pair of LCMs to their two generators is at most 3^omega(rs), and the product of the two coefficient bounds is also at most a fixed divisor power. Small-prime prefactors cause only their N^o(1) overhead. Consequently the Poisson remainder from §2 remains a power-saving after the actual expansion, including all signed coefficients.

## 4. Exact leading term for G, with a short Dickman derivation

Write c_Z=product_{l<=Z}(1−1/l) and w(n)=mu_M(n)^2 product_{l|n}(l−1)^−1 for integers with all primes>Z, zero otherwise. Then v_a²=w(r0)w(s0) for disjoint assignments. Since all p-side primes that can occur in r0<=N^A are allowed, the p-side measure is unrestricted w; the j-side measure is w restricted to prime factors <z. We show

    G = (1+o(1)) c_Z² L² I_tilt.

Uniformly for 1<=U<=N, the unrestricted sum of w(n) up to U is

    c_Z log U + O((log Z)^C).

Indeed its Dirichlet series divided by zeta(1+s) has local factors (1+(l−1)^−1 l^−s)(1−l^−1−s) for l>Z, and (1−l^−1−s) otherwise. At s=0 the former have value 1, and their nonconstant coefficients are O(l^-2) (two degrees only). The excluded prime coefficients are −1/l. Hence the absolute log moments of the convolution partner are O((log Z)^C), and its signed sum is c_Z. Convolving with 1/n yields the assertion using the harmonic sum. This error is o(c_Z L). For fixed s0 an extra coprimality restriction in the p-side sum costs at most O(c_Z L) sum_{l|s0,l>Z}1/(l−1)=o(c_Z L) uniformly by the same support estimate as in §3. Summing over s0 preserves the o(c_Z² L²) error.

For the j side, removing primes >=z in the unrestricted w-sum by exact inclusion-exclusion uses only at most floor(y/mu) prime divisors for a cutoff N^y; y is in a fixed bounded range. The large prime variables are distinct, squarefree, and replacing their gcd conditions on the residual after factoring them out costs o(c_Z L), uniformly, since every such prime is >=N^mu and there are O(1) of them per tuple. In the tuple sum repetitions have negligible weight by sum_{l>=z}1/l²=o(1). Prime harmonic Mertens and the unrestricted sum just proved give the limiting j-side cumulative mass in units c_Z L as

    sum_{j>=0} (-1)^j/j! integral_{u_i>=mu, sum u_i<=y}
                                 (y−sum u_i) prod_i du_i/u_i.

This is a finite sum on each bounded interval, uniform by continuity of the integrals (or a fixed fine grid and the monotonicity of the cumulative measures). Its derivative equals D(y/mu). Indeed in unit-scaled variables x=y/mu, let J_j(x) be the same simplex integral without the leading x−sum. On the moving boundary sum u_i=x, the identity x J_j'(x)=j J_{j−1}(x−1) follows by inserting sum u_i and symmetry, cancelling one reciprocal in each term. Hence the alternating density is 1 on [0,1] and satisfies the Dickman delay equation thereafter. This proves j-side weak convergence against bounded continuous weights, without assuming distribution of rough j at the scale of the true short interval. Here the Dickman function appears **only in the Selberg denominator**, not as a hypothesis about the actual cofactor. Applying this to the p-side mass c_Z L (A−(5/2)y)_+ proves the formula for G.

Finally V0/c_Z²→S_N, by its factors 2 at the prime 2 and l(l−2)/(l−1)² at odd primes. Multiply the expected model upper by H integral(W_N) sum_q b_q/q, add the power error, and use B=(4+o(1))(b−a)H S_N/L². This gives the stated coefficient 1/(4 I_tilt).

## 5. Affine benchmark, strict gain and .06 limitation

In the optimal ordinary affine two-root Selberg square, the r,s labels are not separated in the generator and the square support is one product <=K², with supremal log_N K=T from the O(1) floor per fixed q. Its exact denominator is sum_{d<=K} mu_M(d)² product_{l|d} nu_l/(l−nu_l), with two roots below z, one above, and one at 2. Split the sum at Z. The small-prime divisor contribution is exactly V0^−1 after allowing a shift in the log_N cutoff of o(1), since all divisors of P0 are N^o(1). For l>Z, the weight for a possible two-label prime is 2/(l−2), whereas the two labelled weights sum to 2/(l−1); their factor ratio contributes 1+o(1) uniformly over each individual support by §3. The one-label factors are identical. Thus the same leading-term calculation gives the exact ordinary denominator L²(I_aff+o(1))/S_N, where the old shape is x+y<=T. Allowing a vanishing but fixed exponent shave in the literal affine error only weakens this benchmark. This compares the tilted shape to the exact optimal ordinary Selberg coefficient for that support, not just an older coarse lower bound on its denominator; it is not a universal impossibility statement about other sieve methods.

For the gain, the Dickman identity uD(u)=integral_{u−1}^u D(v)dv, with D(v)=0 at v<0, is obtained immediately from its delay equation and the initial interval. It gives integrability by factorial decay and, integrating in u, integral uD(u)du=integral D(u)du. Hence the full positive density D(y/mu) has mean mu, and the mean truncated to [0,T] is at most mu. Since a positive part is at least its argument, restrict the tilted integral to [0,T] to get

    I_tilt−I_aff >= integral_0^T [(3/2)(V−y)−eta] D(y/mu)dy
                 >= [(3/2)(V−mu)−eta] * integral_0^T D(y/mu)dy
                 >= [.01−.0005]*.02 = .00019.

Here t<=.21 gives V>=.026666…, and T>mu ensures the mass at least .02. The gain strictly lowers the actual normalized upper coefficient. For example I_aff<=.15²/2 implies at least a factor 1/(1+.00019/.01125)<.984 in the coefficient, even with this deliberately crude comparison.

For the particular larger mu=.06, tightening the same tilted family cannot help on .20<=t<=.21 (the numeric inequalities below work through .23). Put I(k)=integral [T+kV−(1+k)y]_+ D(y/.06)dy for 0<=k<=1.5, omitting an exponent shave only helps the upper comparison. This is convex in k, since positive part preserves convexity of affine functions. At k=1.5, D<=1 gives I(1.5)<=(.5−1.5t)²/5. At k=0, use D=1 for y<=.06 and D(y/.06)=1−log(y/.06)>=2−y/.06 on [.06,.12]. Since T>=.135, this gives I(0)>=.09 T−.0042. The latter bound exceeds (.5−1.5t)²/5 at t=.20 and .23 (differences .0013 and .003145), and hence on the whole interval by concavity of the difference. Convexity of I(k) then gives I(k)<=I(0) for the entire 0<=k<=1.5 family at .06. Also weakening the true .06 condition to the short .02 alone does not improve its old upper: even the maximum possible tilted denominator at k=1.5 and .02 is <=(.5−1.5t)²/5, already less than the .06 affine baseline. These are quantitative limits of this family and this short-cutoff substitution, not of other sieve shapes. Neither the positive result at .02 nor the comparison at .06 closes any unproved threshold for P3.
