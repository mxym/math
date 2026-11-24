# Small-prime Goldbach at the square-root source scale: a hybrid weighted P4 lower bound

**Status.** Research note, 2026-11-24. No priority claim. Real prime roots on a literal fixed-N interval. Unconditional Omega <= 4, not Omega <= 3, not Omega <= 2, and not Goldbach. The analytic ingredient beyond a plain Richert/BV calculation is a one-prime-marked switched upper sieve with different cutoffs on its two linear forms. No full-angle prime tuple asymptotic is used.

## Statement and notation

Fix real 0<a<b. For every sufficiently large even N, put H=sqrt(N), L=log N, I=(aH,bH], H0=(b-a)H and X=Li(bH)-Li(aH)=(2+o(1))H0/L. Put

    S_N = 2 product_{l>2}(1-1/(l-1)^2) product_{l>2,l|N}(l-1)/(l-2),
    B = 2 X S_N / L = (4+o(1)) H0 S_N / L^2.

There are >= (3/40)B + o(B) distinct actual primes p in I for which N-p is squarefree, has no prime divisor < N^(1/20), and Omega(N-p)<=4. The same order survives if, for a sufficiently small fixed delta>0, one also deletes rows with two factors >N^(1/2-delta), or a ratio <=N^delta between two distinct factor primes when rank >=3 (by the earlier angular estimates; see §7). All o-terms are uniform in N, with a,b fixed.

Let A be the multiset of literal m=N-p, p prime in I, p not dividing N. This excludes at most O(log N) source primes. In the following d0=249/1000, mu=1/20, beta=3/10, T=11/50, D=N^d0, z=N^mu, y=N^beta. The normalized conditional counts are for m of A that are z-rough and divisible by a prime q, and t=log q/L. Define

    eta=5-1/beta=5/3,
    w(m)=1-eta^(-1) sum_{z<=q<y, q|m} (1-log q/log y).

For squarefree m<=N with P^-(m)>=z, the summand total is at least Omega(m)-log m/log y: extend the summation to all q|m, adding only nonpositive summands. Hence w<=0 when Omega>=5, and always w<=1. A positive lower bound for the signed w-sum on squarefree m yields the same (unweighted) lower bound for Omega<=4. This is the usual Richert device, not a new weight.

## 1. Prime-root lower bound and supported small marks

For any squarefree d, the reduced AP density is g(d), with g(l)=1/(l-1) for primes l not dividing N (so never l=2), g(l)=0 for l|N. For d coprime to N, the residue is N mod d. Bombieri–Vinogradov at p~H gives sum_{d<=D}|r_d| <<_A H L^(-A) for each A, since .249<.25. The correction from discarding p|N is negligible: for each discarded p, the only discrepancies it changes have d|N-p; the number of these moduli, including any fixed divisor weight, is N^o(1). If d shares a prime with N, the remainder vanishes by construction. For any fixed C, weighted BV with C^omega(d) follows by Cauchy–Schwarz against this absolute sum and the bound sum C^(2omega(d))|r_d| << H L^O_C(1). Indeed the trivial residue count and the main term are << (H/d)*tau(d) because d<=D<H, and the weighted harmonic sum of a fixed divisor power is logarithmic to a fixed power. The proof uses the true scale H for BV, not N.

For any fixed c>0, uniformly for cutoffs z' between N^c and z, the one-dimensional Euler factor is

    V_N(z')=(1+o(1)) e^(-gamma) S_N/log z'.

For comparison of truncated products the factor over l|N is increasing with cutoff; its missing tail beyond z' is 1+O_c(N^(-c)). The dimension-one product condition follows uniformly by comparing to the primes-not-dividing-N unrestricted product (omitting local factors only lowers the ratio). The usual linear sieve is valid for s in the fixed compact ranges used here; reference Montgomery–Vaughan II §21.3 Theorem 21.9 and (21.70)–(21.71):
https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf .

Write f,F for lower/upper linear sieve functions. Since s f(s)/(2e^gamma)>=log(s-1) at s=d0/mu=4.98 (from (21.71), or the delay equation and sF(s)>=2e^gamma), the basic rough count in units B is at least A0+o(1), A0=log(d0/mu-1)/d0.

For a prime q in [z,N^T], apply the upper linear sieve to A_q at level D/q, with z'=min(z,(D/q)^(1/2)); remaining prime divisors of a z-rough m satisfy this weaker cutoff. This forces s'=max(2,(d0-t)/mu), never requires F(s) for s<1, and log z' >= .0145 L. The prime q itself is not in the sifting set, and if q|N then A_q is empty. The main bound for the conditional count at q, in units B/q, is

    h(t)/(d0-t)+o(1),  h(t) <= 1+x-2log(1+x/2),  x=max(0,(d0-t)/mu-3).

Here s'F(s')/(2e^gamma)=1 for 2<=s'<=3; for 3<s'<=3.98 formula (21.70) gives 1+ integral_0^x log(1+v)/(2+v) dv, and log(1+v)<=v. Replacement q-1 by q is uniform. **Errors are aggregated, not claimed individually uniform:** the sieve remainders are weighted sums of r_{q d}; qd<=D, every d is a product of primes <z'<=z, and q>=z. Thus every qd has at most one representation, so the same weighted BV applies. The sieve-function o(1) is uniform and sum_{z<=q<=N^T}1/q=O(1). In all prime-mark sums omission of q|N can only help, since the majorant is nonnegative.

## 2. Large marks: exact affine switch with an asymmetric Selberg denominator

Here N^T<q<y is a true prime. Since p~H and q<=N^.3, p!=q; hence q|N would give zero. Fix such q coprime to N. Write the cofactor j=(N-p)/q, in the literal interval ((N-bH)/q,(N-aH)/q) with the corresponding half-open endpoints and length H0/q. Demand that qj is z-rough and p=N-qj is prime. For an upper bound, forbid the root j=0 at primes l<z, and the root N-qj=0 at **all** primes l<=K where

    K=N^((1/2-t)/2-1/1000),   v=log K/log z=(.249-t/2)/.05.

We have 1.98<=v<=2.78, q>K, p>K, and all the genuine terms satisfy these exclusions. For l<z, there are two different roots modulo l unless l|N (including l=2), when they coincide. For z<=l<=K there is one root. At every prime l<=K this is a proper set of residues modulo l, and its density g_a(l) is the root count divided by l.

The exact squarefree Selberg denominator is G_a(K)=sum_{d<=K} mu_M(d)^2 prod_{l|d} (g_a(l)/(1-g_a(l))). Here mu_M is the Möbius function and all primes dividing such d automatically do not exceed K. Let G_0(Q) be the corresponding full two-form denominator at arbitrary argument Q, using two roots for l not dividing N and one root for l|N. Define b_l=g_0(l)/(1-g_0(l)) and c_l=g_a(l)/(1-g_a(l)). Then c_l=b_l below z, and at l>=z the difference is zero if l|N and otherwise

    b_l-c_l = 2/(l-2)-1/(l-1) = 1/l+O(1/l^2).

For each squarefree d, telescoping over its prime factors and replacing every remaining c factor by the larger b factor gives

    0<=prod b_l - prod c_l <= sum_{l|d} (b_l-c_l) prod_{r|d,r!=l} b_r.

Sum over d<=K, replace the restricted remainder d/l coprime to l by the unrestricted nonnegative G_0(K/l). This is an exact lower bound

    G_a(K) >= G_0(K) - sum_{z<=l<=K} (b_l-c_l) G_0(K/l),

not an assumption of disjoint loss and not an alternating-series asymptotic. In particular, extending the prime sum to l|N only with a positive upper bound is legal.

## 3. Evaluation of the full denominator and its loss

Uniformly for 1<=Q<=N, we have

    G_0(Q) = (log Q)^2/(2S_N)+O((1+log Q)(log log N)^C).

Here is a proof, including squarefree normalization. Define b_N(d) as the coefficients of the Euler product with factor (1+b_l l^(-s))(1-l^(-1-s))^2 at l. The weight in G_0 is exactly the convolution b_N * (tau(n)/n), because multiplying by zeta(1+s)^2 yields the squarefree Euler product. For l>2, b_N(l)=O(l^-2) if l does not divide N and O(l^-1) otherwise, b_N(l^2)=O(l^-2), b_N(l^3)=O(l^-3), and higher powers vanish. The prime 2 contributes only a fixed bounded factor. Thus sum |b_N(d)|(1+log d)^2 <= (log log N)^C: to bound exceptional prime sums split l|N at L^2, use PNT/Mertens up to L^2, and use at most L/log 2 large prime divisors with max (log l)^j/l for each j<=2. The absolutely convergent local evaluations give sum b_N(d)=product_l (1+b_l)(1-1/l)^2=1/S_N. Finally sum_{m<=Q/d}tau(m)/m=(1/2)log^2(Q/d)+O(1+log(Q/d)), and the log moments bound the substitution of log Q and the tail d>Q. S_N is bounded below absolutely and above by (log log N)^C, so these errors are small relative to any fixed positive multiple of L^2/S_N.

The positive loss above is therefore at most

    (1/(2S_N)) sum_{z<=l<=K} log^2(K/l)/l + o(L^2/S_N)
       = (mu^2 L^2/(2S_N)) integral_1^v (v-u)^2 du/u + o(L^2/S_N).

The equality is Mertens/partial summation, uniform on the compact v range; the O(l^-2) correction and the uniform G_0 error are o(L^2/S_N). Thus

    G_a(K) >= (mu^2 L^2/S_N)(J(v)+o(1)),
    J(v)= v^2/2 - (1/2) integral_1^v (v-u)^2 du/u
        = 5v^2/4 - (v^2/2)log v - v + 1/4.

For 1.98<=v<=2.78, J'(v)=2v-v log v-1>0 (log v<1.1 is sufficient), and J is positive, bounded away from zero on this range. No asymptotic for G_a is needed.

## 4. Genuine Selberg error over all large q

For each squarefree d formed by the exclusions, the number of j hitting the forbidden residues at all its primes is exactly (H0/q)g_a(d)+O(nu(d)), with nu(d)=prod_l (root count)<=2^omega(d). The standard quadratic Selberg weight with lambda_1=1 attains the main denominator G_a(K)^(-1). For clarity, M(k)=prod_{l|k} g_a(l)/(1-g_a(l)); diagonalization of sum lambda_d lambda_e g_a([d,e]) gives sum_k M(k)^(-1)*(sum_{k|d} lambda_d g_a(d))^2. Set the inner variables to mu_M(k)M(k)/G_a(K) (k squarefree, k<=K, and zero otherwise). Möbius inversion gives lambda_1=1 and

    |lambda_d| <= prod_{l|d}(1-g_a(l))^(-1)

for squarefree d<=K, since the positive remaining restricted sum of M(r) is at most G_a(K). All factors are <=3, including l=2 where g_a=1/2. The pointwise square majorizes the sifted indicator. The total error for fixed q is bounded by:

    sum_{d,e<=K} 3^(omega(d)+omega(e)) 2^omega([d,e])
       <= (sum_{d<=K} 6^omega(d))^2 = K^2 (log N)^O(1).

There is no absolute prime-distribution remainder hidden here. Summing these errors even with bounded weights gives O(H N^(-.002) L^O(1)) since K^2=N^(.498)/q and sum_{q range}1/q<<1 (even an integer harmonic log loss would be harmless). This is a power-saving total on the literal p~H scale. Hence the large-q positive main upper cap in units B/q is

    1/(4 mu^2 J(v)) + o(1)

by X=(2+o(1))H0/L. In contrast to a four-form upper sieve, one factors out a genuine prime q and only pays a two-linear-form sieve on a short arithmetic progression. The cost beyond the BV level is combined with, not assumed to inherit, prime distribution in short intervals.

## 5. Positive margin and exact finite arithmetic

By Mertens/PNT for q marks, a bounded piecewise continuous function B_q(t) contributes integral B_q(t) dt/t when summed with 1/q on a fixed positive exponent interval. Therefore the negative weighted mark cost before division by eta is at most (C+o(1))B, with

    C = integral_mu^T [(1-t/beta)/t]*(1+x-2log(1+x/2))/(d0-t) dt
        + integral_T^beta [(1-t/beta)/t]/(4 mu^2 J(v)) dt.

The base is >= (A0+o(1))B. The included rational replay proves A0>5.54 and C<9.103. Thus A0-C/eta >.075, since 5.54−.6*9.103=.0782. This computation is an exact bound rather than an optimization or an empirical input to the theorem.

On any t-cell [a1,b1] in the first integral, (1-t/beta)/t and h^*(t)=1+x−2log(1+x/2) decrease, whereas 1/(d0-t) increases. Use h^* and the numerator at a1, and the denominator at b1. In the second integral use the numerator at a1 and J at b1 (v decreases, J increases). Upper endpoints for logs in J are used with a minus sign, hence they give conservative lower denominators. The series for log x (x>=1) follows by integrating the geometric series in (x-1)/(x+1); the displayed remainder bound uses denominator >=21. Round each integral upper contribution separately upward by 10^-9, so denominator sizes do not accumulate. The replay outputs C1=3.157972136, C2=4.336089259, C3=1.608362412, sum 9.102423807 (all terminating upper rationals). The lower series for A0 gives >5.547.


```python
from fractions import Fraction as F

def log_bounds(x):
    assert 1 <= x <= 4
    v = (x-1)/(x+1)
    a = 2*sum(v**(2*i+1)/(2*i+1) for i in range(10))
    return a, a + 2*v**21/(21*(1-v*v))

D, z, y, T = F(249,1000), F(1,20), F(3,10), F(11,50)
eta = F(5,3)
def cap_bv(a,b):
    x = max(F(0),(D-a)/z-3)
    h = 1+x-2*log_bounds(1+x/2)[0]
    return (1-a/y)*h/(a*(D-b))
def cap_aff(a,b):
    v = (F(249,1000)-b/2)/z
    J = 5*v*v/4-v*v*log_bounds(v)[1]/2-v+F(1,4)
    assert J > 0
    return (1-a/y)/(4*a*z*z*J)
def upper(left,right,cap):
    n = 1000
    dx = (right-left)/n
    unit = 10**9
    total = 0
    for k in range(n):
        a = left+k*dx
        w = unit*dx*cap(a,a+dx)
        total += -(-w.numerator//w.denominator)
    return F(total,unit)
A = log_bounds(D/z-1)[0]/D
C1 = upper(z,D-3*z,cap_bv)
C2 = upper(D-3*z,T,cap_bv)
C3 = upper(T,y,cap_aff)
assert A > F(554,100)
assert [C1,C2,C3] == [F(394746517,125000000),F(4336089259,10**9),F(402090603,250000000)]
assert F(554,100)-(C1+C2+C3)/eta > F(3,40)
```

The equivalent exact rational replay was run with BigInt and returned the three listed upper numerators; these assertions contain no floating tests.

## 6. Genuine squarefree conversion and plain P5 fallback

Discarding squareful rough m costs o(B), even as a signed weight, since |w| is bounded for fixed z=N^mu and every z-rough m<N has <=1/mu distinct prime factors. Directly, to count m=N-p in its interval with r^2|m, z<=r<=N^(1/3), sum O(H0/r^2+1) over integers r: O(H/z+N^(1/3)). For r>N^(1/3) write m=c r^2, c<=N^(1/3); for each c the interval for r has length O(H/sqrt(Nc)), hence sum O(N^(1/3)+H/N^(1/3)). This is o(B). It now follows that the squarefree Omega<=4 actual count is >=(A0-C/eta+o(1))B.

If the asymmetric Selberg calculation is not used, a shorter P5 proof: choose d0=.24, mu=.06, beta=.23, eta=6−100/23=38/23, and use only BV upper bounds, shrinking sieve cutoffs as in §1. The base is log 3/d0 and mark integral is at most log(23/6)/d0 because (1−t/beta)/(d0−t)<=1/d0, and s'<=3 throughout. Since log(23/6)<(3/2)log 3 and eta>3/2 the margin is > (7/76)log(3)/d0. Same squarefree conversion.

## 7. Compatibility with genuine angle exclusions (optional)

Use [the preceding fixed-target all-angle upper](PrimeOppositeThreeFactorAngularSeparation.md) (B-process/Robert–Sargos or Guo) at the same z, whose sieve cutoff power is less than mu. The absolute upper count uses only $H\asymp\sqrt N$ with fixed positive window endpoints, so it applies here even when $b\ge1$. Its per-box four-form upper only requires that the three factor coordinates are z-rough, not individually prime: the primes condition was used only to guarantee local avoidance below that cutoff. Therefore any rough m with >=3 prime factors and a close pair of prime factors q,r gives an actual z-rough triple (q,r,m/(qr)), after sorting. In that sorted triple two adjacent coordinates must have a ratio <=N^delta even if the third is between q and r. Distinct p cannot give the same triple since its product is N-p. For each Q dyadic least side length, each of the two ratio strips has O(1+delta L) intermediate R dyadic choices, with the largest in O(1) dyadic boxes, so O((1+delta L)L) boxes altogether. The earlier per-box upper is O_{a,b,mu}(S_N H/L^4), inclusive of its little-o remainder; output bad count is O_{a,b,mu}(delta S_N H/L^2)+o(B). Optional two-high deletion has the same order (previous thin hyperbola bound; if two factors>N^(1/2-delta), for 2delta<mu they supply all of m). First pass to the **unweighted positive P4 family** above, then subtract these bad counts. A sufficiently small fixed delta retains a positive multiple of B for the same actual family. This is not needed for the rank bound.

## 8. What is still missing for P2, and a single quantitative switched estimate

With only the BV support D=N^(.25-eps), any divisor-supported pointwise score cannot distinguish a prime or a semiprime with both factors >D from a rank-three vector all of whose factors have exponents above .25 and are separated (e.g. .28,.33,.39). At d=1 the divisibility data agree and for every nontrivial d<=D they all vanish. This is a deterministic limitation of such pointwise weights, not a no-go theorem for all uses of BV plus additional arithmetic. The per-box upper for all-angle true rank-three rows does not supply that missing coefficient; the angle domain has positive area and there are O(L^2) boxes. Grouping into a z-rough triple handles Omega>=3 at the same logarithmic order but carries the same issue. No P3 or P2 result is obtained here.

A sharp next target that avoids demanding the full rank-3 or rank-4 prime tuple asymptotic: use instead mu2=.08, beta2=.7, eta2=3−1/beta2=11/7, same d0=.249, B as above. In this paragraph z2=N^.08. The base rough lower bound in units B is log((.249/.08)−1)/.249 >3.003. The part of the mark sum .08<=t<.083 is already <=(.195+o(1))B using §1: its exact limiting upper integral is integral_.08^.083 (1−t/.7)/(t(.249−t)) dt = .1941916756..., since the upper sieve s is in (2,3). Define a single switched weighted moment in the remaining range:

    T_N = sum_{q prime, N^.083<=q<N^.7, (q,N)=1} (1-log q/(.7L))
           * sum_{j integer, aH<N-qj<=bH}
                      1_{P^-(j)>=z2} 1_{N-qj is prime}.

For q>=z2 this tests precisely the complement's roughness, apart from the inconsequential omitted roots p|N (one may insert the omission inside; including them can only increase the upper bound). Proving T_N <= (4.51+o(1))B for all sufficiently large even N would give a genuine squarefree Omega<=2 lower bound: .195+4.51=4.705 < (11/7)*3.003. That inequality for the switched sum is **unproved**. It is not the assertion of a per-box discrepancy nor a restatement of the desired rank: it is one prime-marked cofactor moment with a rough rather than prime inner cofactor, and it ignores the actual rank completely. A plausible reference level, not used in the proof, is the local-sieving/Buchstab model integral (1/(2*.08)) integral_.083^.7 omega((1−t)/.08)(1−t/.7) dt/t. This is <=4.457 under omega(u)<=.57 for u>=2. The latter bound follows from the formula (1+log(u−1))/u on [2,3] (maximize or check .57+log .57>0), and propagates by the Buchstab delay identity for u>=3. Thus 4.51 is above this reference model and below the sufficient threshold. It is not an easy transfer: q near or beyond H gives at most O(1) possible j for each q, so one must average or switch the variables there; a sizeable intermediate portion also sits beyond the actual BV moduli. The residue N at source length H is of size H^2: Lichtman arXiv:2309.08522 Theorem 1.7 (1.7) only states the cited Goldbach-uniform result for |a|<x^(1+epsilon), so the published beyond-square-root level cannot simply be put at x=H here. In particular the two-form affine bound from §§2–4 is not valid pointwise with a useful density through q~H, and does not imply this target.

## Literature scope

The weighting mechanism and sieve functions are classical (the Montgomery–Vaughan reference above, including (21.116) for a Richert-type arrangement). Compare [Yingjie Li and Yingchun Cai, Chen's theorem with small primes](https://camath.fudan.edu.cn/cambcn/ch/reader/view_abstract.aspx?file_no=32B305&flag=1), Chinese Annals of Mathematics B 32 (2011), 387–396: P2 with source bounded by N^.945, not this scale. Runbo Li, Remarks on additive representations of natural numbers, Theorem 1.2 (author PDF https://runbolicarey.com/assets/downloads/Remarks_on_additive_representations_of_natural_numbers.pdf) reports .9409 for a coefficient version of small-prime P2; [the author's separate preprint](https://runbolicarey.com/assets/downloads/A_remark_on_large_even_integers_of_the_form_p_P3.pdf) discusses D_(1,3)(N,0,.817). These are context for the problem, not claims of best current exponent or priority for the square-root P4 application. Focused search did not identify a matching fixed-window P4 theorem, but this is not a comprehensive novelty review.
