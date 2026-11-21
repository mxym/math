# A variable-level two-smallest switch for actual low Goldbach rows

This pointwise estimate unconditionally removes selected low rows in
[SinglePrimeRoughRowCriterion.md](SinglePrimeRoughRowCriterion.md). It
does not establish the required bound on the surviving rows. In
particular, it is not an asymptotic or a proof of Goldbach.

Retain the notation x=N/2, I=(x/2,x], L=log x,
M_N=S(N)x/(2L), a(n)=(log(N-n))1_{N-n prime}, b(n) the
subpower-rough reference, w=a-b, ε=exp(-s/2), y=x^ε,
z=x^{1/3-2ε}, and the marker set
J={p prime: x^{1/3+5ε}<p≤x^{1/2-(s+2)ε}}. Take s a sufficiently
large fixed multiple of 4, and put

    K=s/4,       K0=2(K+1),         H=1/2−ε.
    A_p = H−log_x p,                p∈P*={1}∪J;
    β_p = A_p/K0,                   γ_p = A_p/(K+1)=2β_p;
    T_p(r) = x^{(A_p−log_x r)/K}.                               (10)

As usual, 1|n, and p=1 means the unmarked term, not a prime. Write
c_1=1 and c_p=−1 for p∈J. We have A_p≥(s+1)ε, β_p>ε,
γ_p<1/4 for s large, and T_p(r)≥r when r≤x^{γ_p}.
All cutoffs are real; inclusion and exclusion at endpoints in the
formulas below are literal.

For n∈I with y≤P^-(n)<z, let r=P^-(n) and q=P^-(n/r).
In particular q is the second smallest factor with multiplicity,
and n/r>1. For each p|n, p∈P*, delete its contribution to the
signed expansion of R(N) if either

    y≤r<x^{β_p},                                      (whole rows)
    x^{β_p}≤r<x^{γ_p} and r≤q<T_p(r).                (two-factor wedge)

Let D(N) be the sum of all deleted contributions c_p w(n)
and let R_rem=R−D. Then, uniformly as even N→∞ at fixed s,

    |D(N)| ≪ [s² exp(−s/4)+o_s(1)] M_N.                        (11)

The implicit constant in the first term is absolute. The two-factor
part, unlike a single raising of the y cutoff, still holds if each
q-range [r,T_p(r)) is replaced by any interval
[U_p(r),V_p(r))⊂[r,T_p(r)) (or with the same right endpoint), and
each (p,r) receives any weight in [−1,1]. In particular these are
local fixed-target comparisons for actual primes, not a mean-square
or a statement requiring arbitrary prime-pair decorrelation. There
can be multiple markers per n; the deletion is per summand in the
signed expansion, not a condition that a marked integer is removed
once.

## 1. Sieve comparison with a moving level and a forced small prime

Write X_I=x/2 and g_N(d)=1_{(d,N)=1}/φ(d). Use the established ordinary
Type I statement (3) of the criterion for each t=a,b: for every fixed
δ,B,C>0,

    Σ_{m≤x^{1/2−δ}} τ(m)^C
       |Σ_{n∈I,m|n} t(n)−X_I g_N(m)| ≪_{δ,B,C} xL^{-B}.         (12)

Here δ=ε is fixed. Split off the two sequences before applying an
upper or lower sieve; the signed w need not be nonnegative. Use the
ordinary dimension-one linear sieve, e.g. [Bordignon–Johnston–
Starichkova, arXiv:2207.09452v6, §2](https://arxiv.org/html/2207.09452v6#S2)
or [Iwaniec, *A new form of the error term in the linear
sieve*](https://bibliotekanauki.pl/articles/1393119.pdf).
We use the standard F(v), f(v) enclosure with coefficients bounded
in absolute value by one, F(v)−f(v)≪exp(−v) for v≥2, and little-o
coefficient errors uniform on any fixed compact v-range.
For the weight formulation, see [Theorem 2.1 of Superscars for
arithmetic point scatters II](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136).
The exponential bound has an absolute constant: the
linear-sieve delay equations give F(v)−f(v)=2e^γ ρ(v−1)/v,
where ρ is Dickman's function. The normalized difference is one
for 1≤v≤2 and its translated derivative is ρ′(t)=−ρ(t−1)/t.
Monotonicity and the integral equation
tρ(t)=∫ₜ₋₁ᵗ ρ(u) du give ρ(t)≤1/⌊t⌋!.

The dimension-one product hypothesis is uniform here: deleting factors
of N only decreases the product of reciprocal local factors
over any interval of primes, and the full product for 1/(ℓ−1),
ℓ>2, satisfies the dimension-one estimate by Mertens.

First consider the sum of w(n) over p|n, P^-(n)≥U=x^u, with
p=1 or p∈J and U<p if p>1. The conditional squarefree density
g_N(pd)/g_N(p) on d from the sieving primes equals g_N(d) whenever
g_N(p)≠0. Sieve with D_local=x^{A_p}; hence all physical moduli
pd≤x^H. If g_N(p)=0, all their Type I main terms are zero and
the same comparison holds with zero main (use the ordinary
pointwise linear-sieve inequalities). In addition to the two
Type I error sums, the absolute comparison costs at most

    [F(A_p/u)−f(A_p/u)+o_s(1)] X_I g_N(p)V_N(U),
    V_N(U)=∏_{ℓ<U}(1−g_N(ℓ)).                                   (13)

If p>1, both y and x^{β_p} are indeed <p. Uniformly for exponent
u≥ε bounded above, V_N(U)=(e^{-γ}+o_s(1))S(N)/(u L) by Mertens and
the ordinary local singular identity. Only u in a fixed compact
subset of (0,1) at this fixed s occurs.

Next condition on rp|n, with primes r<z and p∈P*. For p>1, p>r.
Sieve v=n/r with cutoff U=x^u≥r and, if marked, U<p.
Then the actual moduli are **rpd**, including r²p if r|d
(the divisor d is of n/r, not just of n). For (rp,N)=1 the
conditional local density at ℓ≠r remains g_N(ℓ); at r it is
g_N(r²p)/g_N(rp)=1/r. When r is among the sieving primes it
therefore modifies V_N(U) by the factor

    (1−1/r)/(1−1/(r−1)) = 1+1/[r(r−2)];

otherwise the factor is one. These modifications preserve the
dimension-one hypothesis above and are uniformly 1+o_s(1)
since r≥y. If g_N(rp)=0 every main remains zero, as in (13).
Take D_local=x^{A_p−t}, t=log_x r. All actual moduli
rpd≤x^H. For both endpoint cutoffs in (11), the remaining
comparison is bounded by

    [F((A_p−t)/u)−f((A_p−t)/u)+o_s(1)] X_I g_N(rp)V_N(U)
    ·(1+o_s(1)),                                               (14)

plus the Type I errors.

Each modulus has at most τ(m)² descriptions (p,r,d), allowing
p=1 and the r² case; the factors p,r are divisors, and d is then
determined. The first sieve with no r has at most τ(m)
descriptions. The endpoint comparison uses at most two sieves per
index; arbitrary choices of U,V or sign weights alter none of these
absolute error bounds. Thus (12) absorbs all errors uniformly in N,
not just after averaging N. All positive ratios A_p/u or
(A_p−t)/u used below lie between K and 1/(2ε) (fixed s).
The little-o terms after summing normalizations are o_s(M_N):
the reciprocal prime sums are bounded at fixed ε, and every
endpoint u≥ε.

## 2. Exact two-smallest identity and the signed bound

For every p∈P*,
the deleted whole rows are given exactly by the difference of
the two rough sums in (13) at U=y and U=x^{β_p}. This is ordinary
Buchstab sorted by the least prime factor, with p kept as the
restriction p|n. No marker is a deleted smallest factor.
At y the parameter is A_p/ε≥s+1, so the sum over p costs
O(e^{−(s+1)}/ε)M_N+o_s(M_N) since Σ_{p∈P*} g_N(p)≪1.
At x^{β_p}, the parameter is exactly K0; the cost is at most

    O(K0 e^{−K0}) M_N Σ_{p∈P*}g_N(p)/A_p+o_s(M_N).             (15)

In the second wedge, for fixed p,r and
r≤U≤V≤T_p(r), write H_U(v)=1_{P^-(v)≥U}. The exact second switch is

    Σ_{n∈I,rp|n} w(n)[H_U(n/r)−H_V(n/r)]
      = Σ_{q prime; U≤q<V} Σ_{rqv∈I,p|rqv,P^-(v)≥q} w(rqv).   (16)

When p∈J we have p>T_p(r) because log_x T_p(r)≤H/K<1/3.
Thus the marker always survives into v on the right. Formula (16)
also holds if q=r (there is precisely one choice of q as the
least factor of n/r, even with multiplicity). If v=1, the
convention P^-(1)=∞ applies. When U=V both sides vanish.

Take either moving endpoint u=log_x U, log_x V. From (14),
the relevant normalized cost per (p,r) is bounded by a
constant times g_N(rp)M_N exp(−(A_p−t)/u)/u, plus its
summable little-o term. This expression without g_N(rp)M_N
is increasing for u≤(A_p−t)/K since K>1. At the right endpoint
its bound is

    e^{−K} K/(A_p−t) ≤ e^{−K}(K+1)/A_p,   β_p≤t≤γ_p.

On this band g_N(rp)=g_N(r)g_N(p), and the prime reciprocal mass
Σ_{x^{β_p}≤r<x^{γ_p}} 1/(r−1) = log 2+o_s(1) is uniform
in p, smoothly varying between fixed positive exponents at each s
by Mertens (one can keep only an upper bound of 2). Summing both
endpoints proves the wedge bound, including the general intervals
and weights in the statement. The remaining sum satisfies

    Σ_{p∈P*} g_N(p)/A_p
       ≪ 1+∫_{1/3}^{1/2−(s+2)ε} du/[u(H−u)] + o_s(1)
       ≪ 1+log(1/((s+1)ε)).                                   (17)

For the first inequality use reciprocal prime sums uniformly on
this fixed exponent interval; its endpoint is separated from H by
(s+1)ε and the weight is bounded there, so ordinary partial
summation or Riemann sums apply. Factors p|N only decrease the
nonnegative sum. With s/4=K, (15)–(17) and the first y
error prove (11).

For an exact test of a nonempty moving marked box, set s=4K,
K≥20. Take marker exponents in [3/8,19/50], r-exponents in
[2/(25K),4/(45K)], and q-exponents in [1/(10K),2/(19K)].
Since ε=e^{−2K}<1/10000, A_p is between 1199/10000 and 1/8.
Then β_p≤1/[16(K+1)]<2/(25K), γ_p>4/(45K), and
(A_p−4/(45K))/K>2/(19K). Also q>r throughout this box.
The marker band is contained in J for K≥20 (use
e^{40}>2^{40} to bound both ε and (4K+2)ε monotonically).
The moving interval version of (11) therefore applies to
this whole box. These are present factor positions, not an empty
constraint: even the subset of integers with one final prime
v/p, in (x/(2rqp),x/(rqp)], has ordinary positive three-exponent
density times x/(2L) by the prime number theorem, with all four
positions distinct and sorted as r<q<p<v/p. The interval for its
last exponent stays uniformly in a compact subset of (1/2,1).
The b-weight of this subset has the same positive density times
M_N by applying the subpower sieve to the last prime as in
[HighPrimeRowBound.md](HighPrimeRowBound.md), (9).
Its normalized density is the integral of
1/[t q' u(1−t−q'−u)] on the above exponent box
(t=log_x r, q'=log_x q, u=log_x p), bounded below by a fixed
positive constant as K grows since the r,q' interval ratios are
fixed. Thus the switched discrepancy can be made much smaller than
its comparison mass. This comparison only controls the entire
rough quotient class of (16); it does not assert that the final
factor is prime on the a side.

## 3. Specific low-row remainder and a scope obstruction

Since γ_p≤H/(K+1)<1/4, no removed row intersects
R_hi at α=4/15. With s large enough, (11) costs an arbitrarily
small fixed multiple of M_N; combine with (7) of the criterion
and (8) of the high-row estimate. For example, choose s large
and then N large so that all those error terms together total
less than .002 M_N in absolute normalized loss. Then the
single additional estimate

    R_rem(N)−R_hi(4/15) ≤ .003 M_N                              (18)

would leave at least .002 M_N genuine weighted prime pairs in
the central interval, exactly as before but with the removed
positions no longer in the hypothesis. (18) is not proved.

The new cancellation cannot by itself be extended to all the
remaining cases by moving the *same* linear-sieve level. To get
a positive standard lower sieve on rp|n after imposing
P^-(n/r)≥x^u, our available level requires t+log_x p+2u<H.
If q of exponent v is conditioned on instead of ranged over in
(16), the analogous requirement is
t+log_x p+v+2u<H (in particular t+log_x p+3v<H for u≥v).
Moreover, explicitly conditioning on two J markers
already costs a product >x^{2/3}, before the small factors.
If h=rp (or r) is fixed of exponent B in [0,H], making the last
quotient n/h∈(x/(2h),x/h] prime by roughness at sqrt(x/h)
requires the sieve ratio (H−B)/((1−B)/2), which is <1.
These observations obstruct this literal ordinary-BV
conditioning argument, not every possible two-prime switch.

There is also a quantitative check for the surviving sign.
Take the earlier [arithmetic parity witness](ArithmeticTwoWeightParityWitness.md)
with exactly the present b and model a^+(n)=b(n)(1+λ(n)).
The model is nonnegative and supported on arbitrary integers,
not actual shifted primes. Its proof of (12) is valid at
Z=exp(L^{1/4}) here as well: use Bonferroni rank L^{1/4}+O(1),
so the largest auxiliary modulus is exp(O(L^{1/2}))=x^o(1)
and the factorial tail is below every log power. All the
division-of-progressions and λ BV steps there are unchanged.
Fixed-degree prime-factor box upper estimates of the earlier
factor-4 type still hold in this model: the weight is exactly
2b on the even-parity boxes, zero on the odd-parity boxes.
This is not a claim that every form of Chen switching or
prime-specific input is modeled.

For this a^+, w=λb. The exact identity (6) of the criterion
therefore gives

    R^+(N)= E_y^+(N) + Σ_{p prime in I} b(p) + O(C_b(N)),
    |E_y^+|≪ (e^{−s}/ε+o_s(1))M_N,
    C_b=Σ_{n composite in I} b(n)B(n)
         ≪ ((s+2)ε+o_s(1))M_N.

The first error bound is the criterion's linear-sieve proof
on (12), and the second is its exact thin-strip classification
followed by (9) of HighPrimeRowBound in the last factor
(all fixed factors exceed z). Thus R^+/M_N can be made
arbitrarily close to one under the same order of choices s,N.
On the high rows the semiprimes contribute exactly +b.
Ternaries with no marker have −b, one marker zero, and two
markers +b. Dropping the negative sector and applying the
reference calculation in HighPrimeRowBound gives

    R_hi^+(4/15)/M_N ≤ log(11/8)+3/80+o_s(1) < .356+o_s(1).

The exact bound .356 follows from the first eight terms of
2 Σ_{j≥0}(3/19)^{2j+1}/(2j+1) with tail bounded by
2(3/19)^{17}/[17(1−(3/19)^2)] (the same method as the prior
constant check). Since the deleted part in the model is still
bounded by (11), for fixed s sufficiently large and all large
even N, the surviving low residual is >.64 M_N in this model.
In particular (18) does not follow from the ordinary Type I
data, the present switch, and separate fixed-degree majorants
alone. The estimate (11) itself is genuine arithmetic for
actual shifted primes and imposes no hypothesis of a missing
Goldbach representation; the remaining positive input must
distinguish the actual prime side from this one-sided model.

## Context

The second Buchstab identity and linear-sieve enclosure are
classical; the result concerns the exact moving region and
normalization (11) for this particular fixed-target criterion.
[Grimmelt–Teräväinen v2](https://arxiv.org/abs/2508.16400v2) use
rough models in additive Fourier estimates to bound an
exceptional set for two Chen primes. [Pham v1](https://www.preprints.org/manuscript/202611.0694)
uses restricted switching at a larger level with mean-value
results. [Arneth v1](https://zenodo.org/records/23011047) studies
different marked-switch and Liouville obstructions. These do
not yield (18); conversely (11) estimates only its stated
selected rows and supplies neither an exceptional-set result
nor a general parity-breaking estimate.
