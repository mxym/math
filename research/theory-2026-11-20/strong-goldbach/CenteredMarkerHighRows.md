# Centered divisor markers remove the even high prime rows

**Unconditional fixed-target result.** Replace the single-prime
marker in the signed Goldbach criterion by a truncated alternating
divisor marker. The high part with least prime exponent at least
31/200 then costs less than .983 of the reference before vanishing
small-cutoff errors. Every even composite factor count disappears
away from thin divisor walls. No distribution beyond the square
root is used. The remaining low signed estimate is different from
the earlier one and is unproved.

Write x=N/2, I=(x/2,x], L=log x, M_N=S(N)x/(2L), and retain the
true shifted-prime weight a(n), subpower-rough reference b(n), and
w=a-b from [SinglePrimeRoughRowCriterion.md](SinglePrimeRoughRowCriterion.md).
Fix α=31/200 (or any fixed 1/7<α<1/6). For sufficiently large fixed s set

    ε=e^(−s/2), y=x^ε, z=x^(1/3−2ε), δ=(s+2)ε,
    H_v(n)=1_{P^-(n)≥v},                 P^-(1)=∞,
    F(n)=Σ_{d|n, P^-(d)≥x^α, d≤x^(1/2−δ)} μ(d),
    B(n)=H_z(n) F(n),
    E_y=Σ_{n∈I} w(n)H_y(n)F(n),
    R_new=Σ_{n∈I, y≤P^-(n)<z} w(n)F(n).

The d=1 term is included. Let R_hi and R_lo partition R_new
according as P^-(n)≥x^α or P^-(n)<x^α. Uniformly in even N,

    R_hi ≤ [C_3(α)+18 U_5(α)+O_α(δ)+o_{s,α}(1)] M_N,          (31)

where

    C_3(α) = 2∫_α^(1/4) log(1/(1−2t)) dt/[t(1−t)]
            +2∫_(1/4)^(1/3) log((1−2t)/t) dt/[t(1−t)],
    U_5(α) = (1−5α)^4/[4!·5!·α^4(1−4α)].

The exact [rational checker](check_centered_marker_high.py) gives
C_3(31/200)+18 U_5(31/200)<.983. No estimate of the old low
residual is assumed to transfer, since F includes multiples of
larger subsets of factors even in low rows.

## 1. Ordinary Type I and exact signs in the extraction

Use (3) of the original criterion: a,b have the same Type I main
(x/2)g_N(m), with g_N(m)=1_{(m,N)=1}/φ(m), and arbitrarily
many log powers of divisor-weighted saving in L1 up to
x^(1/2−ε). For each eligible d, separately apply the ordinary
linear upper/lower sieve to each nonnegative sequence on d|n,
with cutoff y and level y^s, inserting the sign μ(d) only
afterward. Its local divisors use only primes <y, so are
coprime to d. All physical moduli are ≤x^(1/2−2ε). The
large/small prime split is unique (a τ(m) bound would also
suffice). If (d,N)>1 the same pointwise sieve bounds have
zero main and their discrepancy sums still apply. The total
Σ_{d eligible} μ(d)^2 g_N(d) is O_α(1) by the exponential
series of Σ_{x^α≤p≤x^.5}1/(p−1)=O_α(1). The enclosure gap
is O(e^(−s)) times the local sieve density
V_N(y)≍S(N)/(εL). Hence

    |E_y| ≪_α [e^(−s)/ε+o_{s,α}(1)] M_N.                       (32)
    Σ_{n∈I} w(n)B(n)=E_y−R_new.                                (33)

The second identity is exact by the difference of the two rough
indicators; it needs no positivity of F.

For prime n∈I, B(n)=1. A z-rough n∈I has at most three
factors since z^4>x. Repeated p≥x^α can be ignored in the
high and z-rough parts: the number of n with such a p²|n is
O(x Σ_{p≥x^α}p^(−2)), a+b≪L, and F is bounded by 2^6 on
these parts. For a z-rough distinct semiprime, B is 0 or 1.
It is 1 only if the least factor r is in
1/2−δ<log_x r≤1/2: both factors ≤x^(1/2−δ) would give product
<x/2 eventually, and if exactly one qualifies its sign cancels
the d=1 term. For a z-rough distinct ternary, all factors
are ≤x/z²=x^(1/3+4ε)<x^(1/2−δ) and all products of two exceed
the marker limit. Thus B=−2 exactly. The positive true
semiprime loss is O(δ+o_s(1))M_N by the two-form sieve in §1
of the criterion, and the reference ternary weight is
O(ε+o_s(1))M_N by the fixed-factor last-prime reference (9)
of [HighPrimeRowBound.md](HighPrimeRowBound.md), now with all
factor exponents in an O(ε) strip around 1/3. Constants are
uniform for s large.

Consequently, writing G_a=Σ_{n∈I prime} a(n), and using the
reference prime mass from (4) of the original criterion,

    G_a = Σ_{n∈I} b(n)B(n)+E_y−R_new−Σ_{n composite}a(n)B(n)
        ≥[1−O_α(δ)−o_{s,α}(1)]M_N−|E_y|−R_new.                 (34)

The negative composite B is paid on the b side, but −aB helps
the lower bound on that branch. No "B is a sieve minorant" or
unstated nonnegativity is used.

## 2. Fixed-target reference and upper sieve for prime products

Let I_k(G) be the integral for a bounded nonnegative weight G
on the sorted k-factor simplex, against

    dt_1 … dt_(k−1)/(t_1···t_k),   t_k=1−Σ_(i<k)t_i,
    α≤t_1≤…≤t_k.

All G here are piecewise continuous with finitely many affine
boundaries, and all product carriers are distinct squarefree
products restricted to I. Then with limits uniform in even N
at fixed region,

    Σ_{k-factor n∈I} b(n)G = [I_k(G)+o(1)]M_N,
    Σ_{k-factor n∈I} a(n)G ≤ [4 I_k(G)+o(1)]M_N.               (35)

For b apply the subpower prime-product sieve, or fix the first
k−1 primes and apply the last-factor proof in the prior high
note (9); its scale is ≥x^(α+o(1)), arbitrary intervals are
covered by maximal prefixes, and the auxiliary moduli use only
primes below those fixed factors. Each nonzero local excluded
class is exactly the same reduced class density as there,
so the singular factor is S(N). Ordinary prime reciprocal
sums then give the specified simplex density including x/2
from the product interval.

For a apply the dimension-one optimized Selberg sieve on the
whole product sequence. Precisely, [Liu–Park–Song,
Theorem 3.2](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3)
applies to the indicator of a product of any fixed number
k of **distinct primes restricted to interval slots** and
gives a maximal reduced-residue discrepancy against the
coprime total summed through x^(1/2−τ) for every fixed τ>0.
Use the two prefixes x and x/2 (with u=1 at each rescaled
endpoint, or u=log(x/2)/log x using their uniform proof).
Our fixed exponent boxes use identical/disjoint bins;
each unordered product has a single bin-count assignment.
In the proof of that result one can alternatively use
its Lemma 3.1 on one interval-prime slot and the convolution
of the remaining slots via dyadic decomposition, keeping
the bounded factorial when bins coincide. Sharp product
ends can also be handled by a log-power smoothed cutoff:
the transition per modulus d is O(Δx/d+1) since the carrier
is bounded, and hence negligible in summed errors at
x^(1/2−τ); separate the smooth cutoff by Mellin inversion
with log-power loss. If controlling repeated-prime terms
directly, p²|n forces p≤sqrt x, so the +1 progression
errors summed over p and moduli are O(x^(1−τ)). All of
these are at the **full** product scale x, with no loss
of a positive power for k=5. Divisor-weighted errors follow
from Cauchy and the trivial progression bound. Replacing
the coprime total by the full one costs
O(x^(1−α)(log x)^C) in the weighted harmonic sum,
since a product factor dividing d is at least x^α.

The Selberg denominator for d≤x^(1/4−τ/2) is
(1+o(1)) log(x^(1/4−τ/2))/S(N), as proved in §3 of the
prior high note. Apply it to N−n, which for true primes is
larger than this cutoff, and then use log(N−n)=(1+o(1))L.
Sending fixed τ↓0 gives 4, for each fixed positive box.
Approximate G by upper step functions for a and Riemann-integrable
step comparisons on b, using the same finite mesh with
disjoint bins; after N→∞ send the mesh to zero. In particular
a proper subset-sum wall within width h has O_α(h)+o(1) of
normalized a+b mass: the compact density is bounded, the
wall is transverse, and the size of the main bound comes
from (35) rather than the number of mesh boxes. This handles
the positively weighted quintuple sectors without assuming
a distribution theorem for a signed nonseparable filter.

## 3. Exact centered geometry

In R_hi all prime factors are ≥x^α, and at most six occur
since α>1/7. Ignore repeats as above. Use exact
t_i=log(p_i)/log n, with Σt_i=1, t_i≥α, and
t_i=log_x p_i+O(1/L). Put aside the region where any proper
nonempty subset sum is within 2δ of 1/2. By (35), this and
all endpoint shifts cost [O_α(δ)+o_{s,α}(1)]M_N, with
|F|≤2^6. Outside these walls, F is exactly the signed
subset sum restricted to those subsets with exponent sum
strictly below 1/2.

For even k each complementary pair has equal sign and precisely
one member below 1/2; by zero total, F=0. For any composite
with a coordinate >1/2, the retained subsets are exactly all
subsets of its nonempty complement, so again F=0. This
handles all even ranks and the unbalanced odd ranks.

For balanced k=3 all singletons but no pairs are retained, so
F=−2. When bounding R_hi above this costs only 2b, since
a≥0. To obtain its mass drop the upper least-factor cutoff
P^-(n)<z. With sorted t≤u≤1−t−u, the upper u-end is
(1−t)/2; the lower end is 1/2−t for t≤1/4 and t for
t≥1/4. The antiderivative of 1/[u(1−t−u)] is
log(u/(1−t−u))/(1−t). Thus the integral is exactly C_3(α).

For balanced k=5 all singletons are retained and no
four-factor subset can be (4α>1/2). If j pairs have sums
>1/2, the retained pairs number 10−j and the retained
triples j, by complementarity. Hence F=6−2j∈[−14,6].
Using F=F_+−F_- and (35), the upper bound on its signed
discrepancy is [3I_5(F_+)+I_5(F_-)+o(1)]M_N: the negative
actual part −F_-a helps and the positive actual part is
compared to its exact b reference. Pointwise
3F_++F_-≤18, so after enlarging to the whole simplex it
costs at most 18 I_5(1). Concavity of Σ log t_i gives
∏t_i≥α^4(1−4α) at every point, since the minimum is at a
vertex. The sorted simplex volume is (1−5α)^4/(4!·5!)
(the permutation Jacobians have modulus one on the
projected coordinates). This proves (31).

## 4. The new remaining condition

At α=31/200 pick s sufficiently large, then N large, so
the sum of errors in (31), (32), (34) is less than .005 M_N.
The quantified high term is <.983 M_N. Accordingly the
single additional inequality

    R_lo(N) = Σ_{n∈I, y≤P^-(n)<x^(31/200)}
                   (a(n)−b(n)) F(n) ≤ .010 M_N

at every sufficiently large even N would leave
G_a≥.002 M_N and a positive multiple of M_N/log N
genuine central prime pairs. This unproved condition differs
from the prior single-mark one. The present F differs from the
previous smooth logarithmic centered-Möbius kernels: it uses
only eligible large factor divisors below the ordinary
distribution level, gives exact high-rank parity cancellation,
and preserves ordinary presieve transfer. No positivity on
its true low-factor residue follows from these calculations.

## Context

The complement pairing in the centered divisor sum is elementary; the quantitative result here is the presieved comparison and the explicit bound at 31/200. The [earlier logarithmic centered kernel](SymmetricParityReduction.md) cancels the opposite parity and leaves different weights. The upper policies and labelled product estimates of [Chan v1](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf), the support restrictions and kernel results of [Pham v1](https://www.preprints.org/manuscript/202611.0694), and the signed-correlation programs of [Arneth v1](https://zenodo.org/records/23504447) and [Bahboui v1](https://www.preprints.org/manuscript/202610.0809) are related but do not enter the proof. [Salazar v1, §5](https://arxiv.org/html/2611.10059v1#S5) provides a useful comparison for the ordinary two-linear-form upper-sieve step. The numerical bound (31) uses only the ordinary full-product estimate (35) and concerns this one-sided decomposition, not the best almost-prime theorem or a priority assertion.
