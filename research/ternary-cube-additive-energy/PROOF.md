# Sharp additive-energy exponent on the ternary cube

AI-assisted research draft. No claim of external review, priority, or an answer for other alphabets. Sums below are ordinary coordinatewise integer sums, NOT addition modulo 3.

For a finite nonempty set A let E(A) count ordered quadruples (a,b,c,d) in A with a+b=c+d. Let t be the smallest real exponent making E(A)≤|A|^t for every A⊆{0,1,2}^d and every d≥1. Define P(z)=1+12z+6z². Then t=4/q, where (q,z) is the unique solution in the region

    1.4702039297178894 < q < 1.4702039297178896,   1/4 < z < 1

of

    3 z^(1−q/2)(1+z)=1+6z,          (4−q) log P(z)=4 log(1+6z).

This is an implicit exact constant; the certified enclosure is
**2.7207109973971711 < t < 2.7207109973971716**. Equality for a finite nonempty set holds only for singletons. Nevertheless an explicit sequence of Hamming balls around the all-ones word attains the exponent asymptotically (not equality at a fixed dimension).

## 1. The known reduction and endpoint symmetrization

De Dios Pont–Greenfeld–Ivanisvili–Madrid (2023), Proposition 21 and §4.3, identify t=4/q where q is the largest exponent such that
||a+b e(θ)+c e(2θ)||_(L4 of the unit torus) ≤ ||(a,b,c)||_q
for every coefficient triple. This is the finite-set/discrete-extension equivalence, not a new reduction here. Taking moduli increases the fourth power on the left, by expansion. For nonnegative a,b,c the fourth power is

    a⁴+b⁴+c⁴ +4(a²b²+b²c²+c²a²) +4abc·b.

Among permutations the largest value is obtained by putting a largest coefficient in the middle. For a nonzero triple, put b=1 by homogeneity and x=a/b, y=c/b in [0,1]. The numerator is

    W(x,y)=1+4x²+4y²+4xy+x⁴+y⁴+4x²y².

We show that for q≥10/7 it strictly increases on averaging any two *unequal endpoint q-masses* x^q,y^q, while keeping their sum fixed and leaving the center fixed. By symmetry let 0<y<x≤1, v=y/x. The desired derivative sign W_x/x^(q−1)<W_y/y^(q−1) reduces exactly to

    v^(q−1) [(2+v)+x²(1+2v²)] < (1+2v)+x²(2v+v³).

It suffices to prove strict inequalities at x²=0 and 1, since the difference is affine. At 0, replace v^(q−1) by v^(1/3), which is larger. The resulting difference is (1−w)³(1+w)>0, where w=v^(1/3). At 1 replace v^(q−1) by v^(3/7). With u=v^(1/7) the difference becomes

    R(u)=1−3u³+4u⁷−u¹⁰−2u¹⁷+u²¹.

It is strictly positive for 0≤u<1. The ascending coefficients of
(1+v)²¹ R(v/(1+v)) are

    1,21,210,1327,5931,19890,51816,107104,177842,238602,258699,
    225435,156023,84063,34206,10122,2191,477,165,48,4,0.

This is an integer binomial expansion. Continuity and strict increase on
the interior of the averaging path also give strict improvement from y=0<x.
This proves the symmetrization; its range more than covers the critical q.

## 2. A unique nonconstant maximum and the crossing

Write z=x²=y² after averaging. The maximal fourth-power ratio is now

    max_{0≤z≤1} G_q(z),   G_q(z)=P(z)/(1+2 z^(q/2))^(4/q).

Every value is attained by the corresponding nonnegative triple (√z,1,√z).
The derivative of log G_q(z) for z>0 has the sign of h_q(z)−1, where

    h_q(z)=3 z^a (1+z)/(1+6z),       a=1−q/2.

Indeed clearing the positive denominators in the derivative gives a
positive multiple of 3(1+z)−z^(q/2−1)(1+6z).
Work on the closed q interval with endpoints q_L=1.4702039297178894,
q_U=1.4702039297178896. The function h starts at 0 and ends at 6/7. Its
logarithmic derivative has numerator a+(7a−5)z+6az². This upward-opening
quadratic is positive at 0 and negative at 1 (14a−5<0), so its only zero
in (0,1) is a strict maximum of h. Also h_q(1/4)>1 throughout, since
h increases with q at this point, and h_(q_L)(1/4)>1 by the rational
certificate below (or a coarser direct logarithm bound). Consequently
h=1 has exactly two roots, one on each side of 1/4. Call the larger one
z(q). The derivative sign of G runs minus, plus, minus. The maximum on
[0,1] is max{1,M(q)}, where M(q)=G_q(z(q)) is its unique maximum on
[1/4,1]. As a maximum of a continuous function on a fixed compact
interval M is continuous. It is strictly increasing because for each
z∈[1/4,1] the positive triple's ℓ^q norm strictly decreases with q.

At the critical point z=z(q), z^(q/2)=3z(1+z)/(1+6z). Hence

    q log M(q)=4 log(1+6z)−(4−q) log P(z).

At q_L the RHS is strictly negative, and at q_U it is strictly positive.
Here are reproducible exact endpoint certifications. At q_L bracket z(q_L)
between 0.32606289730212337828 and that rational plus 10^(−20); at q_U
use 0.32606289730212362033 and that rational plus 10^(−20). At each left
endpoint log h is positive and at each right endpoint it is negative.
Substituting intervals into the last display gives, in units of 10^(−25),

    q_L log M(q_L) ∈ [−2806923826,−2805386773],
    q_U log M(q_U) ∈ [ 2716006432, 2717543485].

These are outward rational enclosures: reduce each log argument by powers
of two to [1,2], use 2∑_(j=0)^39 y^(2j+1)/(2j+1) where y=(v−1)/(v+1),
and bound the remaining tail by 2y^81/(81(1−y²)); log 2 uses the same
rule. All comparisons and printed bounds are verified by plain-integer
and Fraction arithmetic in verify.py; none depends on float convergence.

There is exactly one crossing M(q)=1 in the displayed interval. It
is the largest admissible q by norm monotonicity even outside this
interval: the sharp interior triple at the crossing violates the inequality
for every larger q. This proves the asserted exact formula. At that
q the only nonzero nonnegative coefficient extremizers are point masses
and scalar multiples of (√z,1,√z) in exactly this order: a positive product
abc forces the largest coefficient to the center and unequal endpoints
strictly improve by averaging. The face with exactly two nonzero
coefficients is also strictly below the maximum by strict symmetrization.
We do not need uniqueness for complex phases.

## 3. Finite-set strictness; a concrete asymptotically extremal construction

For clarity, the dimension-free upper bound can be seen directly by
Hölder induction (the standard tensorization argument). Let A_i be its
three slices; expand the energy integral by orthogonality in the
sliced coordinate. For each i+j=k+l the remaining integral of four slice
transforms is at most the product of their L4 norms by absolute values
and Hölder. Summing gives E(A)≤W_4(v_0,v_1,v_2), where W_4 denotes the
homogeneous quartic in §1 and v_i=E(A_i)^(1/4) (zero for empty slices).
Inductively bound v_i≤|A_i|^(1/q); the quartic has nonnegative
coefficients and contains v_i⁴, hence the substituted inequality is
strict if any nonempty slice is strict. By §2 the result is
E(A)≤(∑|A_i|)^(4/q). Beginning with d=0, if equality holds, each
nonempty slice is a singleton by induction. Then (|A_i|^(1/q)) is a
0–1 triple, none of which with two or more occupied coordinates can be a
non-point-mass extremizer just identified. Conversely singleton equality
is immediate.

Put f=(√z,1,√z), Z=∑ f_i^q, and π_i=f_i^q/Z. Define α=π_0+π_2<2/3.
For each d take the ternary Hamming ball

    A_d={w∈{0,1,2}^d : #{j:w_j≠1}≤⌊αd⌋}.

Then log E(A_d)/log|A_d|→t as d→∞. To prove it, put a distribution
ν on the 19 allowed ordered single-coordinate quadruples i+j=k+l by
ν(i,j,k,l)=f_i f_j f_k f_l/P(z). The symmetries of the equation act
transitively on the four positions; let μ be their common marginal.
For each letter i, the logarithmic derivative of the homogeneous quartic
in f_i is 4μ_i. Since f is a strictly positive unconstrained maximizer
of the normalized fourth power, stationarity in each log f_i equates this
to 4 f_i^q/Z. In particular μ=π. Writing H for ordinary Shannon entropy
in natural logarithms,

    H(ν)=log P(z)−4∑π_i log f_i = (4/q) H(π),

because P(z)=Z^(4/q). This uses a standard type-counting construction,
not a new tensorization principle. Choose the integer count N_ω=⌊dν_ω⌋
of each allowed quadruple, and assign the less than 19 unallocated
coordinates to (1,1,1,1). In *each* of the four resulting words, the
number of noncentral letters is at most d(π_0+π_2) before integer
rounding and cannot increase by this final allocation. Thus every ordering
of these coordinate types contributes one distinct ordered additive
quadruple in A_d. All 19 limiting probabilities are positive and
N_ω=dν_ω+O(1). Stirling therefore gives

    log E(A_d)≥log(d!/∏N_ω!)=dH(ν)+O(log d).

Also |A_d|=∑_(k≤αd) binom(d,k)2^k satisfies
log|A_d|=dH(π)+O(log d): the maximal summand is the
last one for all sufficiently large d, since α<2/3. Its exponential
rate is H_bin(α)+α log 2=H(π). Combined with the dimension-free upper
bound this proves sharpness constructively for every sufficiently large
dimension and does not claim attainment for a single nontrivial set.
