# The zero-order boundary of actual APPT entropy: a uniform two-parameter transition

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

This determines the leading APPT entropy deficit when the Rényi order tends
to zero while the smaller local dimension grows. It covers every larger
dimension n≥m, including arbitrary diverging or oscillating aspect ratios.
The fixed-order subunit formula is not silently extrapolated: an additional
α log m transition changes the optimal coefficient. This note gives ordinary
mathematical proofs on the actual all-unitary APPT set. It is not a complete
Lean theorem, external peer review or priority certificate. It belongs to the
same growing-order APPT research direction as [the high-order paper](PAPER.md).

## 1. Quantities and the uniform theorem

For actual APPT densities ρ on C^m⊗C^n, 2≤m≤n, put D=mn, γ=n/m and

    E_α(m,n)=log D−min_APPT S_α(ρ),       0<α<1,
    S_α(ρ)=log Tr(ρ^α)/(1−α),
    W_α(m,n)=max{1, 1−m^(−α)+(α/2)γ}.

All powers at zero have their continuous positive-order meaning, 0^α=0.
Logarithms are natural. The minimum is over the original APPT density set.

**Theorem Z1 (every aspect at the zero-order boundary).** For every A_m→0
with A_m>0,

    sup_(n≥m, 0<α≤A_m)
       | D E_α(m,n)/W_α(m,n)−1 | →0        as m→∞.         (Z1)

In particular this applies to every path α→0, m→∞, uniformly in n≥m,
with no lower bound on α. It is a first nonzero equivalent, not an exact
finite-dimensional formula. The α=0 endpoint separately has
`min_APPT S_0=log(D−1)` and is consistent with W_0=1; it is not derived
by substituting zero into a divided kernel.

For example, if

    α log m→τ∈[0,∞),        α n/m→c∈[0,∞),

then

    D E_α(m,n)→max{1,1−e^(−τ)+c/2}.                      (Z2)

For finite τ the boundary between its two branches is c=2e^(−τ). The first
branch is realized by the uniform rank-(D−1) APPT state. The second is realized
by an actual full-rank negative-spike/projection family selected below.
Taking the fixed-order coefficient `1+αγ/2` through α→0 would instead give
`1+c/2`, which is wrong for finite τ and c>0.

**Theorem Z2 (near-minimizers at every finite transition point).** Suppose
τ and c are finite as in Z2. For any sequence of actual APPT densities, put

    ℓ=Dλ_D∈[0,1],      Q=Σ_i(Dλ_i−1)²,
    a=e^(−τ)>0.

Its entropy deficit attains the limit in Z2 if and only if:

* If c<2a: `ℓ^α→0`.
* If c>2a: `ℓ^α→a` and `Q/γ→1`.
* If c=2a: the distance of `(ℓ^α,Q/γ)` to `{(0,0),(a,1)}` tends to zero.

The critical condition permits alternation; it does not require a single
branch limit. Since c=2a>0 at the boundary, γ→∞ there. The same is true in
the c>2a case. In the first case c can be zero, so no assertion Q/γ→0 is
added: it need not hold on a bounded-aspect path. The high branch is eventually
full rank; the low branch allows both singular and sufficiently small positive
least eigenvalues. No eigenvector or exact finite-optimizer classification is
asserted.

## 2. Actual physical data and the least-eigenvalue width restriction

Use the companion actual-APPT notation, with m≥3:

    R=m(m−1)/2, S=m(m+1)/2, j=D−S+1,
    h_0=m−1, b=λ_j>0, t=1/(Db),
    z_i=λ_i/b−1,
    a_i=z_i≥0, β_i=−z_(D+1−i)≥0,
    g_i=a_i+β_i,  w=g_R,
    q=λ_D/b=1−β_1=tℓ.

Here q is a positive-or-zero pivot-relative least eigenvalue; ℓ is the actual
normalized least eigenvalue. They are kept distinct. The physical witnesses,
with full ordinary proofs in `ENTROPY_ASYMPTOTIC.md` Sections 2 and 4 and
`SHARP_ASPECT_RATIO.md` Section 3, give

    Σ_(i≤R) g_i²≤8,       h_0 w≤2,
    Σ_(i≤h_0)(a_i+β_(i+1))²≤4q,                          (Z3)
    |t−1|≤ν_m=1/m+2/(m−1)→0,
    Σ_i z_i²≤6C(m,n),  C=max{8,4+D/h_0²}.                (Z4)

The last estimate includes the true trace-centering term D(t−1)², rather than
discarding it. For reference it follows from the physical variance bound
`V/b²≤C`, with V=Σλ_i²−1/D, and the normalization estimate as in E19.
Every nonexceptional z_i, outside the first h_0 and last h_0+1 slots, has

    |z_i|≤ε_m=2/√h_0→0.                                  (Z5)

The shifted star also restricts the entire smallest paired gap. Since
h_0+1=m≤R for m≥3, for every i≤h_0 ordering gives

    a_i+β_(i+1)≥a_R+β_R=w.

Combining with Z3 yields

    h_0 w²≤4q,
    w²≤(4/h_0²)min{1,h_0 q}.                             (Z6)

This is a necessary bound for the actual spectrum. It couples a very small
least eigenvalue to the allowable width of the middle spectrum. It is why
one cannot independently attach an arbitrarily tiny hole to the full-width
bulk optimizer.

Centering the true spectrum at `(λ_R+λ_(D−R+1))/2`, as in F9, gives

    V/b²≤Σ_i g_i²−wΣ_i g_i+D w²/4
         ≤8+(D/h_0²)min{1,h_0 q}.                        (Z7)

For the centering step, each paired interval has distances u,v≥w/2 and sum
g_i after division by b, and hence squared-distance sum at most
`g_i²−w g_i+w²/2`. All other eigenvalues lie in the final interval of width
w. The trace mean minimizes the sum of squared distances. Thus Z7 follows
from actual eigenvalues and physical paired tests, not a model spectrum.

## 3. A uniform small-order state identity

The following Taylor and normalization comparisons are used once m exceeds a
common threshold with ε_m<1/2 and ν_m<1/2. This threshold is independent of
n and α. The preceding physical inequalities themselves hold in their
specified finite-dimensional range.

For 0<α≤1/2 let

    f_α(x)=[(1+x)^α−1−αx]/[α(α−1)],      x≥−1.

It is nonnegative. On |x|≤ε<1/2,

    f_α(x)=x²/2+O(εx²),                                  (Z8)

with an absolute constant uniform in α in this entire interval: its second
derivative is `(1+x)^(α−2)`, with exponent in [−2,−3/2].
The exact pivot/normalization identity from the subunit note is

    αΣ_i f_α(Dλ_i−1)
      =t^(−α)[αΣ_i f_α(z_i)−αD f_α(t−1)].                (Z9)

We do not lose its second, trace-centering term.

Let H consist of the first h_0 and last h_0+1 entries. Its least entry is
z_D=−(1−q). The other head entries have squared sum at most 4q, by Z3.
Their kernels are uniformly bounded by a constant times that squared sum:
for q≤1/16, β_2≤2√q≤1/2; for q≥1/16, all negative head entries satisfy
`1−β_i≥q≥1/16`. Taylor's integral bound then has a fixed coefficient.
Positive head entries have f_α(a)≤a²/2. Thus

    αΣ_(H) [f_α(z_i)−z_i²/2]
      =α f_α(q−1)+O(α)=1−q^α+O(α),                      (Z10)

uniformly for q∈[0,1]. The last step is exact up to its stated uniform bound:

    α f_α(q−1)=[1−q^α−α(1−q)]/(1−α),
    |α f_α(q−1)−(1−q^α)|≤α/(1−α).

At q=0 these formulas use 0^α=0 and remain valid. There is no α-independent
bound on f_α(−1) itself; multiplying by α first is essential.

Apply Z8 to the nonhead coordinates and t−1, using Z4–Z5. Exact centering gives

    αΣ_i f_α(z_i)−αD f_α(t−1)
      =1−q^α+(α/2)V/b²
          +O(α)+O[α(ε_m+ν_m)C(m,n)].                    (Z11)

Since `V/b²=t²Q`, t→1 uniformly and `t^(−α)=1+O(αν_m)`, Z9 becomes

    A_α(ρ):=αΣ_i f_α(Dλ_i−1)
      =1−ℓ^α+(α/2)Q+o(1+αγ),                            (Z12)

uniformly for n≥m and 0<α≤A_m→0. Indeed `q^α=t^αℓ^α` differs from ℓ^α by
O(αν_m), since 0≤ℓ≤1, and `αC=O(α+αγ)` controls the remainders. Uniformity
here means a common error bound divided by 1+αγ tends to zero for the whole
order/dimension range, not separate fixed-α estimates.

The exact entropy identity is

    D[log D−S_α(ρ)]
       =−D/(1−α) log[1−(1−α)A_α(ρ)/D].                  (Z13)

The physical upper bounds give `A_α=O(1+αγ)`, uniformly. Thus
`A_α/D=O(D^(−1)+α/m²)→0` for the whole range. Taylor of this logarithm is
therefore uniform in its actual positive argument, and Z12 also gives

    D[log D−S_α(ρ)]
       =1−ℓ^α+(α/2)Q+o(1+αγ).                           (Z14)

This is an identity at the stated asymptotic scale for every actual APPT
state, not just an upper bound or an extremizer ansatz.

## 4. Optimize the unrestricted upper bound

Using Z7 in Z11 first, then Z9/Z13, gives the sharper least-eigenvalue-sensitive
bound

    D[log D−S_α(ρ)]
      ≤1−q^α+c_m min{1,h_0 q}+o(1+αγ),
    c_m=αD/(2h_0²).                                     (Z15)

The factor t^(−α), the logarithm and the constant eight contribute only
to the uniform error already accounted for. Optimize over all q∈[0,1].
For q≥1/h_0 the maximum is at q=1/h_0 and equals
`1−h_0^(−α)+c_m`. For q≤1/h_0 put u=h_0 q∈[0,1]. The function is

    1−h_0^(−α)u^α+c_m u.

Because u^α is concave, this expression is convex. Its maximum is at an endpoint,
giving exactly

    max_(0≤q≤1)[1−q^α+c_m min{1,h_0q}]
       =max{1,1−h_0^(−α)+c_m}.                            (Z16)

Finally `c_m=(αγ/2)[m/(m−1)]²`, and
`|h_0^(−α)−m^(−α)|=O(α/m)`. Replacing them by the canonical quantities changes
Z16 by o(1+αγ), uniformly in n. Since W_α is at least max{1,αγ/2}, it is
comparable with 1+αγ. This proves the unrestricted limsup in Z1.

## 5. Matching actual APPT states for both branches

The uniform rank-(D−1) state

    ρ_sing=(I−vv*)/(D−1)

is APPT after every global U: the largest eigenvalue of any partial-transposed
unit pure projector is at most one, so `I−(Uvv*U*)^Γ` is positive semidefinite.
For every α>0 its entropy is log(D−1), and

    D[log D−S_α(ρ_sing)]=D log[D/(D−1)]→1                 (Z17)

uniformly D≥m². This realizes the first branch exactly at finite dimension.

To realize the second, for m sufficiently large and 0<α≤1/2 choose an integer

    H=max{1, floor(min{√m, exp(1/√α)})},
    b_0=(H+1)m,       d=b_0−H²≥0,
    k=floor(D/2).

Uniformly for α≤A_m→0, one has H→∞, H/m→0 and

    α log H≤√α→0.                                       (Z18)

The inequality follows because the minimum is no greater than exp(1/√α).
The floor does not obstruct H→∞: both arguments in the minimum tend to infinity
uniformly. Choose P of rank k and a unit v orthogonal to its range. Define

    B=b_0 I+2HP−d vv*,
    Z=(D−1)b_0+2Hk+H²,       ρ_H=B/Z.                    (Z19)

This is the previously established actual finite downward-spike family;
only the order-dependent parameter selection is new. It is positive because
`b_0−d=H²>0` and P≥0, and trace-normalizes to a full-rank density.

For every global unitary and every Schmidt witness, the projection contribution
is at least `−2HΣ_(i<j)s_i s_j`, while the negative pure contribution is at least
`−d s_1²`, using the largest partial-transpose eigenvalue s_1². Put
r=m−1, T=Σ_(i≥2)s_i and Q_0=Σ_(i≥2)s_i². The sufficient quadratic has the
exact identity

    b_0Σ_i s_i²−2HΣ_(i<j)s_i s_j−d s_1²
       =(Hs_1−T)²+(H+1)(rQ_0−T²)+(2H+1)Q_0 ≥0.           (Z20)

Cauchy gives rQ_0≥T². Hence Z19 is an actual all-global-unitary APPT state.
It is not obtained by reflecting a positive-spike spectrum and assuming APPT.

Let

    p_0=H²/[(H+1)m],       κ=2H/[(H+1)m],
    θ=k/D,                z=Z/(Db_0)=1+κθ−(1−p_0)/D.

The actual normalized spectrum has κ-upper entries `(1+κ)/z` (k copies),
middle entries `1/z` (D−k−1 copies), and one least entry

    ℓ=p_0/z.

Here p_0≤H/m→0 and z→1 uniformly; κm→2 and θ→1/2. In particular

    ℓ^α=m^(−α) exp{α log[H²/(H+1)]−α log z}
        =m^(−α)+o(1),                                   (Z21)

uniformly in the entire range, by Z18 and m^(−α)≤1. For every other coordinate
`|Dλ_i−1|=O(1/m)`. Its exact squared sum is

    Q_rest=[D κ²θ(1−θ)+(1−p_0)²/D
             −(κθ−(1−p_0)/D)²]/z²,                     (Z22)

obtained by summing the full two-level baseline squares and removing the
selected lower baseline coordinate where the hole was placed. Thus
`Q_rest/γ→1` uniformly, and the least-coordinate square contributes at most one.
Applying the actual-state identity Z14 gives

    D[log D−S_α(ρ_H)]
       =1−m^(−α)+(αγ/2)[1+o(1)]+o(1).                   (Z23)

Both errors are uniform, not an O_α term evaluated at a moving order. Taking the
better of Z17 and Z23 proves the matching lower half of Z1. Taking a maximum
does not introduce an existence gap: both are explicit actual density sequences
at each permitted parameter pair.

## 6. The complete finite-window near-minimizer classification

Assume τ,c finite and put a=e^(−τ)>0. Z14 gives for any actual sequence

    D[log D−S_α(ρ)]=1−ℓ^α+(c/2)(Q/γ)+o(1).              (Z24)

For c>0, γ→∞. Z7, t→1 and q=tℓ also imply

    Q/γ≤min{1,mℓ}+o(1).                                  (Z25)

For clarity, the errors before passing to this finite-c window are O(1/m)
and 8/γ. For c=0, the weaker bound Q=O(1+γ) instead gives αQ→0 directly.

Here is the crucial constraint between possible limiting data. If
`ℓ^α≤a−ε` along a subsequence, then

    (mℓ)^α=m^αℓ^α≤1−ε/(2a)<1

eventually. As α→0 this forces mℓ→0, and hence Q/γ→0 when c>0.
Thus any subsequential limit z of ℓ^α below a has zero variance coordinate.
The variance coordinate is always at most one asymptotically when c>0.
These are physical restrictions, not arbitrary independent choices of z and Q.

If c<2a and c>0, any limit z<a has entropy limit 1−z, which is optimal only
at z=0. Any limit z≥a has entropy limit at most `1−a+c/2<1`. Compactness
therefore forces ℓ^α→0. Conversely that condition makes mℓ→0 and αQ→0,
so Z24 gives one. If c=0, Z14 already reduces to `1−ℓ^α+o(1)` and proves
the same equivalence, without the unnecessary claim Q/γ→0.

If c>2a, the optimal value `1−a+c/2` is strictly above one. A limit z<a
has zero variance coordinate and value at most one. A limit z≥a satisfies

    entropy limit ≤1−a+c/2−(z−a)−(c/2)(1−q_*),

where q_* is its limiting Q/γ∈[0,1]. Optimality forces z=a and q_*=1.
The converse follows directly from Z24.

At c=2a, the optimum is one. Limits with z<a must have z=0 and q_*=0;
limits with z≥a must have z=a and q_*=1. Compactness gives exactly the
distance-to-two-points statement in Z2, and Z24 gives its sufficiency even
for alternating sequences. Z17 and Z19–Z23 realize the two alternatives.
The high branch has ℓ^α→a>0, so it cannot have infinitely many zero least
eigenvalues; it is eventually full rank. The low branch permits the explicitly
singular optimizer, or a full-rank arbitrarily small-hole approximation.

This proves Z2. No equivalence of state observations or eigenvectors is
silently added to this spectral entropy classification.

## 7. Verification, attribution and scope

The required actual-APPT physical estimates are explicitly identified in the
proof/formalization map. The finite negative-spike family was already developed
and its actual all-unitary construction is part of the existing APPTSubunit
core, subject to its exact source types. The uniform α→0 kernel analysis,
dimensional optimization, adaptive limits and Z1/Z2 are not in its old
8-module/39-root audit. No module, root, axiom or audit scope is added here.

The contemporary primary-source comparison in [the companion high-order note](PAPER.md)
remains bounded: Ahiable–Kothakonda–Winter and Tran discuss von Neumann and
finite-dimensional spectral optimization; no matching zero-order joint window
was identified in the actual statements read. This is not historical priority
certification. The elementary singular spectrum and the finite projection/
negative-spike construction are credited as existing inputs. Their reuse does
not count as additional independent breakthroughs.

Unresolved scope includes arbitrary moving orders that stay away from both
endpoints, α comparable to m with unrestricted aspect, fixed-m changing-order
minima, exact finite minima and complete formalization. The proof does not
infer absolute separability from APPT. No new Release, DOI, aiXiv submission
or external human peer-review status is asserted.
