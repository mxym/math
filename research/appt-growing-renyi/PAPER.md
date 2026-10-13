# Growing Rényi orders of actual APPT states: bulk competition and the min-entropy crossover

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. Research proof, 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

This closes two growing-order regimes that do not follow by exchanging limits
in the repository's fixed-order Rényi theorems. It also gives a full leading-scale
spectral criterion in the bounded-aspect growing-order regime. The projection-
plus-spike family and the exact largest-eigenvalue endpoint are existing inputs,
not newly invented constructions. The uniform order/dimension analysis is given
below on the actual all-global-unitary APPT set. These are complete ordinary
mathematical proofs in the stated ranges, not complete Lean formalizations,
external peer review, or historical-priority certification.

## 1. Objects, quantities and the exact results

Let 2≤m≤n, D=mn. A density matrix ρ on C^m⊗C^n is APPT if `(UρU*)^Γ` is
positive semidefinite for every global unitary U. Write its actual ordered
eigenvalues as λ_1≥...≥λ_D≥0, and put y_i=Dλ_i. For α>1 define

    M_α(ρ)=D^(α−1) Tr(ρ^α)=(1/D)Σ_i y_i^α,
    M*_α(m,n)=max_(ρ actual APPT) M_α(ρ),
    E_α(m,n)=log D−min_(ρ actual APPT) S_α(ρ)
             =log M*_α(m,n)/(α−1),
    u_D=3D/(D+2),       γ=n/m.

All logarithms are natural. Compactness and continuity give the maxima/minima.
Jensen gives M_α≥1. All limits below have m→∞, so the finitely many m=2 cases
are not omitted from a claimed finite theorem; they are outside the growing-m
asymptotic assertion.

**Theorem G1 (growing sublinear order, every aspect ratio).** Let L_m→∞ and
U_m/m→0, with 2≤L_m≤U_m eventually. Then

    sup_(n≥m, L_m≤α≤U_m)
    | [M*_α(m,n)−1] /
       [u_D^α/D + α(α−1)/(2m²)] −1 | →0.                   (G1)

In particular, this holds on every path α→∞, α=o(m), uniformly over all n≥m,
including arbitrary diverging or oscillating aspect ratios. It implies

    E_α(m,n) ~ log[1+u_D^α/D+α(α−1)/(2m²)]/(α−1).           (G2)

The error in `(α−1)E_α−log[1+u_D^α/D+α(α−1)/(2m²)]` tends to zero as well.
The two positive moment contributions can be comparable; taking their maximum
instead of their sum would miss that transition.

**Theorem G2 (bounded aspect, every diverging order).** For every fixed Γ≥1
and every L_m→∞,

    sup_(m≤n≤Γm, α≥L_m)
      | D[M*_α(m,n)−1]/u_D^α −1 | →0.                     (G3)

There is no upper bound on α: it can grow faster than m or D. Consequently

    E_α(m,n) ~ log(1+u_D^α/D)/(α−1),                       (G4)
    (α−1)E_α(m,n)−log(1+u_D^α/D) →0,

uniformly in that same range. The exact u_D, rather than an unqualified 3,
is retained because α can be arbitrarily large.

**Theorem G3 (complete bounded-aspect leading spectral criteria).** On any
bounded-aspect path with α→∞, let ρ be any sequence of actual APPT densities.
Define

    χ=α log u_D−log D,
    h=α log[u_D/(Dλ_1)]≥0,        χ_+=max{χ,0}.

Then

    (M_α(ρ)−1)/(M*_α−1) →1   iff   h→0;                  (G5)

    [log D−S_α(ρ)]/E_α →1   iff   h/(1+χ_+)→0.            (G6)

Thus the sharp moment-excess criterion resolves the top eigenvalue to o(1/α).
Relative entropy-deficit optimality has the weaker tolerance o(χ/α) once
χ→+∞. Either criterion forces Dλ_1→3, every other normalized eigenvalue to
tend uniformly to one, and eventual full rank. It does not require the purity
coefficient to attain its fixed-order maximum.

These theorems do not claim a complete growing-order law when α is comparable
to m and the aspect ratio is unrestricted, or a fixed-m growing-order theorem.
The α→0 boundary and exact finite minima remain separate. All stated uniform
quantifiers are proved below.

## 2. Actual physical inputs and a bounded exceptional spectrum

We use the physical rearrangement and shifted-star inequalities already proved
in the companion notes. Their actual definitions are retained here. For m≥3 let

    R=m(m−1)/2,    S=m(m+1)/2,    j=D−S+1,    h_0=m−1,
    b=λ_j>0,      t=1/(Db),
    a_i=λ_i/b−1,   β_i=1−λ_(D+1−i)/b,
    g_i=a_i+β_i=(λ_i−λ_(D+1−i))/b,      i≤R.

The all-unitary Schmidt witnesses imply

    Σ_(i≤h_0) g_i²≤4,      Σ_(i≤R) g_i²≤8,
    Σ_(i≤R) g_i≤m,         g_R≤2/h_0,                     (G7)
    Σ_(i≤h_0)(a_i+β_(i+1))²≤4(1−β_1).                    (G8)

The four-unit star is E7, the shifted star is E8 in
`ENTROPY_ASYMPTOTIC.md`. The eight-unit entire paired-gap estimate is A8 in
Section 3 of `SHARP_ASPECT_RATIO.md`: it uses a physical star rearrangement
and an independent rectangular rearrangement with its within-part weights.
It holds for every n≥m, not only the aspect ratios where that intermediate
note first obtained a sharp purity coefficient. These are necessary physical
tests of the original APPT set, not premises on a surrogate spectral set.

For clarity, the nonnegative gap adjacency matrix for *every* edge placement
has norm at most 2, by assigning the top R eigenvalues to negative Schmidt
pair vectors, the bottom R to positive pair vectors, and the remaining m
low eigenvalues to diagonal vectors. All slots are distinct since D≥m².
The star yields the first inequality in G7. The rectangular estimate retained
the weights inside both parts and proves the second; its full proof is linked
above. The uniform-vector Rayleigh test gives the sum bound and hence g_R.
The shifted star separately places the least eigenvalue at its central diagonal,
which gives G8. No caller-supplied Schmidt interface is assumed.

The maximally entangled rank-m witness gives

    Σ_(i≤R)λ_i≤Σ_(i≥j)λ_i,
    λ_R≤[(m+1)/(m−1)]b.                                  (G9)

Its R negative and S positive values are all ±1/m. This also proves b>0:
otherwise the least-S sum vanishes, then all eigenvalues vanish, contradicting
trace one. The companion normalization estimate is

    |t−1|≤ν_m:=1/m+2/h_0 →0.                              (G10)

Indeed top-R positive pivot deviations sum to at most m. Every further positive
deviation is at most 2/h_0 by G9. The bottom-R negative magnitudes sum to at most
m; the remaining at most m bottom slots have magnitude at most g_R. Summing and
dividing by D yields the stronger `m/D+2/h_0`, and G10 follows from D≥m².

Use the actual middle set B={R,...,j}; it has N_B=D−m²+2 entries. Its complement
E has m²−2 entries. On B, G9 gives 0≤λ_i/b−1≤2/h_0, so for x_i=y_i−1,

    |x_i|≤δ_m:=(2/h_0+ν_m)/(1−ν_m)=O(1/m).                (G11)

For E, put z_i=λ_i/b−1. Paired a_i and β_i are nonnegative for i≤R and
`a_i²+β_i²≤g_i²`. The bottom indices R+1,...,S−1 have β_i≤g_R≤2/h_0.
Consequently

    Σ_(i∈E) z_i² ≤8+4/h_0,
    Q_E:=Σ_(i∈E)x_i² ≤C_m,
    C_m=[√(8+4/h_0)+mν_m]²/(1−ν_m)²=O(1).                (G12)

The second inequality is the Euclidean triangle inequality applied to
`x_i=[z_i−(t−1)]/t`, using |E|≤m². This is why the exceptional contribution
stays bounded even when n/m diverges.

The same triangle inequality on the top h_0 positive parts gives

    Σ_(i≤h_0)(x_i)_+² ≤H_m,
    H_m=[2+√h_0 ν_m]²/(1−ν_m)² →4.

Since h_0≥2 and x_1≥x_2,

    y_2≤v_m:=1+√(H_m/2) →1+√2<3.                         (G13)

If x_2≤0 the bound is immediate; otherwise both largest positive squares
are at least x_2². This is a gap for the actual second-largest eigenvalue,
not an assumption of a single-spike spectral shape.

The finite physical purity estimate E17 is

    Q:=Σ_i x_i² ≤max{8,4+D/h_0²}/(1−ν_m)²
                 ≤ζ_m(γ+8),
    ζ_m=(m/h_0)²/(1−ν_m)² →1.                            (G14)

Finally the rank-two uniform witness gives

    λ_1≤λ_D+λ_(D−1)+λ_(D−2)≤3(1−λ_1)/(D−1),
    y_1≤u_D=3D/(D+2).                                    (G15)

The first inequality puts λ_1 in the negative pair slot and the three least
values in the positive slots. The average of the three least tail values is
at most the average of the whole D−1 tail. The endpoint is attained by
`ρ_sp=(I+2vv*)/(D+2)`, whose all-unitary APPT property follows because every
partially transposed unit pure projector has smallest eigenvalue at least −1/2.
This exact endpoint was already recorded in the companion Section 13.

## 3. Real-power estimates and the unrestricted upper bounds

For α≥2 and −1≤x define

    f_α(x)=[(1+x)^α−1−αx]/[α(α−1)].

Taylor's integral identity, with continuity at x=−1, is

    f_α(x)=x² ∫_0^1 (1−s)(1+sx)^(α−2) ds.                (G16)

Thus f_α≥0. If −1≤x≤V−1 with V≥1, then

    f_α(x)≤(x²/2)V^(α−2).                                (G17)

If |x|≤δ<1, it is bounded on both sides by
`(x²/2)(1−δ)^(α−2)` and `(x²/2)(1+δ)^(α−2)`.
Since trace one gives Σ_i x_i=0, the exact moment identity is

    D[M_α(ρ)−1]=α(α−1)Σ_i f_α(x_i).                     (G18)

Isolate the actual largest term in E and bound every other exceptional term
with G12–G13 and G17. This gives

    D[M_α(ρ)−1]≤u_D^α +[α(α−1)/2]C_m v_m^(α−2)
                    +[α(α−1)/2](1+δ_m)^(α−2) Q_B,       (G19)

where Q_B=Σ_(i∈B)x_i². The isolated term is exactly
`y_1^α−1−α(y_1−1)` and is at most u_D^α because y_1≥1.

For G1, α≤U_m=o(m) makes `(1+δ_m)^(α−2)=1+o(1)` uniformly. Equation G14
bounds Q_B by ζ_m(γ+8). The bounded exceptional term satisfies

    sup_(α≥L_m)
      α(α−1)C_m v_m^(α−2)/u_D^α →0,                      (G20)

uniformly in n≥m. To verify this directly, eventually v_m≤5/2 and u_D≥8/3;
C_m is bounded, so it is bounded by a constant times `α²(15/16)^α`.
The supremum over α≥L_m tends to zero. Similarly α²/u_D^α→0 uniformly there.
Thus the extra eight units in G14 have negligible contribution compared with
u_D^α. Divide G19 by

    T_α(m,n)=u_D^α+[α(α−1)/2]γ.                           (G21)

Its unrestricted limsup is at most one uniformly in all n and permitted α.
The ratio error depends only on m, L_m and U_m, not γ.

For bounded aspect Q=O_Γ(1) by G14. Apply G17 to *all* entries other than the
largest, now using G13, without any Taylor flatness requirement. It gives the
stronger actual-state estimate

    |D[M_α(ρ)−1]−y_1^α|
       ≤1+2α+[α(α−1)/2]Q v_m^(α−2).                     (G22)

The difference consists of the nonnegative remaining kernels and the isolated
subtraction `1+α(y_1−1)`, which is at most 1+2α. Divide by u_D^α and use
G20. Uniformly over every actual state and every α≥L_m,

    D[M_α(ρ)−1]/u_D^α=(y_1/u_D)^α+o(1).                 (G23)

In particular this proves the upper half of G3 for every diverging α, with
no relation between its size and m or D.

## 4. A finite physical lower state matching both G1 contributions

For α≥2 set

    H=ceil(√(αm)),
    c=2/(m+H),        q=2−(m−3)c=2(H+3)/(m+H)>0,
    a=2−2(m−2)c²/q,
    d=a−c,           k=ceil((m−1)n/2).

These are the previously proved projection-plus-spike parameters, with a new
order-dependent choice of the integer H. One has

    d q=[2−(m−1)c](2+c)>0.                               (G24)

Let P be any rank-k orthogonal projection and v a unit vector in its range.
The positive matrix and actual normalized density are

    A=I+cP+d vv*,           ρ_H=A/Z,
    Z=D+ck+d=D+a+(k−1)c.                                 (G25)

No numerical positivity test is used. For an arbitrary global U and an arbitrary
unit Schmidt witness with nonnegative coefficients s_1≥s_2≥...≥s_m,
the pure partial-transpose witness W has negative eigenvalues −s_i s_j and
smallest eigenvalue −s_1s_2. Hence

    Tr[(UPU*)W]≥−Σ_(i<j)s_i s_j,
    Tr[(Uvv*U*)W]≥−s_1s_2.

It suffices to prove nonnegativity of
`Σ s_i²−cΣ_(i<j)s_i s_j−d s_1s_2`. Put r=m−2, A_0=s_1+s_2,
B_0=s_1−s_2, T=Σ_(i≥3)s_i, Q_0=Σ_(i≥3)s_i² and

    J=1−c(r−1)/2=q/2,       R_0=J/r>0.

The exact scalar identity is

    Σ s_i²−cΣ_(i<j)s_i s_j−d s_1s_2
      =(2+c+d)B_0²/4
        +(1+c/2)(Q_0−T²/r)
        +R_0[T−cA_0/(2R_0)]².                            (G26)

Indeed `2−c−d=r c²/J=c²/R_0`; expanding the square gives the cross term
`−cA_0T` and its required `c²A_0²/(4R_0)` coefficient. Cauchy gives
Q_0≥T²/r, and all coefficients are nonnegative. The identity even holds for
arbitrary real s_i. It proves the actual all-unitary APPT implication. Since
A≥I and Z>0, ρ_H is an actual full-rank density. Standard Schmidt decomposition
is the only finite-dimensional background input.

The exact spectrum is

    y_1=D(1+a)/Z,
    y_i=D(1+c)/Z  for k−1 entries,
    y_i=D/Z      for D−k entries.                         (G27)

Write θ=k/D and z=Z/D=1+cθ+d/D. Let

    ε=2−a=4(m−2)/[(m+H)(H+3)]≤4/(H+3).

Since c≤2/m and 0<d≤2, G15 and G27 give

    0≤α log(u_D/y_1)
       ≤α[2/m+2/D+2/(H+3)].                             (G28)

For H≥1, ε≤1, and the last bound follows from
`log(3/y_1)=log z−log(1−ε/3)≤cθ+d/D+ε/(3−ε)`.
Uniformly over L_m≤α≤U_m=o(m), H/m→0 and α/(H+3)≤√(α/m)→0.
Thus `y_1^α/u_D^α→1`, with the needed o(1/α) peak resolution actually proved.

Every other normalized deviation has absolute value at most 4/m+2/D.
Its exact squared sum is

    Q_rest=[D c²θ(1−θ)+d²/D−(c−cθ−d/D)²]/z².             (G29)

To verify it, sum `(c−cθ−d/D)²` over the k baseline upper slots and
`(−cθ−d/D)²` over the D−k baseline lower slots; the cross mean vanishes.
Remove the selected upper slot containing the extra spike. The result is G29.
Since

    θ=(m−1)/(2m)+O(1/D),    mc→2,    z→1,

one gets `Q_rest/γ→1` uniformly in n≥m and the entire stated order window.
The correction in G29 divided by γ is O(1/m²); γ≥1 prevents a hidden
fixed-aspect assumption. The small-deviation power estimate from G16 now gives

    D[M_α(ρ_H)−1]
       =y_1^α−1−α(y_1−1)+[α(α−1)/2]Q_rest[1+o(1)]
       =u_D^α[1+o(1)]+[α(α−1)/2]γ[1+o(1)].             (G30)

The subtracted polynomial is negligible against u_D^α uniformly α→∞.
This matches the upper bound G19–G21, proving G1.

For G2 use the elementary pure-spike state from G15. Let t_D=D/(D+2); its
moment is

    M_α(ρ_sp)=[u_D^α+(D−1)t_D^α]/D.

For real α≥1, convexity gives `1−t_D^α≤α(1−t_D)`. Therefore

    |D[M_α(ρ_sp)−1]−u_D^α|≤1+2α=o(u_D^α)                (G31)

uniformly α≥L_m. Together with G23 this proves G3. It is essential to retain
t_D^α when α is very large rather than expanding it under an unproved α=o(D)
assumption.

For any positive T and |η|≤ε<1, concavity of log(1+x) implies

    log[1+(1−ε)T]/log(1+T)≥1−ε,
    log[1+(1+ε)T]/log(1+T)≤1+ε.

It also bounds the absolute difference from log(1+T) by a quantity tending to
zero with ε, uniformly T>0. These facts turn G1/G3 into their relative entropy
equivalents and additive logarithmic statements G2/G4. No small-log assumption
is applied in the critical or supercritical regimes.

## 5. Bounded-aspect spectral criteria and the distinction between scales

In bounded aspect, G23 and G3 immediately identify sharp moment-excess
optimality with `(y_1/u_D)^α→1`. Since y_1≤u_D and y_1≥1, this is equivalent
to `h=α log(u_D/y_1)→0`. This proves G5.

For G6 first show that relative entropy-deficit optimality forces y_1→3.
If χ is bounded above on a subsequence, the optimal moment excess is bounded
and the logarithm is strictly increasing. Uniformly for r in a bounded
nonnegative interval, with its continuous value at r=0,

    log(1+ar)/log(1+r)→1,  0≤a≤1,   iff a→1.

The assertion follows by continuity/compactness: when a≤1−ε its supremum is
strictly below one, including the r=0 limit a. It applies to the actual moment
ratio, so G5 gives y_1→3 on such subsequences.

On a subsequence with χ→+∞, suppose instead y_1≤3−ε. Taylor G17 with the
actual maximum y_1 and Q=O_Γ(1) gives

    log M_α(ρ)≤log[1+e^χ O_Γ(α²)(y_1/u_D)^α].            (G32)

Here `α log(u_D/y_1)≥c_ε α` eventually, while χ≤α log3. If χ/logα is
unbounded, dividing G32 by χ shows a fixed loss of at least c_ε/log3
asymptotically (or the bound collapses to zero). If χ=O(logα) on a further
subsequence, the exponent is negative of order α and the ratio tends to zero.
Both contradict entropy optimality, since `log M*~χ`. This exhausts
subsequences and proves y_1→3 necessarily.

Whenever y_1→3, divide G22 by y_1^α instead of u_D^α. For all large m,
y_1≥8/3 and v_m≤5/2, so the error is at most a bounded constant times
`α²(15/16)^α+(1+2α)/(8/3)^α`. It tends to zero uniformly. Hence

    M_α(ρ)−1=(y_1^α/D)[1+o(1)].                          (G33)

After taking log, the actual-to-optimal entropy ratio is asymptotic, in
relative terms even when χ→−∞, to

    log(1+e^(χ−h))/log(1+e^χ).                            (G34)

For χ bounded above, this tends to one exactly when h→0; use the same compact
comparison, now with a=e^(−h). For χ→+∞ it tends to one exactly when h/χ→0,
because the numerator is `(χ−h)_++O(1)` and the denominator is χ+o(1).
The two subsequence cases give the single criterion `h/(1+χ_+)→0`.

Conversely that criterion first implies

    h/α≤[h/(1+χ_+)](1/α+log3)→0,

so y_1→3 and G33 applies. The scalar comparison then proves entropy optimality.
This closes both directions of G6 without conflating moment and entropy scales.

Finally y_1→3 and t→1 make a_1→2. The first star budget G7 makes every other
top head deviation tend to zero; G8 makes β_1→0. Ordering and the remaining
small-gap bound make every normalized eigenvalue other than y_1 tend uniformly
to one. In particular the least is eventually positive. These statements use
the actual physical inequalities, not empirical spectral convergence alone.

Two actual examples expose the difference from fixed-order rigidity.

* The exact pure spike has Q→4, whereas the fixed-aspect sharp purity coefficient
  is max{8,4+γ}. It nevertheless attains G3 for every α→∞. Optimal purity is
  therefore not a necessary condition for growing-order moment optimality.
* In square dimensions take α=m and the APPT state proportional to
  `I+(2−1/√α)vv*`. Then y_1→3, h~√α/3→∞ and χ~α log3. It satisfies G6 but
  its normalized moment excess tends to zero relative to the optimum. This
  is an actual APPT sequence, since reducing the positive pure-spike strength
  below two preserves the all-unitary bound. It disproves any attempted
  replacement of the entropy criterion by h→0 in the supercritical regime.

## 6. Crossover consequences

For bounded aspect and α→∞, the entire order/dimension transition is governed
by `χ=α log u_D−log D`.

| Regime | Sharp entropy consequence |
| --- | --- |
| χ→−∞ | `E_α~u_D^α/[D(α−1)]` |
| χ→z finite | `(α−1)E_α→log(1+e^z)` |
| χ→+∞ | `E_α~[α log u_D−log D]/(α−1)` |
| α/log D→c∈(0,∞) | `E_α→max{0,log3−1/c}` |
| α/log D→∞ | `E_α→log3`, consistently approaching the exact min-entropy endpoint |

At the critical scale `α=(log D+z)/log3`, u_D^α/3^α→1, so the middle row is
the explicit `log(1+e^z)` window. This is derived from the uniform finite-α
theorem, not a dimension/order interchange. If α/log D→0 with α→∞, the
first row supplies its nonzero small-deficit scale.

For arbitrary aspect with α=o(m), G1 adds a second competition:

    peak/bulk moment ratio =2u_D^α/[γ α(α−1)].              (G35)

When this tends to infinity the peak term determines the equivalent. When it
tends to zero the deficit is `E_α~α/(2m²)`. If it tends to a positive finite
constant, both positive terms must be kept. In the latter two regimes the
optimal moment increment tends to zero since α=o(m), so linearizing the
logarithm there is justified. The leading-order law is uniform even when
the aspect ratio itself oscillates across these regimes.

## 7. Literature, verification and remaining gaps

The contemporary primary sources checked in this round are Ahiable–Kothakonda–
Winter [arXiv:2608.03390v2](https://arxiv.org/html/2608.03390v2), especially
Section 6.2, and Tran [arXiv:2609.18568v1](https://arxiv.org/html/2609.18568v1),
Section 3. They discuss von Neumann optimization, spectral relaxations and
related finite-dimensional results. Their actual entropy statements were read;
no matching theorem for the growing-order regimes G1–G6 was identified in those
sources or the targeted searches. This is bounded literature screening, not a
proof of historical priority. The existing spectral constructions and endpoint
are explicitly credited to their prior setting; standard power/Taylor/convexity
arguments are not presented as newly invented principles.

The [proof/formalization map](THEOREM_MAP.md) was established before this full
manuscript. It identifies the required actual physical inputs and marks G1–G6
unformalized. The old APPTSubunit 8-module/39-root certificate and the separate
positive lacunary companion certificate retain their original scope. No audit
record is relabeled as proving these new order-dependent limits.

`check_growing_orders.py` uses standard-library rational arithmetic to check
252 exact scalar SOS specializations, including signed coordinates, and one
actual rational 25×25 density whose partial transpose rejects a deliberately
wrong protection factor. Its normalized negative value is −9/3269. Fifteen
growing-order spectral evaluations supplement the limit analysis, including
aspect ratios of enormous integer size. The ordinary and assertion-disabled
runs passed. These finite checks do not prove the all-dimension upper bound,
the uniform lower limits or the spectral criteria; those proofs are above.

Unresolved scope includes unrestricted-aspect orders α comparable to m or larger,
fixed-m growing-order minima, the α→0 boundary, exact finite optimizers,
historical-first certification and complete formalization. No absolute-separability
or generic entanglement-distillation conclusion is inferred. No new Release,
DOI, aiXiv submission or external human peer-review status is asserted here.
