# A uniform APPT Rényi profile over every positive order

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. Research proof, 14 October 2026, Asia/Shanghai.
No external funding; OpenAI AI assistants assisted. Original material:
copyright 2026 Yongxian Zhang, all rights reserved.

The new zero- and high-order windows, together with the existing fixed-order
theorems, determine one relative equivalent uniformly over **all positive Rényi
orders in bounded aspect**. They also determine every order below an arbitrary
sublinear threshold uniformly over **every aspect ratio**. This is one APPT
entropy research direction, not separate counted conjecture breakthroughs.
The proof is ordinary mathematics; none of the new profile theorems is included
in the old partial Lean audits or externally peer reviewed.

## 1. A single explicit profile and its exact ranges

For actual APPT densities on C^m⊗C^n, 2≤m≤n, put

    D=mn,   γ=n/m,   B=max{4,γ},   u_D=3D/(D+2),
    E_α(m,n)=log D−min_APPT S_α,        α>0,

with S_1 the continuous von Neumann value. Define

    P_α(m,n) =
      (1/D) max{1,1−m^(−α)+(α/2)B},             0<α<1/2;
      (1/D) [2α+(α/2)B],                       1/2≤α≤2;
      (1/(α−1)) log[1+(u_D^α−1−2α)/D
                           +α(α−1)B/(2D)],      α>2.      (U0)

For sufficiently large m all arguments and denominators are positive. In the
last branch, u_D≥8/3 and α≥2 imply u_D^α−1−2α>0. That expression is
increasing for α≥2, since its derivative is u_D^α log u_D−2>0.
At the two branch points the finite formulas need not coincide exactly;
their relative mismatch tends to zero. This is an asymptotic profile, not
an exact finite-dimensional interpolation or optimizer formula.

**Theorem U1 (all orders in every bounded aspect range).** For every Γ≥1,

    sup_(m≤n≤Γm, α>0) | E_α(m,n)/P_α(m,n)−1 | →0
    as m→∞.                                              (U1)

The supremum covers arbitrary order/dimension paths and oscillations, including
α→0, either finite transition α→1/2 or α→2, the logarithmic min-entropy
window, and α growing faster than D.

**Theorem U2 (all aspects up to every sublinear order threshold).** If U_m≥2
eventually and U_m/m→0, then

    sup_(n≥m, 0<α≤U_m) | E_α(m,n)/P_α(m,n)−1 | →0.        (U2)

This includes arbitrary larger-dimension growth, not only a fixed γ. It excludes
unrestricted-aspect orders comparable to m or larger. U1 handles those orders
when the aspect remains bounded; no statement merges the excluded general
case into either proven range.

The exact α=0 and α=∞ endpoints remain the existing formulas
`E_0=log[D/(D−1)]` and `E_∞=log u_D`. They are not substitutions into
undefined divisions in U0. The finite-positive-order uniform statement is
proved directly, so its growing-order consequences do not rely on exchanging
two nonuniform limits.

## 2. Fixed-order inputs and compact uniformity

The complete inherited mathematical theorems in `SUBUNIT_RENYI.md` and
`ENTROPY_ASYMPTOTIC.md` give, for each fixed α>0,

    E_α(m,n) ~ Φ_α(γ)/D        uniformly n≥m,
    Φ_α(γ)=A_α+(α/2)max{4,γ},
    A_α=max{1,2α},                         0<α≤2,
    A_α=(3^α−1−2α)/(α−1),                  α≥2.          (U3)

The values agree at α=2, and α=1 has its established continuous value.
These inputs optimize actual all-unitary APPT states; no spectral relaxation
is substituted. Their complete written dependency chains, with their exact
formalization gaps, remain the cited companion proofs.

First make U3 uniform on every compact order interval I⊂(0,∞). For each fixed
state, Rényi entropy decreases with α. One direct proof is that
`F(α)=log Σ_(λ_i>0) λ_i^α` is convex and F(1)=0; its secant slope through
one increases with α, while S_α is the negative of that slope. The derivative
at one gives S_1. Zero eigenvalues are omitted from the positive-term sum
and cause no positive-order difficulty. Hence E_α, the maximum state deficit,
is nondecreasing in α.

The function A_α in U3 is continuous on any compact positive interval, including
the branch points. If a≤α,β≤b and |α−β|≤δ, then

    |Φ_α(γ)−Φ_β(γ)|/Φ_α(γ)
       ≤ ω_A(δ)/(2a)+δ/a,                                (U4)

uniformly γ≥1; use Φ_α≥aB/2 and B≥4. Here ω_A is the compact continuity
modulus of A. Take a finite mesh in I. The inherited uniform-in-n limit applies
at every mesh point simultaneously once m exceeds their finite common threshold.
Monotonicity sandwiches E_α between its neighboring mesh values, while U4 makes
both neighboring Φ values relatively close to Φ_α. Let δ decrease to zero.
This proves

    sup_(n≥m, α∈I) | D E_α/Φ_α(γ)−1 | →0.               (U5)

No bound uniform in α was assumed in the old fixed-order proofs. The compact
uniformity is a finite-grid consequence of those proven limits and monotonicity.

On compact I, U0 is itself relatively equivalent to Φ_α/D uniformly in n.
For α bounded below in the first branch, m^(−α)→0 uniformly; Φ_α≥1 makes
its subtraction harmless. The middle branch is exactly Φ_α/D. In the last
branch u_D^α−3^α→0 uniformly and its log argument increment is O_I(1/m²),
since B/D=O(1/m²). The logarithm can therefore be linearized uniformly.
At α=1/2 and 2 these comparisons hold on both sides. Thus U5 supplies every
finite positive-order subsequence needed below.

## 3. The moving-order endpoints

When α→0, the new [zero-order theorem](SMALL_ORDER_BOUNDARY.md) gives

    D E_α ~ W=max{1,1−m^(−α)+(α/2)γ},                    (U6)

uniformly in n≥m. The first branch of U0 differs only by replacing γ with
max{4,γ}. If γ≥4 there is no difference. If γ<4 their difference is at most
2α, which tends to zero; W≥1. Consequently P_α~W/D uniformly in this
endpoint regime. The α log m effect is retained instead of using U3 outside
its fixed-order scope.

When α→∞ and α=o(m), the new [high-order theorem G1](PAPER.md) gives

    E_α ~ log[1+u_D^α/D+α(α−1)/(2m²)]/(α−1),             (U7)

uniformly n≥m. Compare its positive increment numerator
`T=u_D^α+α(α−1)γ/2` with the U0 numerator
`T'=u_D^α−1−2α+α(α−1)B/2`. Their difference is at most
`1+2α+2α²` in absolute value, since 0≤B−γ≤4. Dividing by T≥u_D^α proves
T'/T→1 uniformly. The positive-log comparison in the high-order proof
transfers this relative equivalent even when its argument is large. Therefore
P_α is relatively equivalent to U7 over this entire endpoint regime.

When the aspect is bounded, the new high-order theorem G2 works for every
α→∞, with no α=o(m) requirement. It gives

    E_α ~ log(1+u_D^α/D)/(α−1).                            (U8)

Here B is bounded, so the entire polynomial correction in U0 is negligible
relative to u_D^α, uniformly in α→∞. The same log comparison proves P_α~U8.
Retaining the exact u_D matters for arbitrary α/D; expanding its αth power
without a growth condition would not justify U1.

## 4. Exhaust all order/dimension sequences

If U1 fails, choose m_j→∞, m_j≤n_j≤Γm_j and α_j>0 with relative error
bounded below by ε>0. Every positive sequence of orders has a subsequence
that tends to zero, tends to a positive finite value, or tends to infinity.
For the first use U6; for the second use U5 and the compact comparison;
for the third use U8. Each contradicts that error bound. This proves the
supremum statement U1, including arbitrarily oscillating orders.

If U2 fails, make the analogous selection with n_j≥m_j and 0<α_j≤U_(m_j).
The zero and positive finite subsequences are handled by U6/U5 uniformly in n.
On the infinity subsequence, α_j/m_j≤U_(m_j)/m_j→0, so U7 applies. This proves
U2. No fixed-m theorem or fixed-aspect threshold has been misused as a
uniform all-dimension estimate.

## 5. Verification and interpretation

The substantive new endpoint work is in the two linked proofs, including
actual constructions, quantitative normalization, positive logarithm estimates
and near-minimizer conditions. U5 and the sequence assembly are consequences,
not additional independent breakthroughs. This file supplies a single complete
statement so a reader need not infer unproved uniformity from a catalogue of
fixed-order formulas.

The accompanying [proof/formalization map](THEOREM_MAP.md) discloses the exact
new scope. U1/U2 and their real-power/limit analysis have no complete Lean
formalization. Earlier fixed audit logs are unchanged and do not certify this
new manuscript. Exact finite diagnostics supplement the physical algebra;
they do not replace U5 or the all-sequence proof above. Internal assistant
review is distinct from external human peer review or historical priority.

Unrestricted-aspect α comparable to m or larger, fixed-m moving-order minima,
exact finite minima and full formalization remain open in this work. No
absolute-separability or nonlinear model conclusion is inferred. No new
Release, DOI or submission is asserted here.
