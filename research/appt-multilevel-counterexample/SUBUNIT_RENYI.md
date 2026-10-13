# Subunit Rényi entropy of APPT states: a second spectral transition

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536.
mxymmxym1@gmail.com. Research proof, 13 October 2026.
No external funding. OpenAI AI assistants assisted the research and verification.
Original material: copyright 2026 Yongxian Zhang, all rights reserved.

This note extends the repository's unrestricted joint-growth entropy theorem
to every **fixed** order 0<α<1. The argument below is a mathematical proof using
the explicitly identified companion results. Its main new nonlinear half-order
head bound and the finite downward-spike physical construction have Lean proofs.
The full arbitrary-order asymptotic theorem is **not yet completely formalized**.
No external refereeing or claim of historical priority is made.

## 1. Actual objects and theorem

Let 2≤m≤n, D=mn. An APPT state is a positive semidefinite, trace-one complex
matrix on C^m⊗C^n whose partial transpose is positive semidefinite after **every**
global unitary conjugation. Put

    S_α(ρ) = log(Tr ρ^α)/(1-α),
    E_α(m,n) = log D - min_{ρ APPT} S_α(ρ),       0<α<1.

Powers at zero are defined by 0^α=0. All logarithms are natural. The minimum
exists by finite-dimensional compactness and continuity; APPT compactness was
established in the companion physical package.

**Theorem.** For each fixed α in (0,1), set

    Φ_α(γ) = max{2α,1} + (α/2) max{4,γ}.

Then the following unrestricted, uniform joint-growth equivalent holds:

    sup_{n≥m} | D E_α(m,n)/Φ_α(n/m) - 1 | → 0       as m→∞.    (R1)

In particular, if n/m→γ<∞ then

    D E_α(m,n) → max{2α,1} + (α/2) max{4,γ}.                  (R2)

In square systems this is max{4α,1+2α}. There is a transition at **α=1/2**.
For α<1/2, a vanishing normalized eigenvalue improves the flat-spectrum
coefficient; for α≥1/2, flat families already attain the optimal coefficient.
At the transition both mechanisms attain the same leading value. No complete
classification of all transition-point near-minimizers is asserted.

The parameter α is fixed before the dimension limit. Neither uniformity in α
near zero nor the order-zero entropy follows by interchanging these limits.
Exact finite entropy minima and absolute separability are not determined here.

## 2. Precisely identified companion inputs

The following ordinary mathematical results are used, with their original
definitions and ranges; none is assumed to be a Lean theorem merely because it
appears in a research note.

1. `ENTROPY_ASYMPTOTIC.md`, Sections 2 and 4: the shifted physical star (E8),
   the tail-sensitive variance bound (E16), pivot normalization (E18), total
   square estimate (E19), and head/tail split (E20).
2. `MULTISCALE.md`, Section 2: uniform high-rank lacunary sparse-graph bound,
   for a fixed finite hierarchy. Its canonical fractional-matrix version is
   now also proved in Lean by `APPTReview.lacunary_sparse_matrix_bound`.
3. `FLAT_EXTREMIZERS.md`, Theorem F: flat actual APPT families with excess
   purity asymptotic to K(γ)=max{8,4+γ}, uniformly in n≥m. The companion
   `TWO_ENDED_GRAPH_LIMIT.md` provides the all-unitary construction proof.

The specialized new head estimate, order comparisons and negative-outlier lower
construction are proved below. The previously established entropy theorem at
α=1 is needed only for its **finite nonlinear head bound**, not to presume the
subunit conclusion. Standard Schmidt decomposition and finite-dimensional
spectral theory are used in the physical arguments.

## 3. The normalized kernels and exact centering

For x≥−1 define

    f_α(x) = [(1+x)^α - 1 - αx]/[α(α−1)].

It is nonnegative, has value and derivative zero at x=0, and on x>−1 satisfies
f_α''(x)=(1+x)^(α−2). Let b be the companion positive lower-tail spectral pivot,
z_i=λ_i/b−1 and t=1/(Db). For normalized deviations x_i=Dλ_i−1, exact algebra gives

    Σ_i f_α(x_i) = t^(−α)[Σ_i f_α(z_i) − D f_α(t−1)].          (R3)

Indeed Σ_i z_i=D(t−1), whereas Σ_i x_i=0; expand both power sums to verify (R3).
The exact Rényi identity is

    D[log D−S_α(ρ)]
      = D/(α−1) log[1+α(α−1) Σ_i f_α(x_i)/D].                (R4)

These identities include the centering correction, which cannot be dropped
at this scale. Their arguments are positive because Tr ρ^α>0.

For each fixed α and |x|≤ε<1/2, the integral Taylor identity gives

    f_α(x) = x²/2 + O_α(ε x²),                               (R5)

uniformly in that interval. This follows by bounding
|(1+u)^(α−2)−1|≤C_α ε for |u|≤ε and integrating twice.

## 4. The sharp half-order head bound

At α=1/2,

    f_(1/2)(x) = 2(√(1+x)−1)².

Suppose a_1≥...≥a_h≥0 and 1≥β_1≥...≥β_(h+1)≥0 satisfy the **actual shifted
star** budget

    Σ_(i=1)^h (a_i+β_(i+1))² ≤ 4(1−β_1).                    (R6)

Then

    H_(1/2) = Σ_i[f_(1/2)(a_i)+a_iβ_i]
                    +Σ_(i=1)^(h+1) f_(1/2)(−β_i) ≤ 2.       (R7)

Here is a full scalar reduction and exact certificate, including β_1=1.
Write y=β_1, r=√(1−y) and c=2/(1+r)². For 0≤z≤y,

    f_(1/2)(−z) = 2z²/(1+√(1−z))² ≤ c z²,       c≥1/2.

Write g(a)=a²/2−f_(1/2)(a). If u=√(1+a)−1, then a=u(u+2) and

    g(a)=u³(u+4)/2,
    g(a)(4+3a)−a³ = u⁴(u²+6u+4)/2 ≥ 0.                     (R8)

Thus g(a)≥a³/(4+3a)≥0. Expanding the shifted squares, summing, telescoping
Σ a_i(β_i−β_(i+1))≤a_1 y, and retaining g(a_1) yields

    H_(1/2) ≤ c[4(1−y)+y²]+a_1y−g(a_1)
             = 2(1+r²)²/(1+r)²+a_1(1−r²)−g(a_1).           (R9)

(R6) implies 0≤a_1≤2r. The following scalar inequality completes the proof:

    2(1+r²)²/(1+r)²+a(1−r²)−a³/(4+3a) ≤ 2,
                       0≤r≤1, 0≤a≤2r.                     (R10)

For r=0, a=0 and it is equality. For r>0 set v=a/(2r)∈[0,1]. Multiplying
the difference between the right and left sides by (1+r)²(4+3a) gives r Q(r,v),
where the exact polynomial is

    Q = 12r⁵v²+8r⁴v³+24r⁴v²−4r⁴v+16r³v³+16r³v−8r³
          +8r²v³−24r²v²−12r²v−12rv²+8rv−8r−8v+16.

Its nonnegativity on the entire unit square has the following rational
Bernstein certificate. On each box, use its affine coordinates X,Y∈[0,1]
and express the indicated polynomial in the product Bernstein basis
binom(N,i)X^i(1−X)^(N−i) binom(M,j)Y^j(1−Y)^(M−j).
Every coefficient is nonnegative.

| r interval | v interval | Polynomial | (N,M) |
|---|---|---|---|
| [0,3/4] | [0,1/2] | Q | (5,3) |
| [0,3/8] | [1/2,1] | Q | (5,3) |
| [3/8,3/4] | [1/2,3/4] | Q | (5,3) |
| [3/8,9/16] | [3/4,1] | Q | (7,5) |
| [9/16,3/4] | [3/4,1] | Q | (5,3) |
| [3/4,1] | [1/4,1] | Q | (5,3) |
| [3/4,1] | [0,1/4] | R | (4,3) |

In the last box use Q=32v³+(1−r)R. The complete coefficients are supplied in
`../../formalizations/appt-subunit-renyi/half_certificate.json`. Given power
coefficients d_kl in a box's affine coordinates, its Bernstein coefficients
are exactly

    b_ij = Σ_(k≤i,l≤j) d_kl binom(i,k)/binom(N,k)
                              binom(j,l)/binom(M,l).

Thus this is a finite rational **identity proving an inequality over a
continuum**. No sampled parameters support (R10). The Lean file
`APPTSubunit/HalfHeadPolynomial.lean` checks every identity with `ring` and
its coefficients with ordered-field positivity; `halfEntropyHead_le_two`
proves (R7). `density_appt_paper_halfEntropyHead` connects it to the actual
ordered APPT spectrum and exactly the paper pivot.

The head bound is sharp: a_i=0, β_1=1, β_i=0 for i≥2 gives H_(1/2)=2.
Unlike the von Neumann head, the half-order head can saturate with a negative
outlier; this is the source of the new transition.

## 5. Kernel comparisons for every subunit order

For 1/2≤α<1, weighted AM–GM gives for w>0

    w^(α−2) ≤ (2α−1)w^(−1)+(2−2α)w^(−3/2).

Integrate twice from zero, using f(0)=f'(0)=0, to obtain for x≥−1

    f_α(x) ≤ (2α−1)f_1(x)+(2−2α)f_(1/2)(x),               (R11)

where f_1(x)=(1+x)log(1+x)−x with its continuous endpoint value. Both
head bounds, including their common cross term a_iβ_i, are at most two.
Hence H_α≤2 in this range.

For 0<α≤1/2 and x≥0, second derivatives give f_α(x)≤f_(1/2)(x).
For x=−y, 0≤y≤1, put z=√(1−y). Convexity of z^(2α−1) on z>0 gives

    z^(2α−1) ≥ 1+(1−2α)(1−z).

Multiply by z and rearrange, extending to z=0 by continuity. The result is

    f_α(−y) ≤ f_(1/2)(−y)/(2α).                            (R12)

Since also a_iβ_i≥0 and 1/(2α)≥1, (R7) implies H_α≤1/α. Combining,

    H_α ≤ C_α := max{2,1/α}.                               (R13)

No external entropy theorem in the unresolved order interval is used.

## 6. The unrestricted upper half

Use the companion quantities h=m−1,

    Btail=max{4,D/h²},    C=4+Btail,
    ν_m=1/m+2/(m−1),      δ_m=2/√h.

The actual APPT star, ordering and triangular graph bounds give
V/b²≤Σ_(i≤h)(a_i+β_i−g_R)²+Btail, |t−1|≤ν_m and Σ z_i²≤6C.
All nonexceptional |z_i|≤δ_m. Apply (R5) only to those coordinates and t−1;
use (R3), retaining the centering correction. As in the companion (E23)–(E24),

    Σ f_α(x_i)
      ≤ t^(−α)[ V/(2b²)+Σ_head(f_α(z_i)−z_i²/2)+o_α(C)]
      ≤ C_α+Btail/2+o_α(C),                                (R14)

uniformly in n≥m. In the second line, enlarge the first h residual squares
to (a_i+β_i)², expand them, and drop the extra nonpositive bottom square.
The remaining head is precisely H_α, bounded in (R13).

Since C/D=O(m^(−2)), the logarithm in (R4) is uniformly linear at this
relative scale. Also max{4,D/(m−1)²}=max{4,n/m}[1+O(1/m)]. Multiplying
(R14) by α gives

    D E_α(m,n) ≤ Φ_α(n/m)[1+o_α(1)],                       (R15)

with one error for all n≥m. The actual spectral objects and all APPT
quantifiers have been retained; (R6) was derived physically, not supplied
as an assumed spectral ansatz.

## 7. Flat lower families when α≥1/2

The companion flat families have all |Dλ_i−1|→0 and
Σ(Dλ_i−1)²=K(n/m)[1+o(1)], uniformly in n≥m. Equations (R4)–(R5) give

    D[log D−S_α(ρ_flat)] = (α/2)K(n/m)[1+o_α(1)].           (R16)

For α≥1/2 this equals Φ_α, so it matches (R15), including α=1/2.

## 8. A finite physical downward-spike family

Fix h>0 and m≥h. Let P be any positive contraction, v any unit vector, and set

    b=(h+1)m,    d=b−h²≥0,
    B=bI+2hP−d|v><v|.                                     (R17)

This is APPT **for every finite admissible m**, independently of n. To prove it,
take an arbitrary (possibly unnormalized) test vector and its nonnegative
Schmidt coefficients s_i. Put N=Σ_(i<j)s_i s_j. The contraction expectation
against its partial-transposed pure projector W is at least −N. The largest
eigenvalue of W is max_i s_i². For each i, put T=Σ_(j≠i)s_j and Q=Σ_(j≠i)s_j².
The exact finite SOS is

    b Σ_j s_j²−2hN−d s_i²
      = (h s_i−T)²+(h+1)[(m−1)Q−T²]+(2h+1)Q ≥0.          (R18)

The last inequality is Cauchy on the other m−1 coordinates. Thus the
quadratic form of every unitary-conjugated B after partial transpose is
nonnegative. Its ordinary positivity follows from

    B=h²I+d(I−|v><v|)+2hP ≥0.

All-unitary sufficiency, including arbitrary complex test vectors and no
supplied Schmidt data, is proved by Lean `negativeSpike_absolutelyPPT`.

For an integer projection rank k<D choose v outside its range. The normalized
state ρ=B/Z has actual eigenvalues

    (b+2h)/Z   [k entries],     b/Z [D−k−1 entries],     h²/Z [one],
    Z=(D−1)b+2hk+h².

Lean proves density, all-unitary APPT and the exact objective

    Tr ρ² = [(D−1)b²+4h(b+h)k+h⁴]/Z².                     (R19)

The witness is constructed for every k<D; no hypothetical projector rank or
unitary interface occurs in the final existence theorem.

## 9. The broad negative-outlier lower branch

Take k=floor(D/2), fixed h≥1, and z=h/(h+1). The exceptional normalized
eigenvalue D h²/Z tends to zero, uniformly in n≥m. All other normalized
deviations tend uniformly to zero, and direct use of the displayed spectrum
gives

    Σ_bulk (Dλ_i−1)² = (n/m) z²[1+O_h(1/m)] + O_h(1/m).    (R20)

For clarity, divide B and Z by b: its three unnormalized levels are
1+u, 1, ℓ, where u=2z/m and ℓ=h²/b. Their mean is
t_0=1+u(k/D)−(1−ℓ)/D. Subtract this mean in the two bulk blocks;
their variance is D u²(k/D)(1−k/D)+O_h(1/m)+O_h(1/D).
Dividing by t_0²=1+O_h(1/m) proves (R20). The hole is excluded from
this bulk sum.

The hole contributes α f_α(−1)=1. Using (R4)–(R5) on the bulk yields,
uniformly in n≥m,

    D[log D−S_α(ρ)]
       = 1+(α/2)(n/m)z² + o_(α,h)(1+n/m).                 (R21)

The error in its first term also includes O_(α,h)(m^(−α)), from ℓ^α;
it tends to zero for each fixed positive α. The logarithm error divided by
1+n/m is O_(α,h)(m^(−2)). First take m→∞ with h fixed, then h→∞.
This gives the lower branch 1+αγ/2, and its uniform relative version.
It matches Φ_α for α<1/2 when γ≥4.

For α<1/2 this also rigorously excludes extending the earlier flat-only
coefficient 2α+αγ/2 to the wide sector: the excess is 1−2α>0.

## 10. The high-hierarchy negative-outlier lower branch

For the remaining γ≤4, fix a finite high-rank lacunary hierarchy from
`MULTISCALE.md`. Choose its energies so the total tends arbitrarily close
to four while its uniform graph norm is strictly below two. More explicitly,
fix an integer H≥1, η∈(0,1), J=2H², δ_j=3^(−j), r_j~m^(2−δ_j), and coefficients with

    r_j c_j² → e=2(1−η)²/(H+1)².

Then E=Je=4H²(1−η)²/(H+1)² and the proved sparse-graph cap is
√E+√(2e)=2(1−η). Let nested coordinate projections P_j have ranks r_j,
and choose a unit coordinate vector v outside the largest support. Put

    X=Σ_j c_j P_j,     B=I+X−a|v><v|,     a=1−η.

The all-unitary test must be checked anew for a negative spike. Given a
unit Schmidt vector s, let i maximize s_i², p=s_i², q=1−p. The rank-r_j
negative projection bound gives selected graphs G_j on these Schmidt
coordinates, as in `MULTISCALE.md`. Remove vertex i in each selected graph.
The proved uniform cap bounds the remaining quadratic form by
[2(1−η)+o(1)]q, even after zero-padding to m coordinates. Incident edges
are bounded, without their edge budgets, by

    2 Σ_j c_j s_i Σ_(k≠i)s_k
       ≤ 2√m (Σ_j c_j)√(pq) = o(1).

Here √m Σ c_j→0 since every fixed rank exponent exceeds one. The negative
pure term is at least −a p because λ_max(W)=max s_i². Consequently

    <ψ,(UBU*)^Γ ψ> ≥ 1−a p−(1−η+o(1))q−o(1)
                   ≥ η−o(1)>0,

uniformly over all U, ψ and n≥m. This proves eventual APPT with a strict
finite margin; a limiting zero margin is never used to infer positivity.
Ordinary positivity is immediate from B≥ηI.

Since the projections are nested and r_i/r_j→0 for i<j,
Tr X²→E; its coefficient sum tends to zero and Tr X=o(m). After trace
normalization all bulk deviations tend uniformly to zero and their square
sum tends to E, uniformly in n≥m. The lone hole has Dλ→1−a=η. Therefore

    D[log D−S_α(B/Tr B)] → α f_α(−a)+α E/2.                (R22)

Fix H,η **before** the dimension limit. Then let H→∞ and η↓0; the right
side approaches 1+2α. This supplies the low-aspect lower branch. There
is no use of a growing hierarchy inside the fixed-hierarchy graph theorem.

## 11. Uniform conclusion and remaining formalization

For a given tolerance choose H,η in the high construction and h in the broad
construction first. Use the high construction for n/m≤4 and the broad one
for n/m>4. Their dimension thresholds and errors are independent of n.
For α<1/2 they give Φ_α[1−o_α(1)] uniformly; (R15) supplies the matching
upper half. Section 7 does the same for α≥1/2. This proves (R1)–(R2).

This is a sharp **first nonzero asymptotic**, not an exact finite-dimensional
entropy minimum or a full equality classification. The Lean companion covers
the half-order nonlinear head bound on the actual spectrum, the exact
polynomial certificate, and the finite broad downward-spike family. Kernel
comparisons at arbitrary α, the entire asymptotic entropy objective/centering
and the negative high-hierarchy physical construction remain to be formalized.
Existing companion flat-family and entropy upper asymptotic inputs are ordinary
mathematical proofs; their unformalized portions are explicitly retained here.

## 12. Literature screening

The closest primary papers inspected on 13 October 2026 were
[Ahiable–Kothakonda–Winter, arXiv:2608.03390v2](https://arxiv.org/html/2608.03390v2),
[Tran, arXiv:2609.18568v1](https://arxiv.org/html/2609.18568v1), and
[Patra–Hiesmayr, arXiv:2610.12000](https://arxiv.org/abs/2610.12000).
The first two discuss physical purity/von Neumann entropy and spectral
polytopes; the third concerns separability in two fixed Bell-diagonal families.
None of those inspected statements supplies the unrestricted subunit joint-growth
law proved here. Their results are not being reproved or called incorrect.
This targeted search is not an exhaustive priority certification. Hildebrand's
spectral framework [quant-ph/0502170](https://arxiv.org/abs/quant-ph/0502170)
is credited as background; the finite physical Lean construction builds its
Schmidt and all-unitary bridges explicitly.
