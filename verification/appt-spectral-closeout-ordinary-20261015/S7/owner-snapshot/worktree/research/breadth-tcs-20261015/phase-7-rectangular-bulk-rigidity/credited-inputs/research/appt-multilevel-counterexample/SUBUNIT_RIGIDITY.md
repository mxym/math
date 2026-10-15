# Sharp subunit APPT entropy: necessary outliers and the half-order boundary

Research proof, 13 October 2026. Yongxian Zhang (张永贤), School of Computer
Science and Engineering, South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com.
No external funding. OpenAI AI assistants assisted the work.
New original material: copyright 2026 Yongxian Zhang, all rights reserved.

This proves a necessary-and-sufficient classification of the normalized
spectral outlier structure at fixed finite aspect ratio for 0<α≤1/2.
It uses the complete mathematical proof in [SUBUNIT_RENYI.md](SUBUNIT_RENYI.md)
and its actual physical head/tail estimates. It is a written theorem, not a
complete Lean formalization or external peer review. No historical priority
claim is made. It does not classify the distribution of the vanishing bulk
amplitudes or exact finite-dimensional maximizers.

## 1. Statements for the actual spectrum

Take any sequence of APPT density matrices ρ_j on C^(m_j)⊗C^(n_j), with
m_j→∞, n_j≥m_j and n_j/m_j→γ∈[1,∞). Let D_j=m_j n_j and write the actual
ordered eigenvalues λ_(j,1)≥...≥λ_(j,D_j). Put

    B=max{4,γ},    K=4+B,
    ℓ_j=D_j λ_(j,D_j) ∈ [0,1],
    Q_j=Σ_i(D_j λ_(j,i)−1)²
       =D_j²[Tr ρ_j²−1/D_j],
    δ_j=max_(i<D_j)|D_j λ_(j,i)−1|.

For **each fixed 0<α<1/2**, the following are equivalent:

    D_j[log D_j−S_α(ρ_j)] → 1+αB/2;                         (L1)

    ℓ_j→0,     δ_j→0,     Q_j→1+B.                          (L2)

Thus exactly one distinguished normalized eigenvalue tends to zero; every
other normalized eigenvalue tends uniformly to one. The optimal purity
coefficient of these entropy near-minimizers is 1+B rather than K=4+B.

For **α=1/2**, near-minimality is instead equivalent to

    δ_j→0,
    dist(ℓ_j,{0,1})→0,
    Q_j−(1+B+3ℓ_j)→0.                                      (L3)

In particular every subsequence with ℓ_j→0 has Q_j→1+B, whereas every
subsequence with ℓ_j→1 has Q_j→K. Alternation between the two mechanisms is
allowed; the full sequence is not required to choose one branch. There are
no asymptotically optimal intermediate fixed-height holes at this order.

All these near-minimizing sequences are eventually **full rank**. Their
normalized least eigenvalue can tend to zero, but an actual zero eigenvalue
is incompatible with optimality for any fixed positive α in this interval.

## 2. Strictness of the half-order head comparator

Use the paper pivot, its ordered nonnegative head a_1≥...≥a_h and bottom
head 1≥β_1≥...≥β_(h+1)≥0, with h=m−1. Put y=β_1 and r=√(1−y).
The finite proof in SUBUNIT_RENYI Sections 4–5 gives

    H_(1/2) ≤ C(a_1,y) ≤ 2,
    C(a,y)=2(1+r²)²/(1+r)²+a(1−r²)−g(a),
    g(a)=a²/2−2(√(1+a)−1)²,
    0≤a≤2r,     0≤r≤1.                                    (L4)

The rational comparator in that proof is strictly below two except at
(a,y)=(0,0) and (0,1). To see this without numerical optimization, recall
its exact polynomial certificate Q(r,v), v=a/(2r), for r>0. On the first
six rectangles all Bernstein coefficients are nonnegative and all four corner
coefficients are strictly positive. Hence Q>0 throughout each closed rectangle:
at any pair of affine coordinates at least one corner basis product is positive.
On the seventh rectangle the same holds for R, and

    Q=32v³+(1−r)R.

Consequently Q>0 whenever r<1, and Q(1,v)=32v³ vanishes only at v=0.
For r=0 the constraint gives a=0. The exact gap (R8) cannot create additional
equality points. These rational strictness checks are also reproducible with
`check_half_strictness.py`; they apply to the whole parameter rectangles.

Continuity and compactness of {(a,y):0≤y≤1,0≤a≤2√(1−y)} therefore imply

    H_(1/2)→2 ⇒ a_1→0 and dist(y,{0,1})→0.                 (L5)

This statement is uniform in the growing number of head coordinates; only
the two scalar parameters enter its coercive comparison.

## 3. Necessity at the half-order boundary

The unrestricted upper argument, retaining its remainder, gives at fixed γ

    Σ_i f_(1/2)(Dλ_i−1) ≤ H_(1/2)+B/2+o(1) ≤ 2+B/2+o(1).

Equation (R4) identifies half-order near-minimality with saturation of this
sum. Hence H_(1/2)→2. The pivot normalization t→1 gives
ℓ=(1−y)/t. By (L5), a_1→0 and dist(ℓ,{0,1})→0.

If y tends to zero, all β_i≤y tend to zero. If y tends to one, the actual
shifted-star budget gives

    Σ_i(a_i+β_(i+1))² ≤ 4(1−y) →0,

so in particular β_2→0. Thus along either type of subsequence all head
coordinates except the least eigenvalue tend uniformly to zero. The tail
bound 2/√(m−1) and t→1 prove δ→0 for the entire sequence.

The total physical variance Q is uniformly bounded at fixed γ. Taylor
expansion applies to every coordinate except the least; its sum error is
O(δ Q)=o(1). If ℓ→1, the least term also vanishes and
Σ f_(1/2)(Dλ_i−1)=Q/2+o(1), forcing Q→4+B. If ℓ→0, its exact kernel
value tends to two, and

    Σ f_(1/2)(Dλ_i−1) = 2 + [Q−(ℓ−1)²]/2+o(1),

forcing Q→1+B. Every subsequence has a further subsequence of one of these
two types. This proves all three full-sequence conditions in (L3), including
Q−(1+B+3ℓ)→0; replacing the two-point relation by a single fixed branch
would incorrectly exclude alternating optimal sequences.

## 4. Necessity for every fixed α below one half

The pointwise comparisons give the finite head inequality

    H_α ≤ H_(1/2)/(2α) ≤ 1/α.

Saturation of the full entropy upper bound forces H_α→1/α and therefore
H_(1/2)→2. Again (L5) leaves only the zero-hole and flat scalar endpoints.
The flat endpoint is impossible when α<1/2: if a_1→0 and y→0, every head
deviation is uniformly small. Its squared mass is bounded, since

    Σ_i a_i² ≤4(1−y),
    Σ_(i≥2) β_i² ≤4(1−y),     β_1²≤1.

The local Taylor estimates then give H_α−H_(1/2)→0. This would force
H_α→2, contradicting 1/α>2. Hence y→1, so ℓ→0. The shifted-star budget
and the tail bound give δ→0 as before.

The least coordinate contributes f_α(−1)=1/α by continuity at the endpoint.
Taylor expansion on all the other coordinates and bounded Q now gives

    Σ_i f_α(Dλ_i−1) = 1/α+[Q−(ℓ−1)²]/2+o(1).

Its optimal limit is 1/α+B/2, so Q→1+B. This proves (L2).

## 5. Sufficiency and the finite-rank boundary

Given (L2), the same exact kernel identity and uniform Taylor expansion on
all but the least coordinate prove (L1). Given (L3), every subsequence has
a further subsequence with ℓ→0 or ℓ→1; in either case the half-order kernel
sum tends to 2+B/2. Boundedness and this subsequence criterion give the full
optimal entropy limit. These arguments use only actual spectra of the stated
APPT density matrices; they do not presume a model for their eigenvectors.

The two types genuinely occur: the flat companion constructions realize
ℓ→1, Q→4+B, and the negative-hole high/broad constructions realize
ℓ→0, Q→1+B. Their finite parameters are fixed before the dimension limit,
then chosen diagonally after their established positive-margin thresholds.
This is the same valid order of limits as the sharp lower theorem.

Finally, for an actual singular state in the eventually relevant range m≥3,
the least eigenvalue is zero and hence y=1. The physical shifted star (E8)
forces every a_i and β_(i+1) to vanish; in particular λ_1=λ_(D−1)=b.
Ordering therefore makes all first D−1 eigenvalues equal to b, and trace one
gives b=1/(D−1). Its entropy is log(D−1) for every positive Rényi order,
so D[log D−S_α]→1. The sharp
value 1+αB/2 is strictly above one, and the half-order value is at least two.
An asymptotically optimal sequence cannot have infinitely many singular
terms. This proves eventual full rank without confusing a vanishing least
normalized eigenvalue with a finite zero.

## 6. Verification boundary

The half-order continuum inequality and its actual shifted-star/pivot bridge
have the source-bound Lean audit in `formalizations/appt-subunit-renyi`.
The strict corner checks and the spectral-limit necessity/sufficiency here
are mathematical arguments. The complete rigidity theorem is not included
in that Lean audit, and no old kernel log is relabeled as certifying it.
These are classifications at fixed finite γ and fixed α≤1/2, not uniform
statements for α depending on dimension or for γ diverging.
