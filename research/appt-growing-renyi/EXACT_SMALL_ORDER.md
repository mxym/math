# An exact finite APPT entropy phase at sufficiently small positive order

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding; OpenAI AI assistants assisted. Original material all
rights reserved. This is a complete ordinary proof of the stated finite band,
not a complete Lean formalization or external peer-review claim.

## 1. Exact theorem on the original density set

**Theorem E1.** For every 2≤m≤n, D=mn≥4, and every real order

    0<α≤1/(512D),

the actual all-global-unitary APPT entropy minimum is

    min_APPT S_α(ρ)=log(D−1).                             (E1)

Every equality state, and only such a state, is

    ρ=(I−vv*)/(D−1),       v any unit vector in C^m⊗C^n.   (E2)

Thus the uniform rank-(D−1) spectrum is the exact finite optimizer throughout
an explicit nonzero positive-order band. The constant 512 is a sufficient
bound from the proof, not asserted optimal; the maximal singular-optimizer
order or the general finite-order minimum is not determined.

This finite band covers all dimension pairs, including fixed smaller dimensions.
It is separate from the m→∞ asymptotic theorem. The α=0 endpoint and its
singular spectrum are existing inputs, while the positive-band conclusion
and its strict full-rank exclusion are proved below. No separate major-problem
count or historical-first assertion is attached to this band.

## 2. Two necessary physical inequalities

Let λ_1≥...≥λ_D≥0 be an actual APPT spectrum. A rank-two Schmidt witness with
variable nonnegative coefficients places λ_D and λ_(D−2) on its two diagonal
vectors, λ_1 on the negative pair and λ_(D−1) on the positive pair. These
four slots are distinct. All-unitary positivity of its quadratic implies

    [λ_1−λ_(D−1)]²≤4λ_D λ_(D−2).                         (E3)

For equal Schmidt coefficients, the same rank-two witness gives

    λ_1≤λ_D+λ_(D−1)+λ_(D−2)
        ≤3(1−λ_1)/(D−1),
    λ_1≤3/(D+2).                                         (E4)

The average of the three smallest tail eigenvalues is at most the average
of the whole tail. These are necessary inequalities derived from actual
unitary tests, not a presumed equivalence with a relaxation.

If λ_D=0, E3 forces λ_1=λ_(D−1). The first D−1 entries are consequently equal
and positive by trace one, each 1/(D−1). A second zero would instead force
all eigenvalues zero. Thus E2 is the only singular spectrum.

Every state E2 is actually APPT: the largest eigenvalue of a partially
transposed unit pure projector is at most one, so
`I−(Uvv*U*)^Γ≥0` for every global U. Its density entropy is log(D−1) for
every positive order. It remains to prove a strict inequality for every
full-rank actual state in the band.

## 3. Full-rank states close to the singular boundary

Put N=D−1, u=λ_D>0, μ=(1−u)/N and T=N^(1−α). The first N entries have mean
μ. One has u≤1/D and μ≥u. Suppose first that u≤μ/16. Set
t=λ_1 and v=λ_N. Inequality E3 gives

    t−v≤2√(ut).

Because v≤μ, solving `t≤μ+2√(ut)` gives

    t≤[√u+√(u+μ)]²≤2μ.                                  (E5)

The last bound follows from u/μ≤1/16: its exact coefficient is
`(18+2√17)/16<2`. Also `s−2√(us)` is increasing for s≥u. Since t≥μ≥u,

    v≥t−2√(ut)≥μ−2√(uμ)≥μ/2.                            (E6)

The tail's squared deviations satisfy

    Σ_(i≤N)(λ_i−μ)²≤N(t−v)²/4≤Nut≤2Nuμ.                 (E7)

For completeness, bounded variables in [v,t] with mean μ obey variance
at most `(t−μ)(μ−v)≤(t−v)²/4`: average
`(t−λ_i)(λ_i−v)≥0` and subtract μ².

The magnitude of the second derivative of x^α on [μ/2,2μ] is at most
`4α(1−α)μ^(α−2)`. Taylor at μ, followed by cancellation of the linear
deviations and E7, therefore gives

    Σ_(i≤N) λ_i^α≥Nμ^α−4α(1−α)Nu μ^(α−1).               (E8)

Since `Nμ^α=T(1−u)^α`, integrate the derivative of `(1−u)^α` to obtain

    T−Nμ^α≤αuT/(1−u),
    μ^(α−1)=T(1−u)^(α−1)≤T/(1−u).

Thus E8 implies

    Σ_(i≤N) λ_i^α≥T−[αuT/(1−u)](1+4N)
                    ≥T−5αD uT,                          (E9)

where 1−u≥N/D and N≥3 give `(1+4N)/(1−u)≤D(4+1/N)<5D`.
The extra least power satisfies

    u^α/(uT)=(Nu)^(α−1)≥1,

because Nu<1 and α<1. Adding it to E9 proves

    Σ_(i≤D) λ_i^α≥T+uT(1−5αD)>T,                        (E10)

under α≤1/(512D). This strict inequality covers every positive u arbitrarily
close to zero; compactness away from the boundary is not assumed to handle it.

## 4. Full-rank states away from that boundary

Now u>μ/16. It follows that `u>1/(16N+1)`, so all normalized eigenvalues
y_i=Dλ_i satisfy

    1/16<y_i<3,      (1/D)Σ_i y_i=1,                     (E11)

using E4 for the upper bound. Taylor around one and the second-derivative
bound on [1/16,3] give

    y^α≥1+α(y−1)−128α(1−α)(y−1)².                       (E12)

Indeed `|d²y^α/dy²|≤256α(1−α)` there. Since y_i²≤3y_i,
the normalized variance is at most two. Average E12 to get

    M_α:=(1/D)Σ_i y_i^α≥1−256α(1−α)
                            ≥1−(1−α)/(2D).             (E13)

On the other hand concavity of x^(1−α) at one yields

    (N/D)^(1−α)≤1−(1−α)/D
                  <1−(1−α)/(2D).                        (E14)

Multiplying E13–E14 by D^(1−α) proves `Σλ_i^α>N^(1−α)` in this case as
well. Taking log and dividing by 1−α gives S_α>log N for every full-rank
actual state. Combined with the complete singular classification and actual
attainment, this proves both E1 and E2.

## 5. Interpretation and proof scope

The proof uses only two physical rank-two inequalities, elementary variance,
real-power Taylor bounds and an actual APPT singular witness. Proving an
upper-bound statement on a necessary spectral set does not replace the
original model here: necessity was proved physically and exact attainment
and every equality state were proved on actual densities.

This is a finite theorem on an explicitly restricted order band. It does not
give the sharp end of that band, general finite minima, fixed-m growing-order
minima or unrestricted-aspect large-order first coefficients. It is part of
the same APPT entropy research direction. The cited contemporary entropy
papers and the elementary α=0 endpoint remain credited; no claim of first
historical discovery follows from a bounded literature search.

The new finite real-power optimization is not contained in earlier APPT
kernel logs. The proof/formalization map marks it as unformalized. No Lean
module, axiom or audit root, new Release, DOI or submission is introduced.
