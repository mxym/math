# Macroscopic high-order APPT entropy in every aspect-growth regime

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding; OpenAI AI assistants assisted. Original material all
rights reserved. Written proof, not new Lean verification or external review.

The first nonzero relative equivalents of [U1/U2](UNIFORM_PROFILE.md) have
explicit scope boundaries. At the weaker macroscopic, absolute-error scale,
the high-order phase law has no aspect restriction and no restriction on how
fast the order grows. The distinction of scales is part of the theorem.

## 1. Statement

For actual APPT densities let E_α=log D−min_APPT S_α, D=mn and
u_D=3D/(D+2). If L_m→∞, then

    sup_(n≥m, α≥L_m)
       |E_α(m,n)−max{0,log u_D−(log D)/α}|→0
    as m→∞.                                              (M1)

Thus for *any* α→∞, m→∞ and n≥m, if `(log D)/α→ν∈[0,∞]`,

    E_α(m,n)→max{0,log3−ν},                              (M2)

with value zero at ν=∞. The result includes arbitrary diverging aspect and
orders comparable to or faster than m and D. Where the limiting deficit
is zero it determines no first nonzero coefficient. In particular it does
not fill the unresolved relative window α≈m with unrestricted aspect.

## 2. Uniform proof

The actual spectral estimates in [the high-order proof](PAPER.md) give, for
all sufficiently large m and every n≥m,

    y_1≤u_D,  y_2≤v_m≤5/2,  u_D≥8/3,
    Q_E≤C_m≤C_0,  δ_m=O(1/m),
    Q_B≤ζ_m(γ+8),  ζ_m≤C_1,  γ=n/m.

Here E is the m²−2 exceptional set, B the actual middle spectrum, and δ_m
bounds its normalized deviations. These constants require only a common
large-m threshold; none depends on n or α.

Apply the real-power estimate G19 for every real α≥2. Since γ≥1 and
γ/D=1/m², it gives

    M*_α≤1+r+C_2 α² v_m^α/D
                   +C_3 (α²/m²)(1+δ_m)^α,
    r=u_D^α/D.

The exceptional term is at most `C_2 α²(15/16)^α r`. The supremum of its
coefficient over α≥2 is finite. Hence for an absolute K≥1,

    M*_α≤1+Kr+C_3 (α²/m²)(1+δ_m)^α.                      (M3)

The exact pure-spike APPT state has moment at least r. Jensen also gives
M*≥1, so

    E_α≥[α log u_D−log D]_+/(α−1).                       (M4)

For the upper bound use `1+x+y≤(1+x)(1+y)` and
`log(1+e^s)≤s_++log2` in M3. Dropping the favorable −2 log m term gives

    0≤E_α−[α log u_D−log D]_+/(α−1)
       ≤α log(1+δ_m)/(α−1)+(C+2 logα)/(α−1),              (M5)

for an absolute C. The factor α/(α−1) can be replaced by one in the leading
expression at error at most log3/(α−1). Thus the total absolute error from
M1 is at most

    O(1/m)+O[(1+logα)/(α−1)].                            (M6)

The supremum over α≥L_m tends to zero, proving M1 uniformly in n. No Taylor
condition α/m→0 was applied to the bulk: its full `(1+δ_m)^α` was kept until
after the logarithm divided by α−1. Taking limits gives M2.

This is a consequence of the same actual spectrum decomposition and is not
counted as another independent conjecture solution. No scalar surrogate,
sampled unitary or original conjecture is used as a proof assumption. The
paper's formalization map records the new absolute-error scope, and prior
Lean audits remain unchanged.
