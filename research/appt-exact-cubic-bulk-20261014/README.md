# Exact APPT entropy bulk onset

For every FIXED finite alpha>0, let N_alpha(m) be the smallest integer N>=m
such that EVERY n>=N has actual all-global-unitary APPT entropy maximum
equal to the exact integer-rank q bulk, q=(m+1)/(m-1). Then

    N_alpha(m)=delta_crit(alpha)m^2+O_alpha(m).

Here delta_crit is the complete positive/negative gain-to-protection ratio
threshold in the preceding reviewed cubic correction paper. For large m,
ALL n>=delta_crit m^2+A_alpha m have EXACT bulk equality; ALL optimizing
matrices are normalized I+t Pi with an exactly winning integer rank,
t=2/(m-1), including every rank tie. At alpha2 this is the actual purity
onset N_2(m)=m^2/4+O(m).

[Complete proof](PAPER.md), [predeclared target map](THEOREM_MAP.md),
[source and literature scope](LITERATURE.md), [independent review](REVIEW.md).
The full initial proof and target map are reviewed separately from finite
controls and later status edits. This is ordinary written mathematics in
the existing APPT direction, with no complete Lean theorem or new audit root.

The proof retains the exact integer interval maximum and subtracts actual
entropies before expanding. Its error is proportional to anomaly mass,
including arbitrarily tiny heads and arbitrarily large D/m^3. A disjoint
physical witness controls every head and all omitted mass; an actual
finite-state lower within an O(m) band matches the complete upper.

The preceding zero limiting correction alone did not certify finite equality.
The present theorem gives exact equality above an eventual O(m) upper band;
it does not give every finite minimal threshold, its next coefficient, a
growing-order uniform theorem, or an ASEP bulk classification.
Finite checks use exact Fraction matrices and 320-digit entropy arithmetic.
They support the proof and are not full-domain or formal certificates.

Author Yongxian Zhang, South China University of Technology; no external
funding; OpenAI AI assistants assisted. Original material all rights reserved;
third-party notices retained. No new independent major-conjecture count,
submission, Release or DOI.
