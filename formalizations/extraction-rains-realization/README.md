# Reverse realization of actual Rains fidelity effects

For every K >= 2 and every actual `Extraction.RainsEffect K M`, this package
constructs the complex-linear channel

    Lambda_M(X) = Tr(M X) Phi_K
                + Tr((I-M) X) (I-Phi_K)/(K^2-1).

The definition `channel K M` does not assume CP, TP, Kraus data, or an overlap
certificate. `measurePrepare_completelyPositive` proves CP through its actual
Choi matrix E tensor F-transpose. The Rains PSD hypotheses prove CP of the two
terms; Bell trace/idempotence prove TP and exact overlap on every complex X.

The actual partial-transpose conjugate is proved equal to the positive
measure-and-prepare map with outputs Pi_+ = (I+Swap)/2 and
Pi_- = (I-Swap)/2 and input effects

    E_+ = ((I/K)+Gamma(M))/(K+1),
    E_- = ((I/K)-Gamma(M))/(K-1).

These equal (I+K Gamma(M))/(K(K+1)) and
(I-K Gamma(M))/(K(K-1)), respectively. Their positivity is exactly the Rains
order interval. Gamma transposes Alice, the first tensor factor. This is an
identity of actual maps on all complex matrices.

`protocol` derives both complete finite Kraus families from the proved
CP/Choi/Kraus theorem; no Kraus certificate is a premise.
`protocol_targetEffect` proves exact equality with M.
`rainsEffect_exists_actual_protocol` preserves any supplied preprocessing U
and returns the actual channel formula. `rainsEffect_iff_actual_protocol_effect`
proves equality of the two feasible effect sets for K >= 2. The global U is a
separate preprocessing operation as in the original protocol model.

K=1 is intentionally separate: every TP output then has fidelity exactly one;
the normalized failure output used here requires K >= 2.

Lean 4.34.1; Mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612.
Ordinary compilation only (BUILD_ONLY), pending independent audit. The shared
frozen dependency builds are recorded in DEPENDENCY_SHARING.json. All original
frozen publication/audit scopes remain unchanged.
