# Defensive proof-scope audit: fourth-round NIST KEMs

**Scope and date.** This note audits public claims and already-published outcomes. It does not construct, reproduce, or operationalize an attack. Snapshot: 27 November 2026.

## Exact result: a documented Level-1 BIKE proof obligation failed

Let λ=128. In the Level-1 configuration using the earlier Black–Grey–Flip decoder, as analyzed in the work cited as [42] by NIST IR 8545, NIST states the following δ-correctness criterion for the claimed λ-bit security of the transform:

    δ ≤ 2^(−λ)=2^(−128).

NIST states this precondition explicitly in its BIKE security discussion: [NIST IR 8545, pp. 12–13](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf). The same official report gives the published lower bound

    DFR_avg ≥ 2^(−117)

for that Level-1 configuration and says it defeats the evaluated version’s IND-CCA2 security: [NIST IR 8545, p. 13](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf).

**Proof of the contradiction.** Since −117>−128,

    DFR_avg / 2^(−128) ≥ 2^11.

Thus the publicly established lower bound on failure probability is at least 2,048 times the maximum allowed by the reduction's stated δ-correctness premise. Therefore that premise is false for the evaluated Level-1 version. The FO-based theorem cannot establish its claimed 128-bit IND-CCA2 guarantee. In addition, the NIST report already records the adverse conclusion, so this is an attributed public insecurity result rather than merely an absent proof.

This exact conclusion does **not** automatically transfer to later BIKE specifications. NIST reports that the BIKE team responded with a different decoder and that later work suggested an approximately 9% block-size increase; NIST nevertheless found the DFR analysis less mature and did not select BIKE: [NIST IR 8545, pp. 13–14](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf). A changed decoder or parameter set is a different theorem instance and needs a new δ-correctness proof.

## Negative control: HQC had a proof-scope gap, but later specifications address it

NIST selected HQC because its DFR analysis was more mature than BIKE's, while explicitly describing the 2025 HQC DFR bound as heuristic and dependent on a simplifying coordinate-independence assumption. NIST also states that sufficiently low DFR is needed for the IND-CCA2 proof: [NIST IR 8545, pp. 10–11](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf).

That observation alone never proved HQC unsafe. A 2026 primary paper removes the independence assumptions, derives a closed-form correlated model, and reports that the older approximation is conservative and the parameter sets it analyzes meet their required DFR limits: [Annechini–Barenghi–Pelosi, ePrint 2026/795](https://eprint.iacr.org/2026/795). The October 2026 HQC specification changes some parameter values and incorporates a refined correlated analysis: [HQC specification, 12 October 2026, §6.1.4](https://pqc-hqc.org/doc/hqc_specifications_2026_10_12.pdf).

This is an important audit rule: a missing premise invalidates a claimed derivation, but it is not itself an attack. The correct conclusion changes when later work provides a suitably scoped replacement bound.

## Other already-public outcomes, without attack detail

* SIKE advanced to NIST's fourth round, but NIST's final report says that it is insecure and eliminated it from the project: [NIST IR 8545, p. 17](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf). This shows that finalist status is evidence of extensive review, not a security theorem.
* Classic McEliece's tight KEM proof is conditional on OW-CPA security of the original construction; an alternative route assumes Goppa-code indistinguishability and random-code syndrome-decoding hardness. NIST describes these assumptions and notes that recent cryptanalysis weakens the historical-conservatism argument without concretely breaking submitted parameters: [NIST IR 8545, pp. 14–15](https://nvlpubs.nist.gov/nistpubs/ir/2025/NIST.IR.8545.pdf).
* NIST selected HQC, not BIKE, in the fourth round. Current official status is selection for a future standard, not an already published HQC FIPS: [NIST's HQC selection announcement](https://csrc.nist.gov/news/2025/hqc-announced-as-a-4th-round-selection).

## Reusable audit test

For any competition version, record the tuple

    (exact version, security game, reduction theorem, every premise,
     parameter-dependent bound, later revisions).

A scheme can be called publicly broken here only when a primary source or the official evaluator has already established that outcome for that exact tuple. Failure of a premise supports only the narrower statement that the claimed proof does not apply. Later revisions must be audited separately.
