# Candidate screening and one stopped route

This note records actual screening rather than converting an unsuccessful search into an openness assertion.

## Candidates excluded before sustained research

**General two-qubit CQC.** Wang, Wang, and Chen, *Complementary Quantum Correlations Are Universal for Qubits*, arXiv:2608.04916v1, supplies a proof for all two-qubit states with complementary local measurements. The primary PDF was checked. This is not treated as an open target or re-proved as a new result.

**Strong spin alignment.** Song and Chen, *A counterexample to the strong spin alignment conjecture*, arXiv:2603.25410v1, already gives a counterexample. Its original majorization statement is therefore not an eligible new target. The article separately formulates a compatible-marginal refinement; the entropy conjecture is not refuted by its counterexample. These statements were kept distinct.

## Compatible-marginal spin alignment: stopped discovery route

A local exploratory script attempted alternating optimization of a global pure state, a Ky Fan projector, and a probability vector of replacement-channel subsets, for several three- and four-qubit configurations. It produced no rigorous result. More importantly, the weight optimization often collapsed to the empty/full subset or other degenerate equality cases, and some tested eigenvalue ranks were already at or above the aligned target's support rank. Thus zero numerical gaps were not informative evidence for the conjecture.

This failure mode was identified and the route was stopped rather than reported as a theorem or as supporting numerical verification. No claim of exhaustive search, no certified counterexample, and no proof of the compatible-marginal refinement is made. An improved search would need a nondegenerate fixed-support weight domain and a separate certification step, but that is not part of the present result.

## Selected stronger ECQC target

The repository had just completed the pure-state validity classification. Its remaining full-rank equality question and the natural entire pure stabilizer class admitted a new exact route: Holevo equality gives monomial measurement matrices, while stabilizer measurements reduce to intersections of projective lines. This produced the two complete classifications in this companion manuscript, plus a general spectral/rank obstruction. It is not merely another low-dimensional counterexample, and it does not claim to solve the remaining unrestricted high-dimensional pure-state optimization.
