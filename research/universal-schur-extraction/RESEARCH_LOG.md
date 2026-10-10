# Research log: universal Schur extraction

Started from live main `12568bde` after inspecting the README, SOLVED_PROBLEMS, RESEARCH, current extraction work and recent commits. No tracked or applicable parent AGENTS.md was found. A separate worktree prevents overwriting parallel tasks. The previous frozen proof/preprint releases are not edited.

## Target selection

The general APPT purity problem still has a multilevel spectral gap; its recorded numerical searches have not yielded a new exact mechanism. Repeating those simulations would not be meaningful progress. The selected target is a structural limitation of the new extraction law: state-aware preprocessing knows the eigenbasis and spectrum. Removing both pieces of knowledge changes the quantifiers and could destroy not just capacity but error exponents. The work also resolves the strict below-capacity reliability regime and its nondegenerate Gaussian threshold, previously excluded in the state-aware paper.

## Critical design obstacle and resolution

Assigning separate sectors to each Schur block but dropping blocks that are too large is insufficient: it can lose the maximally mixed and high-entropy contributions. Arbitrary truncation of the unknown representation factor is also invalid. The valid construction retains the full representation factor and truncates only its maximally mixed permutation multiplicity. This retains an exact, known polynomial fraction of every block's mass and preserves block diagonality for every input. Small blocks are never truncated and are extracted with full target Bell dimension, which preserves exponentially small error rather than merely a fidelity exponent of zero. No small-probability mixture with a baseline channel is inserted; such a mixture would spoil the reliability exponent.

## Proof checks

The argument distinguishes: one common unitary versus choosing a unitary after seeing the optimal shape; unknown quantum coherences versus only diagonal inputs; coherent dyads versus tested pure projectors; truncated versus complete blocks; fidelity versus root fidelity; and zero-error threshold versus interior reliability. The universal density operator dominates every iid input by a polynomial factor, allowing an ordinary iid CLT rather than an unproved CLT for Schur shapes. Every integer rounding loss is explicit. There is no assertion of uniform convergence for states approaching a transition with k.

## Literature actually consulted

Keyl--Werner arXiv:quant-ph/0102027v1 was read from primary PDF text and screenshots, including the Schur decomposition and highest-weight character inequality. Universal compression arXiv:quant-ph/9805017 and universal pure-state concentration arXiv:quant-ph/0109028 were checked. Hayashi arXiv:cs/0503089v2 supplies prior second-order source-coding context. Watanabe--Takagi, Nature Communications 17,1857 (2026), DOI 10.1038/s41467-026-69143-3, was read for its different state-agnostic thermodynamic setting.

The web cache for Lin--Li--Fang arXiv:2601.10190 returned January v2, while the direct primary abstract returned v3 revised 22 September 2026 with the new universal-distillation title. The reference is updated to v3; no claim of novelty is based on the old version. Search also identified Takagi--Watanabe--Matsuura--Arai--Hayashi arXiv:2609.40215v1. Its primary abstract and full HTML were retrieved directly after web-cache misses. It already proves universal ordinary mixed-state LOCC capacity, uses a different construction and operation class, and explicitly discusses error and second-order questions. Our theorem is not claimed to solve those standard-LOCC questions: it retains free global entangling preprocessing. The common theme of universality is not itself presented as a new discovery.

No exhaustive historical-priority certification is asserted. Standard representation theory and probability are mathematical inputs, not proved by the checker. The work is an analytic manuscript, not Lean formalization or external peer review.

## Remaining questions

The exact zero-error transition can have exact-packing exceptions and is not assigned a finite reliability value by continuity. The Gaussian statement excludes the dimension-limited cap and zero varentropy. Efficient state-independent implementation, standard fixed-input distillation, finite-copy APPT purity and APPT=AS remain open in this work. The direction was retained because it produced a common protocol and matching converse laws, not because additional regressions happened to pass.
