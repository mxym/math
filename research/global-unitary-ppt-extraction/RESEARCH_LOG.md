# Research selection, audit and attribution

## Starting state

Started from live main `201c4235`, after reading the current README, SOLVED_PROBLEMS, RESEARCH, recent commits and the entire companion negativity proof. No tracked or applicable parent AGENTS.md was found. The old qutrit proof and preprint and the negativity preprint are already published; this continuation does not recreate or edit those immutable versions. No parallel work on this operational extraction problem was present in the inspected index.

## Selection and progress

Repeating the higher-dimensional APPT purity numerical search was not selected: its existing research log identifies an unresolved multilevel gap and no new mechanism. Extending the negativity result merely by more sample spectra would not address the requested research scale either. The chosen target instead asks for faithful entanglement extraction after global-unitary preprocessing, together with the full above-capacity fidelity law.

The completed derivation has two distinct outputs: capacity under local/LOCC/completely-PPT postprocessing, and an exact all-rate cPPT fidelity exponent for every spectrum. The nontrivial converse uses the squared Hilbert-Schmidt budget Tr(M^2)<=N/K^2 for the Rains fidelity effect. A trace budget alone would not prove the half-entropy-deficit threshold. The lower exponent is obtained by applying the Bell-projection construction to a feasible fidelity effect, not by assuming that negativity is distillable. A separate local Kraus construction proves faithful extraction below capacity. This avoids conflating the cPPT map with LOCC.

## Literature and external inputs

- Rains, arXiv:quant-ph/0008047v2, Theorem 3.1: exact fidelity-effect SDP. The original PDF statement and proof were read through the web's parsed PDF output; screenshot requests failed with cache errors. The SDP and isotropic-map proof are reproduced algebraically in our own notation, with credit. No claim is made that this is new.
- Tropp, arXiv:1004.4389v7, Theorem 1.4: independent centered self-adjoint summands, one-sided eigenvalue bound, variance sum; apply also to the negatives. The primary theorem text was retrieved; screenshot requests failed with cache errors. It is an external proved theorem, not something the exact checker proves.
- Fang, Wang, Tomamichel, Duan, arXiv:1706.06221v3, revised 1 October 2019: nonasymptotic PPT distillation and second-order analysis. The unversioned abstract was checked before selecting v3. The current task additionally optimizes a collective global unitary on the input spectrum.
- Lin, Li, Fang, arXiv:2601.10190v2, revised 16 January 2026: error-exponent analysis under non-entangling and other state-preserving operations. The live abstract showed v2; its HTML was inspected. Example 1 defines PPT-state preservation, not the complete partial-transpose-conjugation condition used here. Neither this stronger operation class nor ordinary fixed-state distillation is silently substituted for our task.
- Kondra et al., arXiv:2605.29197v1, Supplemental Lemma 6: prior finite-copy activation. The qualitative fact is credited, not claimed as a new result.
- The companion repository preprint, frozen at `3fac265d142cbc5ce48700abce5cced59a1a4b8f`, supplies the earlier Bell-projection mechanism. The new proof restates it fully. The copied `bell_checks.py` is byte-identical to that companion's checker, with SHA256 `008d4e21d4528bd4a653db8892ffab0d4a1aab509e4d242fe35679883034fe35`.

Public source locations:
https://arxiv.org/abs/quant-ph/0008047
https://arxiv.org/pdf/1004.4389v7
https://arxiv.org/abs/1706.06221
https://arxiv.org/html/2601.10190v2
https://arxiv.org/html/2605.29197v1

Targeted searches used global-unitary/spectrum/purity/entropy-deficit/entanglement-extraction/PPT/strong-converse combinations. They did not identify the same spectrum-optimized formula, but this is not exhaustive priority certification. Pure-subspace packing and typicality are standard methods. The claimed contribution is the combined operational law with matching exact cPPT fidelity exponent, not new invention of those inputs.

## Proof audit and limitations

The proof was checked stepwise for: fidelity versus root-fidelity convention; necessity and sufficiency of both PPT order bounds; trace preservation of all channels; zero eigenvalues; nondivisible local dimensions; the target dimension beyond the input's smaller factor; types not necessarily forming a top prefix; the three escort regimes and their boundary equalities; and the distinction between exponent zero and fidelity tending to one at the critical rate. The capacity proof uses deterministic local Kraus maps with a branch for every leftover coordinate, not postselection.

The current checks verify explicit algebra and small quantum matrices. They are not Lean verification or independent peer review of the unbounded analytic result. The exact LOCC strong-converse exponent is not closed; the cPPT bound is a valid converse for LOCC but its achieving channel need not be local. No simple bound is presented as a full solution to ordinary mixed-state distillation.

The direction is retained because it produced matching analytic bounds for the complete stated task. Future changes should target the remaining operation-class gap or another comparably substantial structural problem, not merely enlarge the regression table. Research and writing used AI assistance.

## Final current-literature check

A final search surfaced Lami, *On PPT entanglement distillation*, arXiv:2610.12454v1 (submitted 8 October 2026). The primary arXiv abstract and PDF were retrieved through the authorized shell after web-tool cache misses; the source PDF and parsed text were read, including Corollary 13 and equations (100)--(102). This is the same completely-PPT channel definition as ours, not just PPT-state preservation. Its quadratic converse with auxiliary state I/N already yields one half of log N minus state entropy. The manuscript now explicitly credits this prior converse and shows the substitution. It does not attribute that bound's first discovery to this work. The mathematical addition is local achievability after spectrum-optimizing global preprocessing and the matching all-rate fidelity exponent; the fixed-input problem addressed by Lami is not solved here. No theorem or certificate was altered by this attribution correction.

Primary source: https://arxiv.org/abs/2610.12454
