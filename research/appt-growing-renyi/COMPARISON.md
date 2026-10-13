# Literature and scope comparison for the growing-order APPT profile

Checked 2026-10-14, Asia/Shanghai. This is targeted primary-source screening,
not exhaustive priority certification. The new mathematical statements are
not credited merely because another source was not retrieved.

| Actual primary source read | Relevant existing scope | Difference of the present theorem |
| --- | --- | --- |
| [Ahiable–Kothakonda–Winter, 2608.03390v2](https://arxiv.org/html/2608.03390v2), Section 6.2 | Minimum von Neumann entropy of an inscribed polytope, APPT upper bounds and finite-dimensional numerical comparisons | U1/U2 optimize actual APPT states for moving positive Rényi orders, with uniform endpoints and precise stated aspect ranges. The projection/ratio/spike background is not newly invented here. |
| [Tran, 2609.18568v1](https://arxiv.org/html/2609.18568v1), Section 3 and scope remarks | Universal entropy relaxation and exact qubit–qudit von Neumann minima | The new results require m→∞ and concern a uniform moving-order profile. They neither re-prove the qubit finite theorem as new nor assert a fixed-m changing-order solution. |
| Repository fixed-order notes `ENTROPY_ASYMPTOTIC.md`, `SUBUNIT_RENYI.md`, `SUBUNIT_RIGIDITY.md` | Fixed finite α values, their all-aspect leading coefficients, fixed-aspect outlier criteria | A finite-grid monotonicity argument gives compact-order uniformity, but the two moving endpoints require new quantitative proofs. α→0 adds the m^(−α) effect; α→∞ requires logarithmic peak/bulk analysis and a different tolerance for entropy optimality. |
| Repository `ASYMPTOTIC.md`, `PROOF.md`, `APPTSubunit` negative-family core | Existing actual finite projection-plus-spike families and their respective sufficiency proofs | Existing families are reused with explicitly adaptive integer parameters. Their new uniform limit theorem is not inferred from an old certificate or counted as a new construction. |

The author HTML pages were opened and their entropy statements read. Exact
searches included `absolutely PPT growing Rényi`, `absolutely positive partial
transpose Renyi entropy maximum`, and `APPT high-order entropy`. No matching
moving-order statement was identified in the actual primary papers checked.
The search is bounded and cannot rule out all later or unpublished work.

Every supplied ordinary proof uses the original all-unitary APPT matrices,
actual ordered eigenvalues, exact trace normalization and finite Schmidt SOS.
No sampled-unitary, scalar relaxation or externally assumed main conclusion
is used as a proof premise. Standard spectral theory, convexity and real-power
calculus are mathematical background. The comparison literature supplies
attribution and context rather than an unproved quantum bridge.

This is one APPT research continuation. U1/U2, endpoint formulas, spectral
criteria, a phase-window comparison and auxiliary controls are not separately
counted as distinct major conjecture breakthroughs. No unsupported importance
rating or general absolute-separability conclusion is added.
