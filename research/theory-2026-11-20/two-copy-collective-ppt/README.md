# Two identical copies can fail even for collective bipartite PPT discrimination

Nine algebraically specified maximally entangled states in C³ ⊗ C³ form an orthonormal basis. With two identical copies, Alice may process her two qutrits jointly and Bob may process both of his. No perfect positive-partial-transpose (PPT) measurement across Alice:Bob exists. In particular neither collective separable measurement nor LOCC can succeed perfectly. This is an unassisted two-party example, not a restriction on the number of rounds, product measurements between copies, or only one-way communication.

## Read or replay

- **two-copy.pdf**, **two-copy.tex**: self-contained mathematical proof, complete 19-coefficient certificate, and positive-minor table.
- **verify.py** with **witness21.json**: standard-library exact integer verifier, run with python3 verify.py. It prints the 45 strictly positive Sylvester minors shown in full in **replay.txt**. Omega is represented by integer pairs in Z[ω], not floating point. The scale field is inessential because multiplying the whole witness by a positive number does not change positivity.
- **root_audit.py**: independent explicit Kronecker-product construction with the Python package SymPy, using sqrt(-3), alternate basis ordering and direct matrix contractions. Run with python3 root_audit.py. Both scripts enforce checks even with Python's optimization flag.

The proof has two independent pieces. First, equality in the maximally entangled PPT trace bound forces the partial transpose of each locally rotated effect to live on the symmetric square. A matrix-element reshuffling identity, positivity of the original effect and the global completeness equation then provide the wrong-label and local-swap constraints. This argument does not assume the PPT effects are separable. Second, a positive matrix given by the 19-coefficient witness must have zero trace against a nonzero positive effect, a contradiction. Twirling acts on the witness, not on an assumed invariant measurement. The integer controls are specific to this second step.

## Boundaries and prior results, checked through 20 November 2026

- [Bennett et al. (1999)](https://arxiv.org/pdf/quant-ph/9804053), printed p. 20, asks whether more than two copies can be necessary. This paper resolves the **two-party orthogonal pure-state collective PPT, SEP and LOCC versions** negatively for universal sufficiency, not every variant.
- [Russo's two-copy problem](https://vprusso.github.io/posts/two_copy_problem/) emphasizes that a valid obstruction must cover measurements acting jointly across local copies; separates SEP, LOCC and PPT.
- [Li–Wang–Zheng, September 2026](https://arxiv.org/abs/2609.07233) establish collective hardness as the number of separate parties grows. Grouping parties changes the allowed operations.
- [Bandyopadhyay, v2 7 November 2026](https://arxiv.org/html/2610.16138v2), Sections 1 and 7, distinguishes the bipartite open question from multipartite results and exhibits a specific 2⊗2 example distinguishable by collective SEP despite failure of adaptive copywise SEP. Our example is different and does not decide whether that two-qubit example is collective-LOCC distinguishable.
- [Ghosh et al.](https://arxiv.org/abs/quant-ph/0205105) treat canonical maximally entangled states; our basis is not assumed canonical. [Bandyopadhyay–Russo](https://arxiv.org/abs/2406.13430) treat access to a separate known resource, not a copy with the same unknown label.
- Searches of recently indexed original papers and the mxym/math tracked tree found no directly matching bipartite counterexample. This is not a guarantee of priority. No finite physical experiment is used.

The PPT copy complexity is **exactly three**: [Nathanson's Theorem 4](https://arxiv.org/abs/1310.4220) supplies a perfect PPT measurement on three copies, which are nine orthogonal maximally entangled states of local dimension 27. At least three are necessary under SEP/LOCC, but the paper does not show that three suffice in those narrower models. We do not optimize the success probability or claim minimum example dimensions or unbounded copy complexity at fixed party number.

Follow-up: [explicit two-copy error floor and perturbation bound](Robustness.md), with [exact integer replay](robust_check.py). The positive-gap statement in the original archive is strengthened to average error strictly greater than 1/20,000,000 under uniform prior.
