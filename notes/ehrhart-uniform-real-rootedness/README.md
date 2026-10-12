# Uniform real-rootedness of the (132,213)-avoiding permutation-polytope family

[Read the complete paper](paper.pdf) · [LaTeX source](paper.tex) · [Source audit](sourceaudit.json) · [Review record](audit/REVIEW_NOTES.md)

For every d >= 3, the Ehrhart h*-polynomial H_d of this particular family has only negative real zeros. The new analytic proof covers **every d >= 1001**. Together with de Castro's explicitly imported finite Theorem 1.3 for d <= 1000, it resolves Conjecture 10.1 of the fixed [arXiv:2609.06096v1](https://arxiv.org/html/2609.06096v1).

A short corollary applies [Zhang's established Veronese theorem, Corollary 3.4](https://zhangbiaomath.github.io/papers/2020-prm-ipvc.pdf), to every positive integral dilate of this family. It is an application of a known preservation theorem.

The proof is an analytic argument with exact rational scalar and induction certificates. It is not Lean formalization, external human referee endorsement, or a claim of globally verified priority. The original d <= 1000 coordinates and their 498500 finite tail inequalities have not been independently reconstructed here. Their official CSV was streamed in full and its SHA256 and byte length independently confirmed; byte-integrity verification does not replace the imported finite theorem.

## Reproduce the certificates

Ordinary Python 3 and its standard library suffice:

    python3 reproduce.py
    python3 reproduce.py --negative-controls

The first command runs the three unchanged exact programs under normal Python, -O and -OO, checks every packaged file against the manifest, compares every witness byte for byte, runs the 39 supplemental exact residual checks, and verifies the 33 closed intervals join without gaps. The second adds six fail-closed controls: invalid q and an invalid margin under all three modes. The controls run in temporary copies and do not change the original scripts.

The programs certify scalar bounds and induction bases. The proof of their implication for all dimensions and all infinite tails is in the paper. Float conversions are diagnostic displays; acceptance uses rational arithmetic and explicit exceptions.

## Compile the paper

With pdfLaTeX and the standard packages listed in paper.tex installed:

    python3 build.py

This rebuilds paper.pdf from paper.tex and interval-table.tex. The distributed PDF was actually compiled, and every page was visually checked for formulas, references, table coverage and overflow. Rebuilding replaces the canonical PDF; retain the distributed copy if checking its published checksum.

## Files and provenance

- verification/: the three original exact programs and independent_residual_checks.py.
- certificates/: the unchanged three original witnesses and the supplemental residual witness.
- provenance/: exact official finite-certificate Release/asset metadata and the completed streamed-byte verification.
- audit/: the final review record, candidate-to-paper mapping, captured reproduction result, and PDF inspection result.
- audit/reviewed-candidate/: immutable historical candidate notes and their original manifest/checksum file, preserved for traceability. Their old status labels are historical evidence, not statements about the final paper.
- MANIFEST.json and SHA256SUMS: canonical package integrity.
- sourceaudit.json: all original input hashes, relocation mapping and final proof-section correspondence.

The source's identities, endpoint facts, repair criterion, product/norm estimates, and finite theorem are attributed explicitly. The current work strengthens the all-dimension analytic bounds for the one stated family. It does not prove a general theorem for arbitrary pattern classes, poset permutahedra or lattice polytopes.

The Release tag is bound to its exact public source commit. Its RELEASE_BINDING.json and SHA256SUMS_RELEASE identify the standalone PDF and full source archive; GitHub's immutable Release signature provides the official release verification.
