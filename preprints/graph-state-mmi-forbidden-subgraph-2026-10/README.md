# A forbidden-subgraph theorem for graph-state monogamy

**Public preprint; not peer reviewed.** Version DOI: [10.5281/zenodo.23272728](https://doi.org/10.5281/zenodo.23272728). Previous immutable edition: [10.5281/zenodo.23272367](https://doi.org/10.5281/zenodo.23272367).

We prove Fuentes–Keeler–Munizzi–Pollack, arXiv:2511.19585v1, Conjecture 1: for every finite qubit graph state, positive tripartite information implies that a locally equivalent graph contains an induced four-vertex claw. The proof gives the complete claw-vertex-minor-free component classification
\[K_1,K_2,P_3,P_4,C_5,W_5\]
and the sharp connected threshold seven.

- [Seven-page PDF](paper.pdf)
- [Complete written proof and exact certificate](../../research/graph-state-mmi-forbidden-subgraph/PROOF.md)
- [Canonical source package and literature screen](../../research/graph-state-mmi-forbidden-subgraph/README.md)

The finite certificate covers all 120 one-vertex extensions, all 1,511 one-step orbit transitions, and all 5,460 labeled four-block assignments. Two independently implemented standard-library checkers and explicit rejection tests pass. These finite checks supplement the all-order induction and entropy proof; the theorem is not claimed as a complete Lean formalization.

Reproduce from the canonical package:

```sh
cd research/graph-state-mmi-forbidden-subgraph
python3 check_certificate.py
python3 verify_independent.py
python3 test_rejection.py
```

No external human peer review or historical-priority claim is made. Research and manuscript preparation used AI assistance; no external funding. Original material is reserved unless a file states another license.


[Editable signed TeX](paper.tex) · [Standalone TeX source ZIP](paper-source.zip). Only article metadata, abstract presentation, display typography and bibliography typesetting changed; the canonical proof is unchanged.
