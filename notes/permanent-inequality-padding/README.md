# Identity padding and a permanent inequality

This package proves Conjecture 9.3 of Sihong Pan, Mark Skandera, and Jiayuan Wang, *Permanental inequalities and unit interval orders*, arXiv:2610.04809v1 (3 October 2026), as a short consequence of their Theorem 8.18.

- `PROOF.md`: full statement, definitions, elementary lemmas, proof, and boundary cases
- `padding_note.tex`: concise typeset-note source
- `AUDIT.md`: independent check of the implication Theorem 8.18 ⇒ Conjecture 9.3
- `SOURCES.md`: primary-source and limited prior-work checks, dated 8 October 2026
- `SHA256SUMS`: checksums for all files above

The mathematical input is the authors’ balanced theorem. This package neither re-proves its long combinatorial argument nor claims priority for the padding observation. No computation is needed for the proof.

Verify file integrity with `sha256sum -c SHA256SUMS` from this directory.
