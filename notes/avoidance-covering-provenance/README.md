# Source provenance for the avoidance and covering refinements

The two notes have distinct proof dependencies. Their mathematical mechanisms must not be conflated.

- [Bounded-cluster avoidance](../bounded-cluster-avoidance/paper.md) extends the routing, entropy, and exceptional-center repair of OpenAI family 084 through mxym entries 004 and 006. Its added step is simultaneous whole-cluster success. Entry 003 is comparative context only.
- [Critical covering gauge](../critical-covering-gauge/paper.md) refines mxym entry 003. OpenAI family 098 supplies the sheet-crossing analytic nonembedding mechanism; the new scale schedule, gauge transfer, and exact packing lower bound are proved in the note. Classical Dvoretzky transfer and compactness-based finite-witness selection are qualitative dependencies.

[PROVENANCE.json](PROVENANCE.json) binds every bundled source snapshot to an immutable repository commit, repository path, Git blob SHA-1, SHA-256, and byte size. OpenAI sources use commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Preceding mxym sources use commit `1c67b4146f9e54291c8a5ca1f42a028bf307629f`. The audited theorem subjects are preserved separately, so the bounded-cluster tail-maximization correction and all later exposition can be compared with the exact audited text.

The gauge PDF includes the complete supporting entry-003 proof, with its analytic appendix. That supporting text retains entry 003's own schedule example. The gauge theorem selects its finite witnesses anew for the new schedule, using the supporting text's explicitly scale-flexible lemmas.

## Rights and disclosure

OpenAI material retains its Apache-2.0 license, reproduced in [OPENAI_MATH_LICENSE.txt](OPENAI_MATH_LICENSE.txt). Mathematical provenance is retained in the notes and in the source snapshots. No affiliation with or endorsement by OpenAI is implied. No additional license has been selected for newly authored material; public availability does not imply one.

These are AI-assisted research notes with independent model-conducted ordinary mathematical audits. They are not human-refereed papers or proof-assistant formalizations. Exact finite checks concern the supplied finite certificates only. There is no literature-priority claim, no universal C1 avoidance claim, and no claim that dimension two is the smallest nonembedding dimension.

## Reproduction

Run `python3 verify.py` from this directory for the exact finite checker replays, independent oracle comparison, source hash checks, and full public-file manifest check. Run `bash build.sh` to reproduce the two PDFs from their editable LaTeX sources. Python uses only its standard library. PDF compilation uses pdfLaTeX with standard TeX Live packages; the default build requires no network.
