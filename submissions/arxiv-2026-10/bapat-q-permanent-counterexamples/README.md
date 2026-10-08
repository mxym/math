# Counterexamples to Bapat's q-permanent monotonicity conjecture

**Author:** Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536).

[Read the PDF](paper.pdf) · [Uploadable TeX ZIP](bapat-arxiv-source.zip) ·
[Audit](AUDIT.md) · [Metadata](SUBMISSION_METADATA.json)

One paper combines two independent proofs concerning the same original
monotonicity conjecture on `[-1,1]`:

1. A specified 200-by-200 complex Hermitian positive-definite matrix with
   rational real and imaginary parts, together with a specified rational
   `q0` in `(0,1)` satisfying `P_q0(B) > P_1(B)`.
2. Existence of a non-diagonal integer real symmetric positive-definite
   matrix with `P'_1(B) < 0` and rational `0 < q0 < q1 < 1` satisfying
   `P_q0(B) > P_q1(B)`. This proof gives no numerical real matrix or
   explicit dimension bound.

The paper contains the complete real existence proof and every complex
coefficient row. The source ZIP includes `main.tex`, `witness.tex`, and the
four data/checker files plus a guide in `anc/`. It excludes the preview PDF,
build debris, private paths, and the large Lean source bundles. Those bundles
remain available in the fixed immutable records cited in the paper.

The two principal counterexample conclusions have complete Lean certificates.
The combined manuscript itself is an editorial consolidation; this preparation
does not claim a new Lean replay or complete formalization of every sentence.
The complex certificate has 30 roots and a 22,812-declaration replay closure;
the real certificate has 776 owned declarations and a 54,739-declaration
union replay closure. Historical input-run timeouts and subsequent successful
continuations remain distinguished. See [the audit](AUDIT.md) for exact scope.

To submit after registering, upload **`bapat-arxiv-source.zip`** as the TeX
source, use `main.tex` as the compilation entry point, and copy the prepared
title, author, and abstract from [the metadata](SUBMISSION_METADATA.json).
The primary category suggestion is `math.CO`, with `math.RA` as a possible
cross-list; these are recommendations, not arXiv moderation decisions.
Choose the distribution license in the arXiv interface and check the PDF
compiled by arXiv before completing submission. Do not upload `paper.pdf`
alongside the TeX ZIP as an extra source document.

The author has not yet registered; no arXiv identifier, submission date,
acceptance, human peer-review approval, or guaranteed historical priority
is claimed. AI assistance and absence of external funding are disclosed
in the manuscript. Source provenance and verification inventories are
provided alongside it.

Check the distributed files and their source correspondence with
`python3 -B check_package.py` from this directory. This verifies the file
inventory, hashes, ZIP/source byte equality, bibliography keys and all 200
witness rows. It is an integrity check, not a new mathematical proof check.
To rebuild and rerun the exact arithmetic, use the parent build script
documented in [the submission guide](../README.md).
