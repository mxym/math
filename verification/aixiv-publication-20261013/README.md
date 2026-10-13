# aiXiv publication and deduplication, 13 October 2026

Author: Yongxian Zhang. AI declaration: `ai-assisted / OpenAI AI assistants`.
The agent followed [aiXiv's publication instructions](https://aixiv.online/skill.md).

This is a submission and document-review record. It is not a new execution of
the archived Lean proofs, a certification of historical priority, or an
external human peer-review report. All account records listed below were still
in the platform's `checking` state at the recorded readback time.

## New, nonduplicate author submissions

| Paper | Record | Exact scope |
| --- | --- | --- |
| Complex three-row pencil norm | [2610.01479](https://aixiv.online/abs/2610.01479) | Fully formalized principal coefficient-norm results |
| Continuum power avoidance | [2610.01480](https://aixiv.online/abs/2610.01480) | Continuum remainder theorem and compact affine-geometric corollary; both underlying Lean packages are identified |
| All cycle chromatic coefficients | [2610.01481](https://aixiv.online/abs/2610.01481) | Genuine cycle graphs, every n ≥ 3, classification and C17 consequence |
| Orbital primal-dual theorem | [2610.01484](https://aixiv.online/abs/2610.01484) | Universal finite-group action theorem, rational optima and sharpness |
| Quadratic-order moats | [2610.01486](https://aixiv.online/abs/2610.01486) | Original all-order Main by the weaker Dirichlet-supply route; no effective bound or strong prime-ideal PNT claim |
| Sharp simplex stability | [2610.01487](https://aixiv.online/abs/2610.01487) | Upper theorem and geometric exponent obstruction in the two separate source projects |
| Bapat original-interval counterexamples | [2610.01488](https://aixiv.online/abs/2610.01488) | Specified complex rational witness and real symmetric integer existence theorem in one manuscript |
| Four-row permanent–determinant inequality | [2610.01489](https://aixiv.online/abs/2610.01489) | Sharp coefficient, attainment, complete equality classification and real pencil norm |
| Four equal Gaussian cells | [2610.01490](https://aixiv.online/abs/2610.01490) | Written proof with explicitly cited external Gaussian isoperimetric results; no claim of a self-contained complete Lean proof |

The preceding four account submissions remain:
[APPT qutrit purity](https://aixiv.online/abs/2610.01472),
[all-graph Chollet](https://aixiv.online/abs/2610.01473),
[cofactor spectral asymptotics](https://aixiv.online/abs/2610.01474), and
[growing-gap avoidance](https://aixiv.online/abs/2610.01475).
The cofactor manuscript's later ramp/endpoint statements are not included in
the Theorem 1 Lean certificate.

## Existing imported records and withdrawn duplicates

The author reported claiming all nine imported records; claim approval was
pending. Account submission count and corpus author-search count are distinct.
Three newly created duplicate author submissions were withdrawn at the author's
instruction, leaving the original imported records as the canonical entries:

| Withdrawn duplicate | Retained imported entry |
| --- | --- |
| [2610.01482](https://aixiv.online/abs/2610.01482) | [Cyclotomic counterexample, 2610.01396](https://aixiv.online/abs/2610.01396) |
| [2610.01483](https://aixiv.online/abs/2610.01483) | [Entropy-root counterexample, 2610.01355](https://aixiv.online/abs/2610.01355) |
| [2610.01485](https://aixiv.online/abs/2610.01485) | [Half-line q-permanent, 2610.01400](https://aixiv.online/abs/2610.01400) |

The withdrawal reasons identify duplication only, without asserting a
mathematical defect. aiXiv retains immutable historical versions and withdrawal
records. None of the author's claimed imported entries was changed.

## Review and disclosure

The manuscript sources were compared against repository revision
`07559d229e39206f657b1b7a2d39d09da21fba41`; the older Windows copies have the same
text, with CRLF rather than LF endings. The active manuscripts were rendered
page by page and inspected. Downloaded online PDFs were also checked for page
counts and text outside the page. The four-row manuscript was typeset anew,
compiled twice without LaTeX warnings or overfull/underfull boxes, and visually
checked on all four pages. Its online PDF is byte-identical to the supplied PDF.
Its source-only server dry run also compiled successfully.

The Bapat submission's manifest, source ZIP and all 200 witness rows passed the
existing integrity checker under Linux. Both independent exact-integer
coefficient checkers were executed again and agreed. Those checks are not
labelled as a fresh Lean replay of the complex or real proofs.

No agent session files were uploaded, following the author's instruction to
minimize disclosure. Credentials and private account files are absent from this
public record. Optional AI process summaries, prompts and other extra fields
were not submitted.

## License metadata and the Gaussian submission

The latest version of the twelve preceding active account papers was read back
as `All rights reserved`; existing third-party licenses and notices remain in
force. Early submissions inherited aiXiv's default CC BY 4.0 metadata.
Subsequent tests showed that even explicitly supplying
`--license "All rights reserved"` on a new submission returned
`record.license = "CC BY 4.0"`, despite the CLI dry-run display showing the
requested value. The MCP `submit_paper` input schema accepts only `CC BY 4.0`,
`CC BY-SA 4.0`, `CC BY-NC-ND 4.0` and `CC0 1.0 (public domain)`;
`All rights reserved` is not a supported new-submission value. The unsupported
value was observed to fall back to CC BY 4.0. Metadata-only
new versions corrected the current records; historical versions remain intact.
This report makes no claim that changing the latest metadata erases historical
licenses.

The four-cell Gaussian paper is prepared and passed a server source-only dry
run. Its eleven-page signed PDF was rendered and checked. The original abstract
uses a section heading rather than a LaTeX abstract environment, so its exact
text was supplied as submission metadata. The paper explicitly cites the
published Gaussian isoperimetric and Milman–Neeman multi-bubble inputs and does
not claim a self-contained complete Lean proof. The latter's standard-Gaussian
normalization and q = 4, n = 3 applicability were checked against the primary
[Milman–Neeman source](https://arxiv.org/pdf/1805.10961v3): Theorem 1.1 gives the
perimeter minimum, and Theorem 1.2 gives uniqueness. The cluster perimeter is
one half of the sum of cell perimeters.

Its automatic submission was initially stopped before publishing because this
new-record license behavior conflicted with the author's rights instruction.
After the author explicitly approved CC BY-NC-ND 4.0 for this paper, submission
was repeated with that supported value and completed as
[aiXiv:2610.01490](https://aixiv.online/abs/2610.01490). The server record was read
back as `CC BY-NC-ND 4.0`, with zero attached traces. The source ZIP and author
PDF were both supplied; the downloaded eleven-page PDF is byte-identical to
the checked signed PDF. The original immutable DOI record was not altered.
This permission concerns the Gaussian paper, without imposing a new blanket
license on unrelated original research. Future submissions must check supported
license values and perform author/title/source deduplication before publishing.

[PUBLICATION_RECEIPTS.json](PUBLICATION_RECEIPTS.json) preserves the public
readback fields, version hashes, withdrawal state, downloaded PDF hashes, and
the actual time and scope of these checks.
