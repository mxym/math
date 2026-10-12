# Quantitative stability and local error exponents for power Hadamard matrices

A complete English research manuscript consolidated from the corrected, analytically reviewed Hadamard series of 8 October 2026.

## Read

- `main.pdf`: typeset paper
- `main.tex`, `sections/*.tex`, `references.tex`: editable LaTeX sources
- `SOURCE_MAP.md`: section-by-section source and proof coverage
- `provenance/source_manifest.json`: input identities and SHA-256 hashes
- `certificates/`: the two unchanged exact finite-certificate files
- `BUILD.md` and `build.sh`: compilation instructions
- `qa/QA_REPORT.md`: compilation, rendering, and editorial checks
- `SHA256SUMS`: release-file byte-integrity manifest

## Results and scope

For exactly unit-modulus matrices of order `2m`, the residual is the largest **unnormalized operator norm** of the Gram errors for **all entrywise powers `1,...,m-1`**. At residual at most `2^-24 m^-3`, the paper constructs an exact solution within `512 sqrt(epsilon/m)` in labelled dephased maximum-entry distance. For odd `m`, nearest-root rounding produces a cyclic `GH(m,2)` seed. At all half-orders, root and compatible-rectangle certificates give an actual exact phase-circle point.

The rectangle graph identifies the full simultaneous tangent kernel and gives polynomial linear conditioning when connected. The paper proves diameter at most seven for the explicitly stated classical quadratic MUB family, with the rate `56 H_(p-1) epsilon/p` under `epsilon <= 2^-34 p^-3`. Second-order liftability and per-point optimal local exponents are classified. A concrete order-four curve proves that the global square-root exponent is necessary when even half-orders are included.

The exact classification and finite-circle geometry are attributed to `mio-qwq/math` at commit `0f0e59c0bfce75b89998fff413da31e957971f82`, including its stated OpenAI order-six antecedent at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The quadratic MUB seeds and finite examples are classical. The paper preserves these attributions and reproduces the required exact arguments in an explicitly attributed appendix.

No claim is made of new seed existence, general odd-half-order graph connectedness, ordinary first-power isolation for the whole quadratic family, formal verification, professional peer review, or historical priority. Ordinary isolation and zero ordinary defect are explicitly distinguished. Constants are not optimized, and literature comparison remains incomplete.

## Preparation status

The source revision passed an independent AI-assisted analytical review and a limited revision recheck. This consolidation preserves that scope and has a separate editorial source-coverage check; it is not a fresh mathematical certification. Obsolete “awaiting audit” labels from the earlier notes are superseded by the dated review receipt, without changing the frozen inputs.

The final typeset copy and corrected external boundary-example label are ready for the original reviewer’s limited final-copy check; that check is still pending. Exact calculations for the label correction are in `provenance/EDITORIAL_CORRECTIONS.md`.

No Git operation, repository publication, attachment delivery, new mathematical search, or expanded parameter computation was performed in preparing this directory. Existing TeX resources were reused. Authorship and licensing have not been assigned or changed by this editorial packaging step.
