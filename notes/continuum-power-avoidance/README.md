# Continuum power avoidance for bounded logarithmic gaps

One closed nowhere-dense one-periodic set of measure greater than 1−ε in every unit interval simultaneously avoids all positive real leading powers with a positive-power remainder, for any prescribed countable family of configurations whose occupied dyadic logarithmic bins have bounded gaps near zero. Every sufficiently small image tail has infinitely many distinct misses. The result covers all translations, nonzero coefficients, positive leading and remainder exponents, and finite error constants; the functions need no regularity or measurability.

For the single configuration {2⁻ⁿ}, the same set avoids every affine null geometric progression, for every ratio in (0,1) simultaneously.

The complete reader proof is [paper.pdf](paper.pdf), with editable single-file source [paper.tex](paper.tex). [PROOF.txt](PROOF.txt) is a public text presentation of the audited argument. [PROOF_MAP.json](PROOF_MAP.json) maps its eleven proof sections to the received proof. This is packaging of an already completed written result, suitable as a source for later formalization. It is not Lean formalization.

## Exact scope

The source condition is bounded gaps between occupied dyadic logarithmic bins. The remainder is bounded by M a^(s+α) for some α>0. The statement does not cover arbitrary slow o(a^s) remainders, all C¹ diffeomorphisms, flat germs, or every positive-upper-Banach-density configuration. Its finite parameters are enormous; no practical construction or runtime bound is claimed.

The sparse-block example S=⋃ₘ≥₃{2^(2^m),…,2^(2^m)+m} has upper Banach density one. Every sufficiently late output template of span at most C log U has no active point for some s∈[1,2]. Section 11 proves this exact obstruction to the present uniform output-window mechanism. It does not disprove a continuum avoidance theorem for the larger source class.

## Attribution and review

The nested-grid routing and exceptional-center repair are attributed to the pinned OpenAI geometric-case family 084 and mxym entry 006v1. Entry 006v2 supplies logarithmic-profile context but states a prescribed countable profile family. The six exact mathematical reference components and two original notices/licenses are retained in sources/. Their pins, URLs, bytes, and hashes appear in [REFERENCE_MANIFEST.json](REFERENCE_MANIFEST.json), [PINNED_SOURCE_VERIFICATION.json](PINNED_SOURCE_VERIFICATION.json), and [PROVENANCE.json](PROVENANCE.json).

The continuum arrangement principle has a primary antecedent in Kolountzakis–Papageorgiou, Analysis & PDE 18 (2025), 93–108, [Theorem 4.1 and its proof](https://arxiv.org/html/2208.02637v2#S4). The present curves become lines under v=log₂t. The arrangement principle itself is not claimed as new. Exponent-dependent activation, full boundary strata, absolute-position entropy cost, and positive-power buffering are proved here.

[Feng–Lai–Xiong Theorem 1.1](https://arxiv.org/html/2312.01319v1) states a global bi-Lipschitz embedding with f′(0)=1. The global C¹-diffeomorphism endpoint is separately proved in the retained 006v1 source. These are comparison results, not premises of this avoidance proof.

[TECHNICAL_AUDIT.txt](TECHNICAL_AUDIT.txt) presents the independent AI-assisted mathematical audit, which passed the bounded-gap written proof. It retains every mathematical assessment and finite-control result while removing delivery/workflow text. The verdict is not human peer review, proof-assistant verification, journal acceptance, exhaustive literature review, novelty certification, or an open-problem-priority claim.

A dated consequence is a negative answer to [Question 1 in Burgin–Goldberg–Keleti–MacMahon–Wang, arXiv:2210.09284v1 (17 October 2022)](https://arxiv.org/html/2210.09284v1#S1). Take the compact F=E∩[0,1], of measure greater than 1−ε; for any a≠0, b, and q∈(0,1), set s=−log(q)/log(2) and f(u)=b+a u^s. Then f(2⁻ⁿ)=b+a qⁿ has zero remainder, so every tail has infinitely many points outside E and F. This concerns that exact dated formulation. It does not assert that the question remained open in 2026, priority, or a broader Erdős-conjecture resolution. Later-literature comparison remains incomplete.

## Replay the exact controls

Only Python 3's standard library is needed, offline:

    python3 -B verify.py
    python3 -B -O verify.py

Both submitted and separately authored independent checkers run normally and with optimization. The runner requires byte-identical outputs equal to the stored reports, verifies the pinned source bytes, and checks manifests and archive members. No assert-dependent check is used.

The independent oracle checks 5,322 exact activation representatives, 320 preorder templates, 2,352 entropy inequalities, and 4,096 selector assignments in actual two-level nested routing. Distinct terminal keys give failure 28561/38416. Deliberate coarsening gives 469225/614656 and collisions in 732 assignments. Parameter-boundary, closed-activation, one-buffer, and 20 sparse-block negative controls detect specific faulty replacements. These finite tests do not prove the infinite analytic theorem or enumerate its calibrated routing tree.

## Rebuild the PDF

With a working TeX Live installation including the packages used by paper.tex, and Poppler:

    python3 -B verify.py --build

This builds in a fresh temporary directory using three pdflatex passes with shell escape disabled, rejects overfull boxes and unresolved references, checks the recorded page count, and extracts the full text. The installation needs its usual writable format/font caches. No external TeX inputs or downloads are required. VERIFICATION.json records the actual page count and all-page visual inspection; byte-identical PDF output is not required across TeX installations.

For a direct build, run pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error paper.tex three times outside the frozen release directory.

## Package integrity and licenses

SOURCE_MANIFEST.json enumerates the actual deterministic source-archive members and hashes all except itself. source.tar.gz includes the reader proof, public audit, source references/notices, exact checkers, reports, provenance, and reproduction tools. It excludes the PDF, release-only metadata, logs, caches, render images, and private runtime/delivery material. MANIFEST.json hashes the complete release payload except itself. PUBLICATION_WHITELIST.json is the complete permitted public-copy path list. ORIGINAL_INPUT_HASHES.json records all 17 original received bundle members, all seven original audit members, and both archive hashes without importing private delivery text.

    python3 -B pack.py

Repacking is deterministic for the same source bytes: lexicographic member order, fixed tar ownership/mode/time, and gzip timestamp zero. Use it only on a working copy. Checksums certify bytes, not mathematical truth.

The original Apache-2.0 license and mxym provenance notice are preserved byte for byte. The notice explicitly grants no new blanket license for separately authored material. No additional license is invented by this package.
