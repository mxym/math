# Exact source and reuse provenance

Requested manuscript: mxym/math c897a556e12e460380c7cf521e88f84286994915,
preprints/002-quadratic-order-moats/v3/source.tex.
SHA-256: c1349aba050aeb5c8c20a6dca07fd8d1f74d029ae9702775eaf96177b597d62f.
The companion PDF SHA-256 is f20775c47d8cce4143baf16d8936ac783e79dcaffaaa449d007cdce772c2ddfc.

OpenAI GaussianMoat source: openai/math
adc7f1241b42e322a6451854ab7e4b4c146bf78a, family028. The 41 actual solution
modules were retrieved under upstream-028/GaussianMoat. The solution Main.lean
contains a genuine `fullMain` proof, while ComparatorChallenges/GaussianMoat
is a comparison scaffold and contains a placeholder. That scaffold is never
imported, counted, or accepted as a proof. The actual solution is specialized
to GaussianInt, SplitSieve and primes congruent to 1 modulo 4. It is not an
imported all-order or A1–A5 theorem. Its original Main and most of its engine
are inspected reference sources, not replayed dependencies of this project.

The generic proof declarations in FiniteLaw.lean and FiniteEntropy.lean were
reused verbatim in Entry002/FiniteLaw.lean and Entry002/Information.lean.
Only imports, an unused namespace-open command, and the explicit autoImplicit
setting changed. Namespaces remain OAI.GaussianMoat to preserve their identity.
These are universal finite-law theorems despite the historical namespace.

The generic BooleanCube proof body is also preserved verbatim, and the generic
SignConcentration prefix through the fair-sign Hoeffding results is preserved
verbatim. Imports and unneeded namespace opens are adapted to the isolated
project. The first checkpoint checked eight complete bodies or exact spans. Round 2 adds further independently hash-checked generic spans and clearly identified adaptations; current exact counts are in logs/proof-reuse.log and proof-reuse.json.

Entry002/Telescope.lean additionally preserves exact generic source spans:
Information.lean 217–316 (cIf infrastructure), WalkWords.lean 178–187
(cHf_congr_fibers), InformationTelescope.lean 79–92 (finite_entropy_telescope)
and 138–150 (cIf_refinement). Four additional generic results are newly proved
with explicit block/smoothing-rate hypotheses. Those hypotheses are not proved
by that original numerical telescope. Round 2 GenericWords,
GenericWalkTelescope and GenericTimeKernels instead prove actual block/shift
rates and construct a true terminal smoothing size. The specialized Gaussian
smoothing theorem is never represented as a generic proof.

All OpenAI-derived source retains attribution and its Apache-2.0 license;
see ../upstream-028/LICENSE. No new license is assigned to the authored research
or new proofs. scripts/check_pins.py and controls/CompilerAudit.lean follow
mxym/math lean/ pin/audit conventions at the requested snapshot; the audit
ownership selector and complete inventory were adapted for Entry002 modules.
The audit tool is metaprogramming instrumentation, not a logical theorem or
an imported proof dependency. Its traversal uses partial recursion; no safe
logical root has a transitive partial/unsafe dependency.

Current exact file hashes and proof-body reuse hashes are recorded in the
frozen checkpoint manifests. A model's written-proof audit, any Python finite
certificate, and a typechecked target are never classified as a Lean theorem.

Round 2 generic probability, conditional/posterior coverage, numerical bands
and finite-law bodies are checked against the same pinned licensed source.
Each metadata record verifies original file hashes, exact span hashes, and
owned module hashes. Only spans actually present verbatim are labeled exact;
lattice/real-mean/counting adaptations are distinctly recorded. The generic
cumulative-to-inclusive dyadic conversion is adapted from the separately
authored mathlib-only analysis proof without importing its external PNT
dependency. The exact arithmetic package/patch/source-closure hashes and
isolated audits are recorded in references/upstream/arithmetic-provenance.json
and ArithmeticSupplyCoverage.md. All 999 external closure sources are included
only as a separately verified foundation project.

Round 3 retains the exact manuscript, target and toolchain bytes. It closes
the literal universal finite sieve with genuine arbitrary-lattice common-window
entropy, backward coverage, selected-prime growth and the actual common-law
information telescope. Its new generic source-reuse records verify the same
pinned licensed source and distinguish exact spans from adaptations.

The separately pinned arithmetic project now proves the complete all-order
prime-supply and MainTarget implications from one explicit genuine number-field
prime-ideal counting asymptotic. The count uses actual nonzero integral prime
ideals and their real cardinality normalized by x/log x; it is never an axiom
or a disguised target hypothesis. That analytic asymptotic remains unproved.
Actual ray modulus exponents, completion congruence, conductor lifting,
conjugate prime distinctness, tower splitting and finite exclusions are proved.

Round 3's external verifier also requires exact root-name sets, hashes of all
owned bridges and audit controls, and original upstream commit blobs followed
by the exact compatibility patches with byte-for-byte resulting source checks.
Negative controls exercise deletion of a root, omission of a source file and
alteration of a patch. These verification checks are evidence about provenance
and audit completeness; they are not additional mathematical proofs. Their
observed results are recorded in the isolated project's verification logs.
