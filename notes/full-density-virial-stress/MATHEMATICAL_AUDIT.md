# Mathematical audit of the virial and stress supplement

7 October 2026. Scoped pass relative to H1–H6. This is an independent model review of the extension, not external peer review, formal verification, or a reproof of the imported package.

The full mathematical audit examined source SHA-256 `5af01c2374e1bb92417613b9e0a39f278d0952ff68383ba02e5346baa2ec0576`. The public source has SHA-256 `0a7a44d4900f964d036cceb6a6826d3c306d57dae5b625896b390633932beec3`. Only source-navigation, bibliography, and reproducibility prose changed; all 15 theorem, assumption, lemma, proposition, corollary and proof environments, and the entire H1–H6 operational import list, are byte-identical. See EDITORIAL_CHANGES.md and AUDIT_PROVENANCE.json. Historical audit hashes are review provenance, not required mathematical dependencies.

The public dependency map pins OpenAI/math at `adc7f1241b42e322a6451854ab7e4b4c146bf78a` and mxym/math entry 009 at `6785c1c830f8e19e2eb07b0bb89f4d475a8b154a`. The original review independently checked upstream Git blob IDs against the live commit-pinned GitHub API and verified every cited label. The public verifier checks the corresponding files in explicit reader-supplied checkouts without network access or changing expected hashes. Upstream filename prefixes 06, 07 and 05 compile as printed Sections 5, 6 and 7; the manuscript uses the corrected numbering.

## Imported statements and the absence of circularity

The following dependency allocation is accurate.

1. **H1:** Upstream `prop:initial`, its factorial inequalities and particle-number moments, `lem:kinetic-envelopes`, `thm:dhm-package`, `eq:dhm-partial-slab` and `prop:one-root` give the stated initial and zeroth-order kinetic controls. The supplement proves the needed first-order vacancy coefficient directly.
2. **H2–H3:** Upstream `lem:autonomous-partition`, `eq:retained-kernel`, `lem:one-slab-expansion`, `eq:crude-operator`, `lem:marked-regrouping`, `lem:diagram-labels`, `lem:stopped-variation` and `thm:marked-expansion` supply finite root-output algebra and unweighted variation estimates. Their dependence is on bounded output tests and a fixed record count, rather than derivatives of a record or a prescribed number of its updates.
3. **H4:** Upstream `eq:sharp-input-bounds`, `lem:sharp-merger-coordinates`, `eq:sharp-scaling`, `lem:sharp-factorials` and `lem:sharp-summability` supply the positive retained-history Gaussian and size estimates. In particular, the fixed-position version is stated and proved; it is not inferred from an integrated spatial bound.
4. **H5:** Upstream `lem:sharp-no-extra`, `eq:sharp-uniform-tree-convergence`, `lem:sharp-spatial-traces`, `lem:sharp-tree-completeness`, `lem:sharp-tree-splitting` and the proof of `prop:tree-evolution` give the qualitative geometry, projection identities, conditional products and last-contact algebra. The source’s marks are observation records. The new collision increments and their resulting scalar source are proved in the supplement.
5. **H6:** Upstream `prop:cutoff` and `eq:cutoff-probability` give the full-time common-data discrepancy probability with exponent 21/20. The supplement separately establishes transfer for the unbounded polynomial observables using deterministic domination.

The public entry 009 manuscript’s `lem:record` is properly identified as a passive collision-count precedent. Neither its fluctuation conclusions nor any speed-weighted incidence limit is imported. No auxiliary unpublished calculation is a theorem input. Thus the new assertion is a conditional theorem with a reproducible dependency boundary, rather than a claim that the underlying kinetic package has been reproved inside this source.

## Weighted-record proof

### Deterministic record bound

For one slab, use its final accepted C-components. No accepted collision crosses a final component’s boundary. The total energy of the labels in that final component is therefore conserved throughout the slab, even before all its prefixes have merged. Starting from speed bound V, its size cap gives the bound square-root(Lambda_i) times V at every time, not just at the slab endpoint.

Iteration through the fixed number L of slabs gives the displayed product bound. A component has at most Lambda_i − 1 + Gamma accepted edges, counting repeated contacts, so each particle has at most that many incidences in the slab. The displayed D_epsilon consequently bounds the actual accumulated B-mark by a fixed power of the logarithm. It uses no typical-N truncation. The same domination holds for the signed stress record after multiplication by the fixed norm of grad(a).

### Globally bounded tests on signed branches

The clipped test is globally bounded on the entire record space, including artificial signed birth inputs. Its powers have the same property. On the actual process, multiplication by P_epsilon recovers the raw mark exactly. On a retained branch the restored clipped value is bounded by the raw absolute mark, and on every fixed finite history clipping is eventually inactive.

The unweighted total-variation error is multiplied only by P_epsilon to the fixed moment degree. Its exponential smallness survives. Arbitrary-power complexity and nonphysical-initial tails are chosen after that degree and likewise survive. This argument does not presume compact support of all artificial signed inputs, a weighted microscopic remainder, or any convergence rate for a normalized record. In particular the proof never multiplies merely qualitative normalized-record convergence by the divergent scale P_epsilon.

### Energy and size domination, including conditional positions

At fixed complexity K and total slab size n, the number of contacts is at most n plus a K-dependent constant. Every incoming B is bounded by square-root(2E), where E is total birth energy. A degree-r raw mark therefore costs at most a fixed polynomial in n and E.

A fixed fraction of the common Gaussian can absorb any subsequently fixed energy degree, with a degree-dependent front constant. Equivalently, shifting the source energy-bin power from A/2 to (A+r)/2 changes the gamma/Stirling estimate by a fixed-degree polynomial in 1+A. Neither method introduces a moment-dependent geometric size base or requires another choice of microscopic L. The remaining polynomial is summed by the existing geometric size majorant.

The same calculation is valid after prescribing a root position, because the source constructs that version by solving for the common translation with unit Jacobian and using the same birth-energy envelope. Joining two components is controlled by a uniform conditional bound for one and an integrated bound for the other, with a fixed Gaussian allowance for the incoming flux. Consequently the collision products are well defined; no product of unspecified almost-everywhere disintegrations is used.

The final wording correctly restricts these raw retained-history moment bounds to each fixed complexity cutoff. High-complexity terms are removed using clipped tests, not an unstated unclipped high-complexity moment estimate. Second and higher fixed moments provide the uniform integrability needed for the first moment and any higher moment explicitly used.

### Finite histories and last-contact identification

The proof fixes complexity, size and energy before taking the geometric limit. Outside the imported null sets, the prescribed incoming velocities, normals and contact times converge and no extra contacts remain. Each finite sum of marks therefore converges. The weighted bounds remove the truncations; physical links keep their epsilon gain and cyclic terms vanish qualitatively. Interface inputs are replaced through their Bol-norm convergence. No first-order contact rate is needed.

The last-contact calculation correctly begins with global reverse-chronological C/O cancellation on unused auxiliary lines. It does not simply delete the last contact on the root while leaving later auxiliary contacts in place. After projecting unused records, an auxiliary C/O pair has the same tested-root output and incoming flux and opposite signs. The B update does not copy a partner’s past mark, so this cancellation remains valid.

After pruning, deletion of a root contact produces two genuine incoming components, with the source’s exact fresh-label factorials and an inherited combined-size restriction. Absolute summability removes that restriction before an unrestricted product is asserted. For the scalar root mark, the C-minus-O increment is B independently of both incoming marks; both components may therefore be projected to their unmarked marginals f_s. No fictitious zero history is assigned to an old partner.

The resulting one-root scalar source is J_f. Summing all particle marks counts every physical event twice, which gives H_epsilon^p converging to one half of the integral of J_f. The factors of two are correct.

## Mechanical identities, local stress and transfer

For centers x and x + epsilon omega, the velocity impulses are −B omega and +B omega. The pair virial increment is exactly epsilon B. Energy conservation and streaming then give the displayed virial and spatial-spread identities, including the factor 2 in front of the time integral of H_epsilon. Rejected contacts contribute zero. Overlaps elsewhere in the pasted flow do not alter these identities.

Energy conservation in the full 3N-dimensional velocity vector and the integrated triangle inequality for its position vector give absolute particle-sum bounds C_T N for the polynomial observables. The same argument bounds the local momentum and streaming observables using the bounded norms of a and grad(a). These are sufficient both for expectations and for the transfer estimate.

The vacancy calculation uses the actual grand-canonical activity normalization. The insertion identity and two-term Bonferroni inequality give the initial coefficient −(4 pi/3) rho_0 f_0 with no extra normalization counterterm. Compact initial support permits integration against each initial polynomial.

Hölder’s inequality gives the first-order transfer exponent

    −1 + (21/20)(1 − 1/p) = (p − 21)/(20p).

It is positive exactly for p > 21. This transfers expectations of the unbounded observables without extending a bounded-test coupling assertion by fiat. Subtracting the two exact virial identities transfers H_epsilon itself; a direct weighted collision-record bound on the bad coupling event is unnecessary.

For local momentum, the exact event mark is particle-exchange invariant and satisfies absolute value at most norm(grad(a)) times B. Its finite-history limit is B times the contraction of omega tensor omega with grad(a). The sphere integral has diagonal coefficients 2 pi/15, 2 pi/15 and 2 pi/5 when the relative velocity is axial. The unordered-event factor one half therefore gives pi/15 times the tensor |g| squared I + 2 g tensor g. Its integrated trace is J_f/2. The weak-balance sign is positive; the corresponding formal force is minus div(Pi_coll).

Pointwise cumulative B-record convergence upgrades to uniform time convergence because each microscopic cumulative expectation is nondecreasing and its limit is continuous. Signed stress records are handled correctly through their increment domination by the B-record, rather than by claiming monotonicity. The limiting J_f is integrable by the Gaussian bound on one factor and global mass and energy bounds on the other.

## Scope and resolved review findings

The two main theorems are full unit-amplitude statements for the specified excluded-product ensemble, compact initial position/velocity support and regular Boltzmann interval, conditional on H1–H6. The stress theorem explicitly inherits the same assumptions.

The source does not claim convergence of the complete mean correction, separate convergence of the local-defect terms, an order-epsilon contact expansion, a new unbounded-test fluctuation theorem, or a change from exact microscopic centering. It correctly leaves the generic signed contact residual open. The obstruction to an unforced linearized corrector is expressly restricted to a topology controlling the relevant moments and a solution class where cutoff approximation justifies those moment identities. This avoids silently imposing global moment equations on an arbitrary distributional solution.

The following issues were resolved during this review:

- Corrected the upstream printed section numbers, which differ from the source filename prefixes.
- Made the stress theorem’s shared hypotheses explicit.
- Made moment admissibility explicit in the obstruction corollary.
- Clarified that the raw retained-history moment estimate is at fixed complexity cutoff.

The earlier audit’s principal proof concerns are all addressed in the final manuscript: symmetric global clipping, conditional spatial Gaussian bounds, reverse-chronological auxiliary pruning, and direct scalar mark identification.

This audit verifies the mathematics and source correspondence described above. It does not certify every argument in U or DHM, literature completeness, external peer review, or independent bitwise build reproducibility across different TeX installations. The build and rendering checks are separate records. Subsequent edits to `manuscript.tex` require a new snapshot check before this audit can be associated with the changed bytes.
