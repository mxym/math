# Technical verification summary for version 1

## Result and theorem scope

The source-level technical audit found no remaining mathematical obstruction to the manuscript’s stated theorem after the correction described below. The result is conditional on the explicitly imported analytic history package and Gaussian finite-dimensional limit from the pinned upstream manuscript.

For three-dimensional hard spheres in the Boltzmann–Grad scaling μ = ε⁻², the manuscript establishes weak convergence of the exactly centered empirical fluctuation fields for both the true flow and one fixed pasted flow. The interval [0,T] is a prescribed regular Boltzmann lifespan under the stated spatially summable Gaussian initial-data and classical-solution bounds. Convergence is in D([0,T], S′_β(R⁶)), with the generalized Skorokhod J₁ topology induced by the strong dual topology of Schwartz space. The limiting probability law is Radon and supported on strongly continuous paths. Its Schwartz-test finite-dimensional evaluations and covariance agree with the upstream Gaussian target.

The manuscript also proves quantitative retained cyclic-history and actual pasted-law increment-cumulant estimates. These are intermediate bounds; no quantitative rate for convergence of the fluctuation law or its covariance is asserted. The theorem does not claim true-flow high-moment convergence, tightness in a fixed negative-Sobolev path norm, or an enlarged uniqueness class for the formal distribution-valued stochastic equation.

## Imported inputs

The reference snapshot is [OpenAI, Hard-sphere fluctuations on the regular Boltzmann lifespan, 23 September 2026](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build), commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The imported package includes:

- The restarted capped dynamics and its common Gaussian Bol input envelopes.
- The actual marked component expansion, chronological merger coordinates, connected-diagram inversion, fresh-label factorials, and unweighted total-variation remainder.
- Arbitrary-power high-complexity and initial-tail bounds, and the physical initial-link gain.
- Normalized factorial-mass and particle-count moment bounds.
- The actual sharp unmarked cumulant bounds, Gaussian finite-dimensional convergence, and the Gaussian target’s continuous C₀-to-L² extension.
- A common-initial-data coupling under which the true and pasted paths differ anywhere in [0,T] with probability O(ε^(21/20)).

Exact theorem, lemma, and equation labels are supplied in manuscript §2. The audit checked these imported statements and their uses against the pinned source. It did not independently reprove the upstream positive-history estimates or the complete kinetic derivation. One fixed choice of the dynamical caps and slab count is used before choosing subsequent fixed observation lists, moment orders, or expansion accuracy.

## Correction made during review

The repeated-pair estimate originally extracted an elementary time gap from a Cauchy–Schwarz sum without explicitly fixing the schedule slot to which that gap belonged. The source was corrected to refine the exceptional skeleton by the earlier pair-contact slot and the first later endpoint-scattering slot.

There are at most a² ≤ n² such choices. Within each refined class, the contact times and the chosen elementary gap are common across the schedules, so the extraction and the ordered-simplex inverse-half-moment calculation are valid. The extra factor is polynomial in size and is absorbed by the existing summable majorant. The correction leaves the repeated-sector O(√ε) bound, the full O(√(ε(1+log(1/ε)))) cyclic bound, and the common fixed dynamics unchanged.

## Actual check coverage

The complete main source and all eight sections were read, including their assembly interfaces. The checks covered:

1. Gaussian geometry only before the first redundant contact: the erased normal coordinate for repeated pairs, forest-cut rank-one transfer, nonneighbor residual-time slope, and the truncated logarithmic integral.
2. Joint squared-flux summation over schedules, including all permitted later weights and nonlinear determined returns, zero extension of unrealizable branches, both factorial denominators, and all particle sizes.
3. Actual marked-hierarchy remainder inversion and factorial-to-ordinary cumulant normalization. Only bounded records are applied to the unweighted microscopic error.
4. Passive accepted-collision records, quotient-coordinate calendar shifts, virtual continuation across interfaces, physical-link localization, and the actual incidence-cumulant error budget.
5. Fourth-moment microscopic-window estimates, eighteenth-moment fine-grid comparisons, mesoscopic interpolation, and control between all grid points.
6. Post-collision right-continuous path conventions, fixed-time compatibility with incoming conventions, exact microscopic means, and uniform true/pasted path comparison without high-moment transfer.
7. Scalar tightness for every Schwartz test, Schwartz finite-dimensional identification, Hilbert-space realization of individual path laws, strong-dual measurability and Radon properties, countable Borel determination, extraction of weak subsequences, and strong continuity and uniqueness of the limit.

The strong-topology and path-Borel results were checked directly in [Jakubowski, On the Skorokhod topology (1986)](https://www.numdam.org/item/AIHPB_1986__22_3_263_0.pdf), especially §5.II, Proposition 5.3 and Theorem 5.5. The theorem is applied to all Schwartz projections, rather than only a countable dense test family.

## Version and reproducibility

Version 1, dated 7 October 2026, comprises the following nine TeX source files. Each SHA256 value below was checked against the frozen reviewed source and the independently rebuilt copy.

- `manuscript.tex`: `f081be42459cc888790621b3f56abd77724035f17e7ab1569daa7b8f2eeaa31f`
- `sections/01_model.tex`: `748784193418598e3d6ee3e0af50bcff359f313c6359a588509640c83c3a90e6`
- `sections/02_imports.tex`: `947c388dc6af1cc30c85e2621823370da699dc73f1b82829704537379af0ee0c`
- `sections/03_geometry.tex`: `619385a0f93a30def8f9ff27510b11acfcbde4ca28b0c53bbf1efabfb3da70c0`
- `sections/04_summation.tex`: `8c196f972d19b013b204e8cefb3d42b9a0a21215ce542dfea4266213a909e6d7`
- `sections/05_increments.tex`: `db2650174a51d059932fd97a00c311034db79b980c0ee9ba09c0edc7524cd069`
- `sections/06_microscopic.tex`: `9b2662b8146bc01932ee03f00ebe854dd96edbcc88dadef070b91ac7996ba2e0`
- `sections/07_functional.tex`: `73e0f5f97a6ea8968d3aedceba38bdc72c6c7a9bbb911b5c893f4a548e23a04f`
- `sections/08_tempered.tex`: `4c93f569c24cbeab34602d3f9ac7fb901bdb1fa70a102d483e6338869e013fd3`

The final PDF has 19 pages and 457,863 bytes. Its SHA256 is `bd5004c4ad2430cff1baf92f2f31903320263dbe95cb222d5d36c739b33f201f`. An independent rebuild produced a byte-identical PDF. The build log contained no LaTeX warnings, unresolved references, or overfull/underfull boxes. Static checks also found no missing or duplicate source labels.


The public-version wording changes were checked against the mathematically audited source. The exact diff consists only of three substitutions in the main file: the date line, the PDF subject, and the status sentence now identify a research draft, version 1. All eight mathematical section files remain byte-identical to the audited version. Every mathematical statement, proof, assumption, dependency, and scope limitation is preserved.

This technical verification is not external peer review or a publication-priority determination. Its conclusion applies to the identified source version and its explicit imported hypotheses.
