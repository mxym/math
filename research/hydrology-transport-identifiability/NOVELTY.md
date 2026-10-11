# Literature audit and novelty boundary

Search completed 11 October 2026. This is a candidate theoretical/methodological
contribution, not a certified first discovery. The review included hydrological
equifinality, rainfall-runoff structural identifiability, differentiable model
parsimony, tracer-aided calibration, bilinear/compartmental similarity methods,
multiple-experiment identification, and observability-based experiment design.
It is not an exhaustive systematic review, and absence from these searches is
not evidence of historical priority.

## Why this problem was selected

Three directions were considered: (i) more expressive rainfall-runoff prediction,
(ii) autonomous extraction of process laws from existing observational records,
and (iii) rigorous conditions for distinguishing process mechanisms. Direction
(iii) offered a complete theorem-and-counterexample cycle with transparent tests.
No large-sample forecast benchmark or field discovery is represented as performed.

Two recent empirical papers sharpen the motivation without proving our results.
Poudel and Steinschneider (2026) compare static/dynamic differentiable models on
531 CAMELS-US basins and caution that dynamic parameters can reflect equifinality.
Pool et al. (2026) show that adding ET objectives can increase discharge uncertainty
in their calibration setting. Neither licenses the universal claim that added
observations are harmful; additional information never removes a true constraint,
but model mismatch, objectives and the admissible model class matter.

## Closest prior work and explicit nonclaims

| Prior work | Mechanism already present | What is NOT claimed here |
|---|---|---|
| Ho and Kalman (1966), DOI 10.1524/auto.1966.14.112.545 | Constructive state-space realization from input-output data | Invention of Hankel realization or minimal-realization similarity |
| Shin et al. (2015), DOI 10.1016/j.jhydrol.2014.11.040 | Structural-identifiability analysis for rainfall-runoff models | Discovery that hydrological parameters can be nonidentifiable |
| Yates, Evans and Chappell (2009), DOI 10.1016/j.automatica.2009.07.009 | Symmetry-based structural identifiability | Invention of symmetry/gauge analysis |
| Clarkson and Kupinski (2009), DOI 10.1137/080715226 | Similarity groups for compartmental ambiguity, normalized eigenvectors, positivity restrictions, spatial information | Novelty of positive compartment similarities, conservation-style normalization, or sensor information in themselves |
| Conrad, Hyman and Eisenberg (2026), DOI 10.1016/j.mbs.2026.109814 | Forcing functions can improve identifiability in a specified model class | A first theorem that environmental forcing can identify parameters; our flexible-class result does not contradict theirs |
| Miazza and Benettin (2026), DOI 10.5194/hess-30-1247-2026 | Tracer and water transport differ under time-variable conditions and environmental removal | Discovery that tracers do not all follow water identically |
| Bartos (2021), DOI 10.1029/2020WR029551 | Observability-based sensor placement for river contaminants | Invention of informative sensor/experiment design |

The particularly close Clarkson-Kupinski paper was checked in full-text HTML.
Its identifiability setting uses spatial support information in SPECT/PET. It
already contains substantial conceptual machinery underlying our argument. The
present paired-material diagonal-contrast construction is not a wholesale new
realization theory. Related multi-tracer pharmacokinetic literature further
limits any broad claim about inventing tracer-based identification.

## Candidate contribution, stated narrowly

The package supplies a single hydrological model-class treatment joining:

1. A maximal continuous physical counterexample interval with all-forcing water,
   total-storage, ET and ideal co-transport invariance, not just a numerical fit.
2. A complete local equivalence dimension for fixed observation/input anchors,
   and its reduction by static structure or common diagonal transport contrasts.
3. An explicit shared-baseline reconstruction of an unknown affine network from
   water and contrasting-material kernels, with conservation fixing the physical
   basis up to permutation; repeated contrasts leave precisely described blocks.
4. A finite-dwell variant avoiding response derivatives under a stated sufficient
   anti-aliasing bound, and a sensitivity calculation targeting water-invisible
   directions for controlled experiment design.

I did not find this exact combined formulation or this explicit witness in the
searched sources. That is a search result, NOT a priority finding. Theorems 1–3
and 5 may be regarded by systems-identification specialists as direct applications
or extensions of known realization theory. An independent comparison with that
literature is necessary before a paper can claim a genuinely novel theorem.
The candidate scientific value is the architecture/tracer distinction and its
operational consequences, not a new proof that equifinality exists.

## Primary sources consulted

- Poudel, S.; Steinschneider, S. (2026), *An argument for parsimony in differentiable
  hydrologic models*, HESS 30, 5173–5193. Published 14 August 2026.
  https://doi.org/10.5194/hess-30-5173-2026
- Pool, S.; Fowler, K.; Gardiya Weligamage, K.; Peel, M. (2026), *Multivariate
  calibration can increase simulated discharge uncertainty and model equifinality*,
  HESS 30, 2797–2815. Published 11 May 2026.
  https://doi.org/10.5194/hess-30-2797-2026
- Miazza, R.; Benettin, P. (2026), *Technical note: Transit times of reactive tracers
  under time-variable hydrologic conditions*, HESS 30, 1247–1260. Published 3 March 2026.
  https://doi.org/10.5194/hess-30-1247-2026
- Shin, M. J.; Guillaume, J. H. A.; Croke, B. F. W.; Jakeman, A. J. (2015),
  *A review of foundational methods for checking structural identifiability of
  models: Results for rainfall-runoff*, Journal of Hydrology.
  https://doi.org/10.1016/j.jhydrol.2014.11.040
- Ho, B. L.; Kalman, R. E. (1966), *Effective construction of linear state-variable
  models from input/output functions*, Regelungstechnik 14, 545–548.
  https://doi.org/10.1524/auto.1966.14.112.545
  Earlier conference record: https://ntrs.nasa.gov/citations/19660046794
- Yates, J. W. T.; Evans, N. D.; Chappell, M. J. (2009), *Structural identifiability
  analysis via symmetries of differential equations*, Automatica.
  https://doi.org/10.1016/j.automatica.2009.07.009
- Clarkson, E.; Kupinski, M. A. (2009), *Global Compartmental Pharmacokinetic Models
  for Spatiotemporal SPECT and PET Imaging*, SIAM Journal on Imaging Sciences 2, 203–225.
  https://doi.org/10.1137/080715226
  Full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC2905890/
- Conrad, J. R.; Hyman, J. M.; Eisenberg, M. C. (2026), *Examining the impact of
  forcing function inputs on structural identifiability*, Mathematical Biosciences,
  article 109814. Online 21 September 2026; earlier preprint dates from 2024.
  https://doi.org/10.1016/j.mbs.2026.109814
- Bartos (2021), *Observability-Based Sensor Placement Improves Contaminant Tracing
  in River Networks*, Water Resources Research.
  https://doi.org/10.1029/2020WR029551

No copyrighted full text, third-party data, or third-party source code is bundled.
