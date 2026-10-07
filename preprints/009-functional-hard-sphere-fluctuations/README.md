# Functional hard-sphere fluctuations on regular kinetic intervals

**Research manuscript 009, version 1, 7 October 2026.**

[19-page paper](v1/manuscript.pdf) · [Main source](v1/manuscript.tex) · [Complete source archive](v1/source.tar.gz) · [Build instructions](v1/README.md) · [Mathematical audit](v1/AUDIT.md) · [Artifact checks](v1/ARTIFACT_QA.md) · [Hashes](v1/SHA256SUMS)

## Precise result

For three-dimensional hard spheres in the Boltzmann–Grad scaling, the exactly centered true and one fixed pasted empirical fluctuation fields converge weakly on a prescribed regular Boltzmann interval. The path space is D([0,T], S′β(R⁶)), with the generalized Skorokhod J1 topology induced by the strong dual topology of Schwartz space. The limiting law is Radon and supported on strongly continuous paths; its finite-dimensional Schwartz evaluations are the existing Gaussian target.

The theorem uses the explicitly stated, pinned analytic history package and finite-dimensional limit in OpenAI’s [Hard-sphere fluctuations on the regular Boltzmann lifespan](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build). The initial density has the specified spatially summable Gaussian density/gradient bounds, and a classical Boltzmann solution with the stated Gaussian bounds is assumed on the given interval. This is not a proof of global regularity of the Boltzmann equation.

## New proof components and explicit inputs

The paper proves quantitative repeated-pair and nonneighbor first-recollision bounds, a squared-flux summation preserving label and time factorials, actual pasted-law increment estimates after microscopic remainder inversion, passive collision-count and calendar-shift localization, microscopic oscillation control, and two-grid tightness. It then verifies all-Schwartz estimates, Radon path laws, strong-dual topology and Borel determination, and exactly centered true/pasted path comparison.

Every new argument is included in the paper. The [dependency inventory](v1/DEPENDENCIES.md) and manuscript section 2 state the imported analytic estimates with exact source labels and distinguish them from new proofs. No private research note is a required theorem or build input. The outgoing right-continuous collision convention is justified explicitly.

The intermediate cyclic bound has scale sqrt(ε(1+log(1/ε))), with sqrt(ε) in the repeated-pair sector. These are proof estimates, not a claimed quantitative rate of convergence of the fluctuation law or covariance. The paper does not infer high-moment convergence for the true flow, tightness in a fixed negative-Sobolev path norm, or a broader distribution-valued SPDE uniqueness theorem.

## Earlier work and verification status

Gaussian-process limits for nonequilibrium hard spheres at short times were established by [Bodineau–Gallagher–Saint-Raymond–Simonella, Annals of Mathematics (2023)](https://annals.math.princeton.edu/2023/198-3/p03); their [equilibrium long-time result](https://arxiv.org/abs/2201.04514) concerns a different regime. The pinned OpenAI source supplies the substantial regular-lifespan finite-dimensional and analytic framework used here. The present paper addresses functional convergence within that declared framework; it does not claim to originate fluctuation theory.

Fresh full-assembly and component audits checked the new proofs and their junctions. One repeated-pair schedule-slot extraction gap was repaired before release and rechecked. All 19 pages, final source identities, pinned labels, archive completeness and clean rebuilding were checked. These are model-assisted mathematical reviews, not external human peer review or proof-assistant verification, and not independent reproving of every imported kinetic theorem. No priority or journal-tier claim is made.

## Additive restricted mean and collisional-stress supplement

The [full-density virial/stress supplement](../../notes/full-density-virial-stress/README.md), [12-page PDF](../../notes/full-density-virial-stress/manuscript.pdf), [complete TeX proof](../../notes/full-density-virial-stress/manuscript.tex), and [editable source archive](../../notes/full-density-virial-stress/source.tar.gz) prove first-order mean corrections for x·v and |x|² at full unit amplitude, together with a local momentum-balance defect limit given by the classical collisional-stress tensor. The assumptions include smooth compact initial position and velocity support, a prescribed regular Boltzmann interval, and the pinned operational history package H1--H6. The speed-weighted passive-record extension is proved in the supplement.

This is a restricted mean result. It neither proves convergence of the entire one-particle mean correction nor extends manuscript 009's fluctuation theorem to the unbounded spatial tests. It imports no fluctuation conclusion from 009. The [public source map](../../notes/full-density-virial-stress/DEPENDENCIES.md), [mathematical audit](../../notes/full-density-virial-stress/MATHEMATICAL_AUDIT.md), and [editorial/source identity record](../../notes/full-density-virial-stress/EDITORIAL_CHANGES.md) state the precise dependency and verification boundaries. Historical 009 v1 files are unchanged; no formal verification, external peer review or priority claim is made.
