# Hydrology storage-invariance research (2026-10-11)

Status: exploratory mathematical note. No real-catchment experiment, new hydrological law, novelty claim, or release. The correction below supersedes the earlier stability formulas.

## Research question and model scope

Can physically constrained state models identify transferable rainfall-runoff mechanisms, rather than merely fit discharge? Extreme-event calibration is a hypothesis to test, not a consequence of water balance.

For a closed, snow-free lumped basin in consistent water-depth units per time step, use
S_{t+1}=S_t+P_t-E_t-Q_t.
Require S,P,E,Q >= 0 and E_t+Q_t <= S_t+P_t.
This omits abstraction, groundwater exchange, snow and routing; those require explicit additional states/fluxes. Monotonicity is a model assumption, not a universal hydrological law.

## Correction: standard perturbation lemma

Let two trajectories follow the same transition F and observation map h. Suppose on a common forward-invariant domain, uniformly in admissible inputs,
||F(s,u)-F(s',u')|| <= a||s-s'|| + b||u-u'||,
||h(s,u)-h(s',u')|| <= c||s-s'|| + d||u-u'||,
with nonnegative constants a,b,c,d. Write e_t=||s_t-s'_t|| and v_t=||u_t-u'_t||. Then
e_T <= a^T e_0 + b sum_{k=0}^{T-1} a^{T-1-k} v_k,
||Q_T-Q'_T|| <= c e_T + d v_T.
Proof: apply the first assumption at each step and induct on T; apply the second assumption at T. Empty sums are zero.

The original note omitted the forcing sensitivity coefficient b and the instantaneous output term d v_T. A joint L-Lipschitz assumption under the sum norm permits a=b=L, not b=1 in general. With bounded model discrepancy r_t, add sum a^{T-1-k} r_k. This compares model trajectories; it does not bound error against nature unless discrepancy is also bounded.

Finite sampled slopes on held-out trajectories do not certify global Lipschitz constants, nor should test data determine constraints. Constants need an analytic architecture-level proof or a rigorous domain enclosure. If a<1 and v_t<=epsilon, then e_T <= a^T e_0 + b epsilon (1-a^T)/(1-a). For a=1 the bound is e_0+bT epsilon. Contractivity is sufficient for a uniform bounded-input bound, not necessary for every useful finite-horizon bound.

This elementary induction is background mathematics, not a research contribution. It proves neither identifiability nor distribution-shift tail calibration.

## Exact counterexample: conservation and contraction do not identify extrapolation

Take E=0, available water x=S+P>=0, and two release functions:
q_A(x)=x/2,
q_B(x)=x/2 for x<=1, and 3x/4-1/4 for x>1.
Set S_next=x-q(x).

Both have nonnegative discharge and storage, exact mass balance, continuous monotone discharge and monotone storage maps. The storage map is globally 1/2-Lipschitz: its slopes are 1/2 for A, and 1/2 or 1/4 for B. Hence both are contractive in storage under identical forcing.

For identical initial states and any forcing trajectory with all available-water values at most 1, the states and discharges agree exactly by induction. Starting at S=0 with P=3, however, A releases 3/2 whereas B releases 2. Any prediction based solely on the identical low-range observations must have absolute error at least 1/4 in one of these two admissible worlds, by the triangle inequality. No claim of historical novelty is made for this elementary counterexample.

Thus conservation, monotonicity and even global contraction do not by themselves determine unseen-event discharge. Adding shared cross-basin parameterization does not remove this example if all observed basins remain within the same low-range domain. A deterministic stability estimate cannot supply a probabilistic tail-calibration guarantee.

## Revised experimental direction

Target identifiable, externally testable mechanisms and report an admissible prediction range where extrapolation is not identifiable. Compare physical-model, differentiable-HBV and data-driven baselines using identical forcing, training periods and budgets. Separate:
- simulation with observed meteorological inputs from operational forecasting;
- sensitivity to forcing perturbations from structural/model discrepancy;
- time-held-out, basin-held-out and climate-regime-held-out evaluations;
- flood peaks, volume and timing from average NSE, and empirical coverage from certified guarantees.

Freeze preprocessing, splits and hyperparameters before final tests; retain extreme events intact across split boundaries and account for temporal dependence. Independent ET/storage/snow observations may constrain mechanisms, but uncertainty in these observations must be included. A real-data benchmark has not yet been downloaded or run.

## Literature anchor

Song et al., Physics-Informed, Differentiable Hydrologic Models for Capturing Unseen Extreme Events (2026):
https://agupubs.onlinelibrary.wiley.com/doi/10.1029/2025WR040414
This motivates unseen-event evaluation; it does not establish novelty or guarantees for this proposal.


## Prior-art screen and next falsifiable target

Identifiability is established hydrological research, not a newly discovered problem. Relevant primary studies include:
- Sorooshian and Gupta (1985), The Analysis of Structural Identifiability: Theory and Application to Conceptual Rainfall-Runoff Models: https://agupubs.onlinelibrary.wiley.com/doi/10.1029/WR021i004p00487
- Schoups et al. (2008), Model complexity control for hydrologic prediction: https://agupubs.onlinelibrary.wiley.com/doi/10.1029/2008WR006836
- Khatami et al. (2019), Equifinality and Flux Mapping: https://doi.org/10.1029/2018WR023750
- Spieler et al. (2020), Automatic Model Structure Identification for Conceptual Hydrologic Models: https://doi.org/10.1029/2019WR027009

These records were screened for positioning; a full-text novelty review remains required before a publishable contribution claim.

### Sharp one-step envelope in a restricted scalar class

Suppose available water x is known, q(0)=0, and for x>y,
ell(x-y) <= q(x)-q(y) <= u(x-y), with 0<=ell<=u<=1.
An exact anchor q(b)=r, with b>=0 and ell b<=r<=u b, implies for x>=b:
r+ell(x-b) <= q(x) <= r+u(x-b).

Proof: substitute y=b in the increment constraint. Both endpoints are attainable by retaining any admissible law below b and extending it linearly above b with slope ell or u. The extension preserves the increment constraint across b by addition. Since q(0)=0 and slopes lie in [0,1], positivity and q(x)<=x hold. The interval width is (u-ell)(x-b), and any deterministic estimator from the anchor has worst-case absolute error at least half that width; the midpoint attains that minimax error.

This is an elementary shape-constrained interpolation observation, not claimed novel. It exhibits exactly what new high-storage observations can reduce: the unobserved distance beyond the last anchor. It cannot be applied directly to latent storage without bounding the storage uncertainty, and marginal envelopes propagated over multiple steps need not be jointly attainable by a single static release law.

A more substantive target is joint multi-step identification with shared release laws, uncertain storage and noisy independent flux measurements. A credible result would require sharp attainable bounds, an efficient reproducible algorithm, and out-of-sample catchment evidence showing which measurements actually tighten those bounds. If existing shape-constrained identification methods already cover this scope, narrow or replace the target rather than relabel them.
