# Hydrology research direction (2026-10-11)

## Candidate main problem
Can a low-dimensional storage state, constrained by exact water balance and monotone runoff response, remain calibrated under forcing distributions outside training support?

## Model class
For basin b and time t, let
\[
S_{t+1}=S_t+P_t-ET_t-Q_t,
\qquad Q_t=f_\theta(S_t,P_t,A_b),
\]
where S is latent effective storage, P precipitation, ET evapotranspiration, Q discharge, and A_b static basin attributes. Enforce nonnegativity, mass closure, and monotonicity in S and P. A cross-basin encoder maps A_b to parameters but the state transition is shared.

## Testable hypothesis
Compared with an unconstrained LSTM and a standard differentiable HBV baseline, the shared transition should retain better tail calibration and physical-state consistency under leave-one-climate-regime-out testing, especially for return periods beyond the training range.

## Potential mathematical result
Assume the learned transition F is L-Lipschitz in state and forcing, and the forcing perturbation at time t is δu_t. Then the state error satisfies
\[
|δS_T| \le L^T|δS_0|+\sum_{k=0}^{T-1}L^{T-1-k}|δu_k|.
\]
If Q=f(S,u) is K-Lipschitz, then
\[
|δQ_T|\le K\left(L^T|δS_0|+\sum_{k=0}^{T-1}L^{T-1-k}|δu_k|\right).
\]
This gives a falsifiable robustness certificate: estimate L,K on held-out trajectories and compare the certified bound with observed extreme-event error. The result is not a theorem about all hydrological systems; it is a conditional stability theorem for the proposed model class.

## Novelty target
The contribution must be mechanism-level: identify whether the learned state is an effective storage variable whose response is invariant across basins/climate regimes, not merely improve NSE. Required evidence: ablations of each physical constraint, tail-calibrated uncertainty, unseen-extreme stress tests, and independent checks against SWE/ET where available.
