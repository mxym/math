# The cost is already present for an unknown support with a known spectrum

Author addendum v2, 16 October 2026. Same resource model and notation as PAPER-v2.md. Ordinary written proof, pending independent read. No Lean or external peer-review claim.

## 1. Flat rank-s orbits attain the same all-target minimax law

Let F_(flat,s)={W P_s W*/s: W in U(D)}, where the nonzero spectrum 1/s is completely known and only its support is unknown. Let G_C^(flat)(k,K;s) be the common-protocol minimax fidelity over this orbit. For fixed m<=n and 1<=s<D,

    sup_(K>=1 integer)
      |G_C^(flat)(k,K;s)/min(1,m^k/K,sqrt(D^k/r_(k,s))/K)-1| ->0.

Indeed the common support is S_(k,s), and the same deterministic LO subspace code serves every member of the orbit. Its Haar average is exactly Omega_(k,s). The upper proof uses only this orbit and therefore applies without enlarging the uncertainty to other spectra. Thus the lower and upper bounds in PAPER-v2 (6.3) apply unchanged.

This makes the distinction from spectrum estimation precise: the sharp finite-block loss persists when the complete spectrum is known. The result for the entire rank-budget class follows from the same two inequalities, with a larger adversarial input class.

At n<=ms, put C0=(1/2)log(D/s), g=s(D-s), C=C_(D,s). For the leading-capacity target K_k=ceil(exp(k C0)),

    G_C^(flat)(k,K_k;s) ~ C^(-1/2) k^(-g/2).

At n>ms, the local-cap target K=m^k is exactly feasible for all sufficiently large k. These are distinct regimes even at the boundary n=ms.

## 2. The zero-error logarithmic loss holds for every known positive rank-s spectrum

Let p_1,...,p_s>0 sum to one, pad by zeros to dimension D, and let F_p={W diag(p) W*: W in U(D)}. The nonzero values can be arbitrary and completely known. The common support of {rho^{tensor k}:rho in F_p} is still exactly S_(k,s).

To prove this, the Haar average has on block lambda the scalar

    s_lambda(p)/(u_lambda(D))

with multiplicity u_lambda(D)v_lambda. It is zero for more than s rows and strictly positive for at most s rows, because every Schur polynomial in positive s variables is a sum of nonnegative monomials and has at least one positive monomial. Thus its support is S_(k,s), independently of the positive eigenvalue values. The trace is one by the Schur--Weyl identity sum v_lambda s_lambda(p)=1.

If a common protocol has fidelity one on every member of F_p, its effective fidelity operator is the identity on this support, by the same positive-average argument as PAPER-v2 (6.6). Hence K<=a and K^2 r_(k,s)<=N. The common LO code supplies the matching floor packing. Consequently all zero-error conclusions in (6.7)--(6.8), including the complete constant term and the n=ms boundary, hold for each individual known positive rank-s spectrum with unknown eigenbasis.

This does not imply the fixed-error minimax law of Section 1 for a nonuniform p. The corresponding average is no longer Omega_(k,s), and its collision moment is not replaced by that of a flat rank-s state. Nonuniform states can have a larger faithful first-order capacity; it is strictly larger than that of the flat rank-s state in the entropy-limited regime n<ms. When the local cap already binds, both capacities can equal log m. The zero-error rate is determined by rank. Extending the flat-orbit fixed-error claim by continuity would be false.

## 3. Geometric interpretation

Rank-s support projectors form the complex Grassmannian, whose real dimension is 2s(D-s)=2g. In the entropy-limited and boundary regimes, the universal exact target loses (g/2)log k relative to its first-order logarithmic size for every fixed positive rank-s spectrum; the same fixed-error correction has been established here for the flat-orbit and rank-budget families only. Thus the coefficient is one quarter of this real support-manifold dimension. The operational coefficient comes from the actual common support rank and the collision moment of an adversarial average, not from counting parameters alone.

The elementary encoding implication of universal compression is credited in PAPER-v2. This addendum asserts the stated extraction laws under the explicit global-unitary resource, not a new theorem about ordinary LOCC distillation or unrestricted quantum compression.
