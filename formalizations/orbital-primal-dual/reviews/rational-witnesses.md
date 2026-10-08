# Independent semantic review: simultaneous rational primal/dual witnesses

Reviewed 8 October 2026. This is an internal AI-agent mathematical/source review, not external professional peer review or an independent clean-kernel replay.

Frozen files read in full:

- `/workspace/scratch/orbital-lean/RationalProjection.lean`: SHA256 `a987b38ac7be6dee66b12ce4de19fccb2372fde894c12ebe1d95a4156e75c30d`.
- `/workspace/scratch/orbital-lean/RationalDuality.lean`: SHA256 `fdaa402e60075f8e6f7d9a1fae213e6ed921d06a6cb0280b1f92e44dc08405a5`.

I additionally read actual definitions of Probability, Match, SignedBound, PairBound, UniformLawBound and dualScore; intervalDual_pairBound; and the actual exact_real_primal_dual statement and proof. The parent reports these files compiled. No substantive semantic gap found in the requested two modules.

## Finite rational projection

The statement is appropriately limited to a supplied finite collection of nonnegative reals. It does not assert a globally order-preserving projection R->Q (which would be false). A finite-dimensional rational span containing 1 is used, its actual coordinate inclusion is a point in an open cone of strict positive constraints, and rational density supplies another point in that cone. Extending the rational-linear functional off that span is legitimate and does not introduce additional sign assertions. Division by g(1)>0 fixes 1. Zero inputs are handled separately by linearity. Rational constants are then fixed automatically. Both empty supplied set and set containing zero/negative values are covered correctly.

## Simultaneous rationalization

The finite set includes all p_g, q_g and both dual inequality slacks. Its finite sign preservation proves the rationalized laws nonnegative and the rationalized interval endpoints ordered at every actual finite state. Normalization is preserved because f(sum p)=f(1)=1, not by approximation. Matching is preserved because all features are rational and f is Q-linear. The dual score calculation legitimately commutes f with rational feature multiplication, including the indicator 0/1. Primal attainment and width equality use the SAME f, so no independently rounded zero-gap quantities are silently equated.

The hypotheses of rationalize_pair_dual include an already-real zero-gap witness. This is an honest bridge lemma rather than the final theorem. In exact_rational_primal_dual the witness is produced by the separately proved exact_real_primal_dual, whose only arguments are the feature matrix and distinguished state: optimality is not passed as an assumption to that final theorem.

## Actual final scope

The resulting PairBound quantifies over ALL real probability laws with matching rational features; it is not restricted to rational laws. The rationalized dual interval provides that bound. Conversely, the old real optimum bounds the new rationalized primal pair. Combining the two directions proves the new rational value is numerically the same old real optimum C, rather than merely another feasible rational lower bound. This justifies 0<=C<=1 and the sharpness claim. The final UniformLawBound uses the actual total-variation ratio around the genuine uniform law and the proved signed/pair/uniform equivalence.

The distinguished state i and a Nonempty finite I are genuine requirements. Finite J may be empty: no feature/rank/nondegeneracy assumption is hidden. Rational features need not be positive. All inequality sign handling occurs on laws/slacks, not by falsely assuming arbitrary features or coefficients nonnegative.

This audit does NOT claim the complete group-action Theorem18 has been connected to these finite features, nor that the whole project has been independently replayed. Those are separate remaining scope checks.
