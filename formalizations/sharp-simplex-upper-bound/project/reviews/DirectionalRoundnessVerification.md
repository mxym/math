# Actual normalized directional roundness

Frozen new source: `Entry005/ActualNormalizedDirectionalRoundness.lean`, SHA256 `977e171b7893c632dfb8560c94f55cf3a1f117a2c7fe98d558538a363864cd9b`.

Five public proofs compile with Lean 4.34.1 and `-DautoImplicit=false`, with zero warnings. All five kernel axiom sets are only `propext`, `Classical.choice`, and `Quot.sound`. The external literal same-law check also compiles with the same standard axiom set. Reproduce with `python3 RunVerification.py`; `LeanPath.txt` records the effective read-only complete cache path. Only this lane's new source and output were written. No original definitions, dependency sources or shared cache outputs were modified.

The final raw-coordinate interface is:

```lean
normalized_convex_body_cone_raw_directional_roundness
  {d : ℕ} (hd : 2 ≤ d) (K : ConvexBody (Space d))
  (hb : closedBall 0 1 ⊆ K)
  (hbound : (K : Set (Space d)) ⊆ closedBall 0 (R0 d))
  (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
  (hbrightness : ∀ u : Space d, ‖u‖ = 1 →
    negativeIntegral ν (fun x => dotProduct (fun j => u j) x) =
      projectionVolumeSet (K : Set (Space d)) u /
        ((d : ℝ) * (volume (K : Set (Space d))).toReal)) :
  ∀ u : Fin d → ℝ, ‖WithLp.toLp 2 u‖ = 1 →
    2 * b d ≤ negativeIntegral ν (fun x => dotProduct u x)
```

The Euclidean-direction wrapper has the same inputs and concludes the inequality for every unit `u : Space d`. The probability measure `ν` is retained identically; no measure, subsequence, anchors or assignment is selected.

The proof derives both geometric volume bounds from the actual body inclusions. `euclidean_unit_ball_cube (d-1)` gives the actual unit projection-ball volume at least `(2/(d-1))^(d-1)`, which is at least `(2/d)^(d-1)`. `normalized_body_brightness_lower` follows from actual projected-set monotonicity and the actual closed-ball projection formula; it transfers this lower bound to `projectionVolumeSet K u`. `bounded_body_volume_le_cube` gives actual `volume(K).toReal ≤ (2*R0 d)^d`, while actual compactness and unit-ball containment give positive volume and positive normalization.

Exact power cancellation gives

`(2/d)^(d-1) / [d*(2*R0 d)^d] = 2*b d`,

with the unchanged original definitions `R0 d = d*(d+1)` and `b d = 1/[4*(d*R0 d)^d]`. This identity, not an asymptotic estimate or altered constant, is proved in `original_roundness_cube_coefficient`. Monotonicity of division then yields the actual brightness lower bound, and the supplied actual brightness identity transfers it to the same law's negative directional integral.

`LiteralSameLawCheck.lean` expands `b`, `R0`, the negative-part integral `∫ max (-(Σ_j u_j*x_j)) 0 dν`, and the literal orthogonal projected-set volume. It retains the same supplied measure `ν`, with no volume/projection lower bound, roundness, integrability, moment, covariance or desired conclusion among its premises. The only analytic law input is the already available exact brightness identity.

This leaf closes actual normalized directional roundness. It proves no finite Minkowski inequality, finite pyramid facet computation, new B representation, or complete sharp Main. There is no blocker for this leaf.

Inspected dependency-source hashes:

- `ProjectionScaleAssembly.lean`: `dac46ff812246c218a2d6d12499f7a57fce528e5c5e8e4e870255a55b531157c`.
- `Constants.lean`: `b3cdc026d3b5be2f495e8613bd98f36408b6ece56811adc1b562994fc447425e`.
- `BallVolume.lean`: `dd55e65e1dc1bf010af5b3e3ee2183e447c4b5970a1bb3f5d9866414d650f609`.
- `ProjectionVolumeSqueeze.lean`: `1d6870ac82787fc360ea1d0344e50b33745e961676626f99b427de130047262e`.
