import GaussianIntrinsicInnerPerimeter

/-!
# Pairwise Lipschitz calibration of genuine simplicial Gaussian flux

The positive symmetric coefficients extracted from actual Gaussian winning
cells admit a sharp dual lower estimate for intrinsic cluster perimeter.
No multi-bubble isoperimetric inequality is assumed.

The finite graph lemma uses only symmetric flux coefficients.  Its application
to the Gaussian problem uses the actual winning-cell moments and erosion
perimeter bridge.  Equality occurs for equidistant score families with the
edge-normalized score calibration.
-/

open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

/-- The symmetric flux pairing is one half of the edgewise difference pairing. -/
theorem symmetric_flux_pairing (v q m : Fin k → Space d)
    (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j)) :
    (∑ i, ⟪q i,m i⟫) =
      (∑ i, ∑ j, w i j * ⟪q i-q j,v i-v j⟫) / 2 := by
  have hi (i j : Fin k) :
      ⟪q i-q j,v i-v j⟫ =
        ⟪q i,v i-v j⟫ + ⟪q j,v j-v i⟫ := by
    simp only [inner_sub_left]
    have hj : v j-v i = -(v i-v j) := by abel
    rw [hj,inner_neg_right]
    ring
  have he : (∑ i, ⟪q i,m i⟫) =
      ∑ i,∑ j,w i j*⟪q i,v i-v j⟫ := by
    simp only [hf,inner_sum,real_inner_smul_right]
  have hswap : (∑ i, ∑ j,w i j*⟪q j,v j-v i⟫) =
      ∑ i,∑ j,w i j*⟪q i,v i-v j⟫ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  rw [he]
  simp_rw [hi,mul_add,Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- Unit-diameter label calibrations control any symmetric nonnegative
flux perimeter.  No positivity of individual off-diagonal entries is needed. -/
theorem symmetric_flux_pairing_le_perimeter (v q m : Fin k → Space d)
    (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hs : ∀ i j, w i j = w j i)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j))
    (hq : ∀ i j, ‖q i - q j‖ ≤ 1) :
    (∑ i, ⟪q i,m i⟫) ≤ fluxPerimeter v w := by
  rw [symmetric_flux_pairing v q m w hs hf]
  have he (i j : Fin k) :
      w i j * ⟪q i-q j,v i-v j⟫ ≤ w i j * ‖v i-v j‖ := by
    calc
      _ ≤ w i j * (‖q i-q j‖*‖v i-v j‖) :=
        mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (hw i j)
      _ ≤ w i j * (1*‖v i-v j‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hq i j) (norm_nonneg (v i-v j))) (hw i j)
      _ = _ := by ring
  have hsum : (∑ i,∑ j,w i j*⟪q i-q j,v i-v j⟫) ≤
      ∑ i,∑ j,w i j*‖v i-v j‖ := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
  unfold fluxPerimeter
  linarith only [hsum]

/-- The dual lower estimate is exactly attained on equidistant score
families, with edge-normalized score directions. -/
theorem symmetric_flux_calibration_equality_for_equal_edges (v m : Fin k → Space d)
    (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i)
    (hf : ∀ i, m i = ∑ j, w i j • (v i - v j))
    (a : ℝ) (ha : 0 < a)
    (hedge : ∀ i j, i ≠ j → ‖v i - v j‖ = a) :
    (∑ i,⟪a⁻¹ • v i,m i⟫) = fluxPerimeter v w := by
  rw [symmetric_flux_pairing v (fun i => a⁻¹ • v i) m w hs hf]
  have he (i j : Fin k) :
      w i j * ⟪a⁻¹ • v i-a⁻¹ • v j,v i-v j⟫ =
        w i j * ‖v i-v j‖ := by
    by_cases hij : i=j
    · subst j
      simp
    · have hh : a⁻¹ * a^2 = a := by
        field_simp [ha.ne']
      calc
        _ = w i j * (a⁻¹ * ‖v i-v j‖^2) := by
          rw [← smul_sub,real_inner_smul_left,real_inner_self_eq_norm_sq]
        _ = w i j * (a⁻¹ * a^2) := by rw [hedge i j hij]
        _ = w i j * a := by rw [hh]
        _ = w i j * ‖v i-v j‖ := by rw [hedge i j hij]
  simp_rw [he]
  rfl

/-- Actual equal-mass full Gaussian simplex winning cells obey the
pairwise Lipschitz flux calibration unconditionally, in every dimension. -/
theorem actual_simplicial_flux_calibration
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (q : Fin (d+2) → Space (d+1))
    (hq : ∀ i j, ‖q i-q j‖ ≤ 1) :
    (∑ i,⟪q i,balancedMoment v i⟫) ≤
      (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2 := by
  obtain ⟨w,h0,hp,hs,hf,_⟩ := actual_balanced_flux_energy v hv
  have hw (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i=j
    · subst j
      rw [h0 i]
    · exact (hp i j hij).le
  have hraw (i : Fin (d+2)) :
      rawWinningMoment v (canonicalPrices v) i = ∑ j,w i j • (v i-v j) := hf i
  rw [actual_simplicial_cluster_inner_perimeter v _ hv w hraw]
  exact symmetric_flux_pairing_le_perimeter v q (balancedMoment v) w hw hs hf hq

/-- The genuine Gaussian intrinsic winning-cluster perimeter attains the
finite Lipschitz calibration at every equidistant full simplex. -/
theorem actual_equal_edges_flux_calibration_equality
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (a : ℝ) (ha : 0 < a)
    (hedge : ∀ i j, i ≠ j → ‖v i-v j‖ = a) :
    (∑ i,⟪a⁻¹ • v i,balancedMoment v i⟫) =
      (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2 := by
  obtain ⟨w,_,_,hs,hf,_⟩ := actual_balanced_flux_energy v hv
  have hraw (i : Fin (d+2)) :
      rawWinningMoment v (canonicalPrices v) i = ∑ j,w i j • (v i-v j) := hf i
  rw [actual_simplicial_cluster_inner_perimeter v _ hv w hraw]
  exact symmetric_flux_calibration_equality_for_equal_edges v (balancedMoment v)
    w hs hf a ha hedge

#print axioms symmetric_flux_pairing
#print axioms symmetric_flux_pairing_le_perimeter
#print axioms symmetric_flux_calibration_equality_for_equal_edges
#print axioms actual_simplicial_flux_calibration
#print axioms actual_equal_edges_flux_calibration_equality

end GaussianMeasureBridge
