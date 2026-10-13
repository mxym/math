import GaussianCovarianceDifferential
import GaussianGramMomentTransport

/-! Uniqueness and Gram invariance of actual simplicial Gaussian flux. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

theorem symmetric_flux_unique
    (v m : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (w z : Fin (d+2) → Fin (d+2) → ℝ)
    (hwd : ∀ i, w i i = 0) (hzd : ∀ i, z i i = 0)
    (hws : ∀ i j, w i j = w j i) (hzs : ∀ i j, z i j = z j i)
    (hw : ∀ i, m i = ∑ j, w i j • (v i-v j))
    (hz : ∀ i, m i = ∑ j, z i j • (v i-v j)) : w = z := by
  obtain ⟨B,hB⟩ := simplicial_normal_basis v hv
  have hb (q : Fin (d+1)) : w 0 q.succ = z 0 q.succ :=
    (normal_basis_flux_base v m w B hB hw q).symm.trans
      (normal_basis_flux_base v m z B hB hz q)
  funext i j
  refine Fin.cases ?_ (fun p => ?_) i
  · exact Fin.cases (by rw [hwd,hzd]) hb j
  · refine Fin.cases ?_ (fun q => ?_) j
    · rw [hws, hzs]; exact hb p
    · by_cases hpq : p = q
      · subst q; rw [hwd,hzd]
      · exact (normal_basis_flux_offdiagonal v m w B hB hw p q hpq).symm.trans
          (normal_basis_flux_offdiagonal v m z B hB hz p q hpq)

lemma sum_scores_zero_of_centered_gram {e k : ℕ} (v : Fin k → Space e)
    (hz : ∀ i, (∑ j, scoreGram v i j) = 0) : ∑ i, v i = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [sum_inner]
  simp only [inner_sum]
  change (∑ i, ∑ j, scoreGram v i j) = 0
  simp only [hz, Finset.sum_const_zero]

/-- Actual balanced moments determine symmetric flux under Gram transport. -/
theorem balanced_flux_eq_of_gram_eq
    (v u : Fin (d+2) → Space (d+1))
    (hv : AffineIndependent ℝ v) (hu : AffineIndependent ℝ u)
    (hzv : ∑ i, v i = 0) (hzu : ∑ i, u i = 0)
    (hg : scoreGram v = scoreGram u)
    (w z : Fin (d+2) → Fin (d+2) → ℝ)
    (hwd : ∀ i, w i i = 0) (hzd : ∀ i, z i i = 0)
    (hws : ∀ i j, w i j = w j i) (hzs : ∀ i j, z i j = z j i)
    (hw : ∀ i, balancedMoment v i = ∑ j, w i j • (v i-v j))
    (hz : ∀ i, balancedMoment u i = ∑ j, z i j • (u i-u j)) : w = z := by
  obtain ⟨T,hT,hM⟩ := balancedMoment_gram_embedding v u hv hzv hzu hg
  have hwu (i : Fin (d+2)) : balancedMoment u i = ∑ j, w i j • (u i-u j) := by
    rw [← hM i, hw i, map_sum]
    simp only [map_smul, map_sub, hT]
  exact symmetric_flux_unique u (balancedMoment u) hu w z hwd hzd hws hzs hwu hz

end GaussianFour
