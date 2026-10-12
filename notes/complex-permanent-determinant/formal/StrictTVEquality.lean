import PermutationTVNative
import EqualityTVStrict

namespace ComplexPencilProbability
open ComplexPencilTensor
open ComplexPencilReal
open ComplexPencilMain
open ComplexPencilEquality
open ComplexPencilAbsolute
open ComplexPencilFull
noncomputable section

theorem normalizedEnergy_eq_rowSq (a0 a1 a2 : ℂ) :
    normalizedEnergy (![a0,a1,a2]) =
      rowSq a0 a1 a2 / 3 := by
  simp [normalizedEnergy,rowSq,
    ComplexPencilLink.sq,Complex.normSq_apply,pow_two]

/-- At strictly subcritical total-variation distance, all
    nonzero-row complex L² extremizers are balanced rank-one.
    This proves the strict refinement stated after Corollary 4. -/
theorem strictTV_equality_forces_flatRankOne
    (p : Fin 6 → ℝ) (hm : uniformMarginals p)
    (hstrict : parityTV p < tvThreshold)
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (ha : 0 < rowSq a0 a1 a2)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq :
      Complex.normSq
        (oneColumnMoment p
          (![a0,a1,a2]) (![b0,b1,b2]) (![c0,c1,c2])) =
      normalizedEnergy (![a0,a1,a2]) *
      normalizedEnergy (![b0,b1,b2]) *
      normalizedEnergy (![c0,c1,c2])) :
    flatRankOne a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  obtain ⟨t,rfl⟩ := (uniformMarginals_iff_parity p).mp hm
  have ht : ‖((6*t:ℝ):ℂ)‖ < detWeight := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    rw [parityTV_weight] at hstrict
    unfold tvThreshold at hstrict
    have hmult : |6*t|=6*|t| := by
      rw [abs_mul]
      norm_num
    rw [hmult]
    linarith
  have heq2 := heq
  rw [moment_weight_eq_law,law_normSq_eq] at heq2
  change
    Complex.normSq
      ((rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2).permanent +
       ((6*t:ℝ):ℂ) *
       (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2).det) / 36 =
      normalizedEnergy (![a0,a1,a2]) *
      normalizedEnergy (![b0,b1,b2]) *
      normalizedEnergy (![c0,c1,c2]) at heq2
  rw [permanent_row_expansion,det_row_expansion,
    ComplexPencilFull.normSq_eq_sq] at heq2
  have hrow0 : normalizedEnergy (![a0,a1,a2]) =
      rowSq a0 a1 a2/3 := normalizedEnergy_eq_rowSq a0 a1 a2
  have hrow1 : normalizedEnergy (![b0,b1,b2]) =
      rowSq b0 b1 b2/3 := normalizedEnergy_eq_rowSq b0 b1 b2
  have hrow2 : normalizedEnergy (![c0,c1,c2]) =
      rowSq c0 c1 c2/3 := normalizedEnergy_eq_rowSq c0 c1 c2
  rw [hrow0,hrow1,hrow2] at heq2
  have hsq :
      ComplexPencilLink.sq
        (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
         ((6*t:ℝ):ℂ) *
            determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    nlinarith [heq2]
  exact strict_pencil_saturation_forces_flatRankOne
     ((6*t:ℝ):ℂ) a0 a1 a2 b0 b1 b2 c0 c1 c2
     ht ha hb hc hsq

#print axioms ComplexPencilProbability.strictTV_equality_forces_flatRankOne

end
end ComplexPencilProbability
