import EqualityCompletionFull
import AbsolutePencil
import Mathlib.Analysis.Complex.Basic

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

/-- Strictly inside the centered sharp complex coefficient disk,
    a nonzero-row extremizer must be balanced rank one.
    The sparse monomial class can attain the boundary, but
    cannot attain the strict interior coefficient. -/
theorem strict_pencil_saturation_forces_flatRankOne
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlam : ‖lam‖ < detWeight)
    (ha : 0 < rowSq a0 a1 a2)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq :
      ComplexPencilLink.sq
        (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
         lam * determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      (4/3:ℝ) * rowSq a0 a1 a2 *
        rowSq b0 b1 b2 * rowSq c0 c1 c2) :
    flatRankOne a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  let P := permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  let D := determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  let R : ℝ := ComplexPencilFull.rho *
      rowNorm a0 a1 a2 * rowNorm b0 b1 b2 *
        rowNorm c0 c1 c2
  let N : ℝ := ‖P+lam*D‖
  let L : ℝ := ‖P‖+detWeight*‖D‖
  have hRpos : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (le_of_lt ComplexPencilFull.rho_pos)
          (rowNorm_nonneg a0 a1 a2))
        (rowNorm_nonneg b0 b1 b2))
      (rowNorm_nonneg c0 c1 c2)
  have hNpos : 0 ≤ N := norm_nonneg _
  have hR2 : R^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    dsimp [R]
    rw [mul_pow,mul_pow,mul_pow,
      ComplexPencilFull.rho_sq,
      rowNorm_sq a0 a1 a2,
      rowNorm_sq b0 b1 b2,
      rowNorm_sq c0 c1 c2]
  have hN2 : N^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    dsimp [N]
    rw [ComplexPencilFull.norm_sq_equals_sq]
    exact heq
  have hNR : N=R := by nlinarith [hN2,hR2]
  have hTri : N ≤ ‖P‖+‖lam‖*‖D‖ := by
    dsimp [N]
    calc
      _ ≤ ‖P‖+‖lam*D‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul]
  have hAbs : L ≤ R := by
    simpa [P,D,L,R] using
      sharp_absolute_value a0 a1 a2 b0 b1 b2 c0 c1 c2
  have hUpper : ‖P‖+‖lam‖*‖D‖ ≤L := by
    dsimp [L]
    have hmult :=
      mul_le_mul_of_nonneg_right (le_of_lt hlam) (norm_nonneg D)
    linarith
  have hD : D=0 := by
    have hdif : 0 < detWeight-‖lam‖ := sub_pos.mpr hlam
    have hzero : ‖D‖=0 := by
      have hh : (detWeight-‖lam‖)*‖D‖ ≤0 := by
        dsimp [L] at hAbs
        linarith [hTri,hNR,hAbs]
      nlinarith [norm_nonneg D]
    exact norm_eq_zero.mp hzero
  have hAbsSat :
      (‖P‖+detWeight*‖D‖)^2 =
        (4/3:ℝ)*rowSq a0 a1 a2*
          rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    have hEqL : L=R := by linarith [hNR,hTri,hUpper,hAbs]
    change L^2 = _
    rw [hEqL, hR2]
  have hcases := (absolute_equality_iff_full
      a0 a1 a2 b0 b1 b2 c0 c1 c2).mp hAbsSat
  rcases hcases with hz | hz | hz | hr | hm
  · rcases hz with ⟨rfl,rfl,rfl⟩
    simp [rowSq,ComplexPencilLink.sq] at ha
  · rcases hz with ⟨rfl,rfl,rfl⟩
    simp [rowSq,ComplexPencilLink.sq] at hb
  · rcases hz with ⟨rfl,rfl,rfl⟩
    simp [rowSq,ComplexPencilLink.sq] at hc
  · exact hr
  · have hdet : D≠0 := by
      rcases hm with ⟨hs0,hs1,hs2,hp⟩
      rcases sparse_rows_det_sign
        a0 a1 a2 b0 b1 b2 c0 c1 c2
          hs0 hs1 hs2 with hh | hh
      · intro hz
        apply hp
        simpa only [D] using (hh.symm.trans hz)
      · intro hz
        apply hp
        have := hh.symm.trans hz
        simpa only [neg_eq_zero] using this
    exact False.elim (hdet hD)

#print axioms ComplexPencilEquality.strict_pencil_saturation_forces_flatRankOne

end
end ComplexPencilEquality
