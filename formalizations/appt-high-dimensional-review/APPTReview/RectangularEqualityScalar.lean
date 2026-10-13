import APPTReview.RectangularMaximum
import APPTReview.UniqueCutReduction

open scoped BigOperators
namespace APPTReview

/-- A shortened-support crossing is strictly suboptimal when the uniform
endpoint is below the optimum. Both denominator signs are retained. -/
theorem cutEdgePurity_lt_of_short (L h i s m C : ℝ)
    (hL : 0 < L) (hh : 0 < h) (hi : 0 ≤ i) (hroom : h+i ≤ L)
    (hs : 0 ≤ s) (hsm : s < m) (hm : 0 < m)
    (hc : 1/L < C) (hf : cutEdgePurity L h i m ≤ C) :
    cutEdgePurity L h i s < C := by
  let d := h*L+(h+i)*s
  let e := h*L+(h+i)*m
  have hd : 0 < d := by dsimp [d]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hx : 0 ≤ s/d := div_nonneg hs hd.le
  have hy : 0 < m/e := div_pos hm he
  have hxy : s/d < m/e := by
    apply (div_lt_div_iff₀ hd he).2
    have ht := mul_pos (mul_pos hh hL) (sub_pos.mpr hsm)
    dsimp [d,e]
    nlinarith
  have ha : 0 ≤ i*(L-h-i)/L :=
    div_nonneg (mul_nonneg hi (by linarith)) hL.le
  rw [cutEdgePurity_quadratic L h i m (ne_of_gt hL) (ne_of_gt he)] at hf
  have ht := quadratic_lt_strict_endpoint (i*(L-h-i)/L) (-(h/L)) (1/L)
    (s/d) (m/e) C ha hx hxy hy hc (by convert hf using 1 <;> dsimp [e] <;> ring)
  rw [cutEdgePurity_quadratic L h i s (ne_of_gt hL) (ne_of_gt hd)]
  convert ht using 1 <;> dsimp [d] <;> ring

theorem cutEdge_middle_scaled {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (k : ℕ) :
    cutEdgePurity ((m:ℝ)*n-m) ((m:ℝ)*((m:ℝ)-1)/2) (k:ℝ) m=
      plateauScaledPurity m n k/((m:ℝ)*n) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnP : (0:ℝ) < n := by exact_mod_cast hn
  have hmP : (0:ℝ) < m := by linarith
  have hD : (0:ℝ) < (m:ℝ)*n := mul_pos hmP hnP
  have hZ : (m:ℝ)*n*((m:ℝ)-1)+2*(k:ℝ)≠0 := by
    have hp : (0:ℝ) < (m:ℝ)-1 := by linarith
    positivity
  rw [cutEdge_middle_identity _ _ _ (ne_of_gt hmP) hZ]
  unfold plateauScaledPurity plateauDenominator
  field_simp

/-- Equality in a full-support middle crossing fixes its integer rank uniquely. -/
theorem cutEdge_middle_eq_rounded_iff {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (k : ℕ) :
    cutEdgePurity ((m:ℝ)*n-m) ((m:ℝ)*((m:ℝ)-1)/2) (k:ℝ) m=
      roundedPlateauPurity m n ↔ k=((m-1)*n+1)/2 := by
  rw [cutEdge_middle_scaled hm hn k]
  unfold roundedPlateauPurity
  have hmP : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnP : (0:ℝ) < n := by exact_mod_cast hn
  have hd : (m:ℝ)*n≠0 := ne_of_gt (mul_pos hmP hnP)
  constructor
  · intro he
    have hs := congrArg (fun x : ℝ => x*((m:ℝ)*n)) he
    simp only [div_mul_cancel₀ _ hd] at hs
    exact (plateauScaledPurity_ceiling_unique hm hn k).2.mp hs
  · intro hk
    subst k
    rfl

end APPTReview
