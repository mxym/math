import APPTReview.LacunaryProbability

open scoped BigOperators NNReal ENNReal
open MeasureTheory
namespace APPTReview

/-- Without factor-two separation the exact-sum graph can be a triangle. -/
theorem nonlacunary_triangle_not_colorable :
    ¬∃ c : ℝ → Bool, ∀ x y : ℝ, 0≤x → 0≤y → x≠y →
      x+y∈([3/5,1/2,2/5]:List ℝ) → c x≠c y := by
  rintro ⟨c,hc⟩
  have hab := hc (7/20) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hac := hc (7/20) (3/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbc := hc (1/4) (3/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  cases h1 : c (7/20) <;> cases h2 : c (1/4) <;> cases h3 : c (3/20) <;> simp_all

theorem separated_three_scales : LacunaryScales ([1,1/3,1/9]:List ℝ) := by
  norm_num [LacunaryScales,List.pairwise_cons]

/-- A real probability measure concentrated on a loop retains full product mass. -/
theorem loop_dirac_line_mass :
    ((Measure.dirac (1:ℝ≥0)).prod (Measure.dirac (1:ℝ≥0))).real (scaleLine 2)=1 := by
  rw [Measure.dirac_prod_dirac]
  norm_num [Measure.real,Measure.dirac_apply',scaleLine]

/-- Omitting the loop contribution makes the claimed energy bound false. -/
theorem loop_term_cannot_be_omitted :
    ¬Real.sqrt (((Measure.dirac (1:ℝ≥0)).prod (Measure.dirac (1:ℝ≥0))).real
      (scaleLine 2)/2) ≤ (1/2:ℝ) := by
  rw [loop_dirac_line_mass]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
  have hn := Real.sqrt_nonneg (1/2:ℝ)
  intro h
  nlinarith

theorem empty_scale_energy (μ : Measure ℝ≥0) :
    (∑ d∈([]:List ℝ).toFinset,Real.sqrt ((μ.prod μ).real (scaleLine d)/2))=0 := by simp

end APPTReview
