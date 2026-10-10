import APPTReview.Basic

open scoped BigOperators
namespace APPTReview
variable {ι : Type*} [Fintype ι]

theorem tail_cauchy (v : ι → ℝ) :
    (∑ i, v i)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, (v i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun _ => (1 : ℝ)) v

/-- Dimension-uniform equality from PROOF.md, with the tail cardinality explicit. -/
theorem multilevel_sos_identity (x y : ℝ) (v : ι → ℝ) :
    (2*(Fintype.card ι : ℝ)-1)*(x^2+y^2+∑ i, (v i)^2)
      - 2*(x*y+(x+y)*(∑ i, v i)+((∑ i, v i)^2-∑ i, (v i)^2)/2)
      - 4*((Fintype.card ι : ℝ)-2)*x*y =
    (2*(Fintype.card ι : ℝ)-2)*(x-y)^2
      + 2*((Fintype.card ι : ℝ)*(∑ i, (v i)^2)-(∑ i, v i)^2)
      + (x+y-∑ i, v i)^2 := by ring

/-- Nonnegativity in arbitrary dimension. The passage from arbitrary quantum
vectors to these Schmidt coordinates is a separate formal obligation. -/
theorem multilevel_sos_nonneg (hι : 2 ≤ Fintype.card ι) (x y : ℝ) (v : ι → ℝ) :
    0 ≤ (2*(Fintype.card ι : ℝ)-1)*(x^2+y^2+∑ i, (v i)^2)
      - 2*(x*y+(x+y)*(∑ i, v i)+((∑ i, v i)^2-∑ i, (v i)^2)/2)
      - 4*((Fintype.card ι : ℝ)-2)*x*y := by
  rw [multilevel_sos_identity]
  have hn : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hι
  exact add_nonneg
    (add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (tail_cauchy v)))) (sq_nonneg _)

theorem entropy_quartic_identity (a : ℝ) :
    3*a^4+7*a^3-18*a^2-12*a+24 =
      3*(a-1)^4+19*(a-1)^3+21*((a-1)-5/14)^2+37/28 := by ring

theorem entropy_quartic_positive {a : ℝ} (ha : 1 ≤ a) :
    0 < 3*a^4+7*a^3-18*a^2-12*a+24 := by
  rw [entropy_quartic_identity]
  have h : 0 ≤ a-1 := by linarith
  positivity

/-- Scalar gaps, not a replacement for the APPT membership proof. -/
theorem explicit_purity_gaps :
    (2675 : ℝ)/1006009 - 97/36481 = 3802/36700214329 ∧
    (2675 : ℝ)/1006009 - 5/1881 = 1630/1892302929 ∧
    (97 : ℝ)/36481 < 2675/1006009 ∧ (5 : ℝ)/1881 < 2675/1006009 := by
  norm_num
end APPTReview
