import APPTReview.PhysicalHeadLimit

set_option maxHeartbeats 100000

open scoped BigOperators
namespace APPTReview
#check density_appt_head_spectral_cubic

theorem zero_head_conditions :
    EntropyHeadConditions (n:=0) (fun _ : Fin 1 => (0:ℝ)) (fun _ : Fin 2 => (0:ℝ)) := by
  constructor <;> simp [Antitone]

#check zero_head_conditions
theorem zero_head_deficit :
    2-entropyHead (n:=0) (fun _ : Fin 1 => (0:ℝ)) (fun _ : Fin 2 => (0:ℝ))=2 := by
  norm_num [entropyHead,entropyKernel]

#check zero_head_deficit
/-- Ordinary zero-eigenvalue endpoints remain admitted by the scalar theorem. -/
theorem singular_head_conditions :
    EntropyHeadConditions (n:=0) (fun _ : Fin 1 => (0:ℝ))
      (fun i : Fin 2 => if i=0 then (1:ℝ) else 0) := by
  constructor
  · intro i; norm_num
  · intro i; norm_num
  · intro i; split_ifs <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  · norm_num
  · norm_num [Fin.sum_univ_one]

#check singular_head_conditions
theorem singular_head_exact_deficit :
    2-entropyHead (n:=0) (fun _ : Fin 1 => (0:ℝ))
      (fun i : Fin 2 => if i=0 then (1:ℝ) else 0)=1 := by
  change 2-((∑ i : Fin 1, (entropyKernel 0 + 0*(if i.castSucc=0 then 1 else 0))) +
    ∑ i : Fin 2, entropyKernel (-(if i=0 then 1 else 0)))=1
  rw [Fin.sum_univ_one,Fin.sum_univ_two]
  norm_num [entropyKernel]

#check singular_head_exact_deficit
/-- The shifted quadratic budget cannot be inferred merely from nonnegativity. -/
theorem missing_star_budget_rejected :
    ¬ EntropyHeadConditions (n:=0) (fun _ : Fin 1 => (3:ℝ)) (fun _ : Fin 2 => (0:ℝ)) := by
  intro h
  have hb := h.star_budget
  norm_num at hb

/-- A positive pivot cannot be silently identified with the uniform eigenvalue. -/
theorem pivot_not_uniform_regression : (2:ℝ)*(1/3) ≠ 1 := by norm_num

/-- Deleting trace one invalidates the normalization estimate, even for equal entries. -/
theorem trace_normalization_required : |(2:ℝ)*1-1| > 2*(0+0) := by norm_num

end APPTReview
