import TensorMain

namespace ComplexPencilTensor

theorem weight_total_one (t : ℝ) :
    (∑ j : Fin 6, weight t j)=1 := by
  simp [weight,Fin.sum_univ_succ]
  ring

theorem first_marginal_uniform (t : ℝ) (r : Fin 3) :
    (∑ j : Fin 6, if first j = r then weight t j else 0) =
      (1/3:ℝ) := by
  fin_cases r <;> simp [weight,first,Fin.sum_univ_succ] <;> ring

theorem second_marginal_uniform (t : ℝ) (r : Fin 3) :
    (∑ j : Fin 6, if second j = r then weight t j else 0) =
      (1/3:ℝ) := by
  fin_cases r <;> simp [weight,second,Fin.sum_univ_succ] <;> ring

theorem third_marginal_uniform (t : ℝ) (r : Fin 3) :
    (∑ j : Fin 6, if third j = r then weight t j else 0) =
      (1/3:ℝ) := by
  fin_cases r <;> simp [weight,third,Fin.sum_univ_succ] <;> ring

/-- All six outcomes are permutations of the three labels. -/
theorem permutation_positions (j : Fin 6) :
    first j ≠ second j ∧ second j ≠ third j ∧
      third j ≠ first j := by
  fin_cases j <;> decide

#print axioms ComplexPencilTensor.first_marginal_uniform

end ComplexPencilTensor
