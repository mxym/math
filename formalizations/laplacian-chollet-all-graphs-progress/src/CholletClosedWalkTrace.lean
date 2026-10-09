import CholletTraceSeries
import Mathlib.Data.Fin.Tuple.Basic

/-! Weighted walks underlying the actual matrix-power trace. Intermediate
vertices are arbitrary finite tuples, including repeated vertices. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

noncomputable def walkWeight (C : Matrix V V ℝ) : (n : ℕ) → (Fin n → V) → V → V → ℝ
  | 0,_,i,j => C i j
  | n+1,f,i,j => C i (f 0) * walkWeight C n (Fin.tail f) (f 0) j

lemma sum_fin_tuple_succ (n : ℕ) (g : (Fin (n+1) → V) → ℝ) :
    (∑ f,g f) = ∑ v,∑ f : Fin n → V,g (Fin.cons v f) := by
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => V)) g
  rw [← h,Fintype.sum_prod_type]
  rfl

theorem walkWeight_nonneg (C : Matrix V V ℝ) (hc : ∀ i j,0 ≤ C i j)
    (n : ℕ) (f : Fin n → V) (i j : V) : 0 ≤ walkWeight C n f i j := by
  induction n generalizing i with
  | zero => exact hc i j
  | succ n ih => exact mul_nonneg (hc i (f 0)) (ih (Fin.tail f) (f 0))

theorem matrix_pow_walk_sum (C : Matrix V V ℝ) (n : ℕ) (i j : V) :
    (C^(n+1)) i j = ∑ f : Fin n → V,walkWeight C n f i j := by
  induction n generalizing i with
  | zero => simp [walkWeight]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    simp_rw [ih]
    rw [sum_fin_tuple_succ]
    simp only [walkWeight,Fin.cons_zero,Fin.tail_cons,Finset.mul_sum]

theorem matrix_trace_closed_walk_sum (C : Matrix V V ℝ) (n : ℕ) :
    (C^(n+1)).trace = ∑ f : Fin (n+1) → V,
      walkWeight C n (Fin.tail f) (f 0) (f 0) := by
  rw [sum_fin_tuple_succ]
  simp only [Fin.cons_zero,Fin.tail_cons,Matrix.trace,Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  exact matrix_pow_walk_sum C n i i

end
end Chollet
