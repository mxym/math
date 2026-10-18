import CircuitCompletion.ActiveWidth
import CircuitCompletion.OccupationStep

open scoped BigOperators
namespace CircuitCompletion

/-- Arithmetic cost of the proved one-step compiler at the integer activity
width. This definition does not assert a completed all-k recursive circuit. -/
def stageGateBudget (j : ℕ) : ℕ := 80*(activeWires j)^2*(2^activeWires j)^2

def recursiveGateBudget (k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range k,stageGateBudget j)+100*k^2

theorem stageGateBudget_bound (k j : ℕ) (hj : j<k) :
    stageGateBudget j≤20480*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2 := by
  have hw : activeWires j≤6*Nat.clog 2 (k+3)+2 := by
    have h1 := activeWires_log_bound j
    have h2 := Nat.clog_mono_right 2 (by omega : j+3≤k+3)
    omega
  have hd : 2^activeWires j≤16*(k+2)^3 :=
    (activeDimension_polynomial j).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : j+3≤k+2) _))
  calc
    stageGateBudget j≤80*(6*Nat.clog 2 (k+3)+2)^2*(16*(k+2)^3)^2 := by
      unfold stageGateBudget
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw _))
        (Nat.pow_le_pow_left hd _)
    _ = _ := by ring

/-- Explicit polynomial/logarithmic arithmetic envelope for the assembled
stage budgets; actual all-k assembly is a separate outstanding theorem. -/
theorem recursiveGateBudget_bound (k : ℕ) :
    recursiveGateBudget k≤
      20480*k*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2+100*k^2 := by
  unfold recursiveGateBudget
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ j ∈ Finset.range k,20480*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact stageGateBudget_bound k j (Finset.mem_range.mp hj)
    _ = _ := by simp;ring

end CircuitCompletion
