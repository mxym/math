import QutritMUB
import QuantumBorn

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
noncomputable section

namespace ECQC.Qutrit

/-- The common literal Born probability table in all four settings. -/
def probabilityTable : Matrix Q Q ℝ :=
  !![0,1/4,1/4; 1/4,0,0; 1/4,0,0]

set_option maxHeartbeats 5000000 in
/-- This computes the actual density-matrix Born rule, not a surrogate table. -/
theorem bornTable_eq (a : Fin 4) : bornTable rho (basis a) (basis a) = probabilityTable := by
  ext j k
  fin_cases a <;> fin_cases j <;> fin_cases k
  all_goals
    norm_num [bornTable, rho, born_pureState, dotProduct, localOutcome,
      psi, coefficients, probabilityTable, Fintype.sum_prod_type, Fin.sum_univ_succ]
    <;> qutrit_arith

theorem probabilityTable_nonneg (i j : Q) : 0 ≤ probabilityTable i j := by
  fin_cases i <;> fin_cases j <;> norm_num [probabilityTable]

theorem probabilityTable_total : ∑ i, ∑ j, probabilityTable i j = 1 := by
  norm_num [probabilityTable, Fin.sum_univ_succ]

theorem actual_born_probabilities (a : Fin 4) :
    (∀ i j, 0 ≤ bornTable rho (basis a) (basis a) i j) ∧
    (∑ i, ∑ j, bornTable rho (basis a) (basis a) i j) = 1 := by
  rw [bornTable_eq]
  exact ⟨probabilityTable_nonneg, probabilityTable_total⟩

end ECQC.Qutrit
