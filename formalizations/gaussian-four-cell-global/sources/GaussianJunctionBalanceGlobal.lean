import GaussianJunctionBalanceRigidity
import GaussianEquidistantRigidity

/-! If every actual triple junction of a full simplex has balanced unit
normals, all edges are equal. Trace and centering then identify the regular
Gram matrix. No minimizing or stationary cluster is postulated here. -/
open Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e : ℕ}

theorem all_triple_balances_regular_gram
    (v : Fin (d+3) → Space e) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i = 0) (ht : ∑ i,‖v i‖^2 = 1)
    (hbalance : ∀ i j l : Fin (d+3),i ≠ j → j ≠ l → l ≠ i →
      ‖v i-v j‖⁻¹ • (v i-v j)+‖v j-v l‖⁻¹ • (v j-v l)+
        ‖v l-v i‖⁻¹ • (v l-v i) = 0) :
    scoreGram v = regularCovariance (d+3) := by
  have h01 : (0:Fin (d+3)) ≠ 1 := by simp
  have hbase (i : Fin (d+3)) (hi : i ≠ 0) : ‖v 0-v i‖ = ‖v 0-v 1‖ := by
    by_cases hi1 : i=1
    · rw [hi1]
    · have he := triple_unit_normal_balance_lengths v hv 0 i 1 (Ne.symm hi) hi1
        (Ne.symm h01) (hbalance 0 i 1 (Ne.symm hi) hi1 (Ne.symm h01))
      exact he.1.trans (he.2.trans (norm_sub_rev _ _))
  have hedge (i j : Fin (d+3)) (hij : i ≠ j) : ‖v i-v j‖ = ‖v 0-v 1‖ := by
    by_cases hi : i=0
    · subst i
      exact hbase j (Ne.symm hij)
    · by_cases hj : j=0
      · subst j
        exact (norm_sub_rev _ _).trans (hbase i hi)
      · have he := triple_unit_normal_balance_lengths v hv 0 i j (Ne.symm hi) hij hj
          (hbalance 0 i j (Ne.symm hi) hij hj)
        exact he.1.symm.trans (hbase i hi)
  apply equidistant_centered_gram_regular (by omega : 2 ≤ d+3) v hz ht (‖v 0-v 1‖^2)
  intro i j hij
  rw [hedge i j hij]

end GaussianMeasureBridge
