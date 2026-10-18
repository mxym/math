import CircuitCompletion.Semantics

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

theorem wireCoordinates_update {n : ℕ} (i : Fin n) (w : Bits n) (b : Bool) :
    (wireCoordinates i).symm (b,fun j => w j.1)=Function.update w i b := by
  funext j
  by_cases h : j=i <;> simp [wireCoordinates,h]

set_option maxHeartbeats 2000000 in
theorem singleWire_action {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup Bool ℂ)
    (v : Bits n → ℂ) (w : Bits n) :
    (((Gate.single i U).denote : Matrix (Bits n) (Bits n) ℂ)*ᵥv) w =
      ∑ b : Bool,(U : Matrix Bool Bool ℂ) (w i) b*v (Function.update w i b) := by
  change (∑ q : Bits n,(singleWire i U : Matrix (Bits n) (Bits n) ℂ) w q*v q)=_
  rw [← Equiv.sum_comp (wireCoordinates i).symm]
  simp only [Fintype.sum_prod_type]
  have he (b : Bool) (q : {j : Fin n // j≠i}→Bool) :
      (singleWire i U : Matrix (Bits n) (Bits n) ℂ) w ((wireCoordinates i).symm (b,q))=
      (U : Matrix Bool Bool ℂ) (w i) b*
        (1 : Matrix ({j : Fin n // j≠i}→Bool) ({j : Fin n // j≠i}→Bool) ℂ)
          (fun j => w j.1) q := by
    change ((U : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix ({j : Fin n // j≠i}→Bool)
      ({j : Fin n // j≠i}→Bool) ℂ)) ((wireCoordinates i) w)
        ((wireCoordinates i) ((wireCoordinates i).symm (b,q)))=_
    rw [Equiv.apply_symm_apply]
    rfl
  simp only [he]
  simp only [Matrix.one_apply]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [wireCoordinates_update]

end CircuitCompletion
