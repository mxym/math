import CofactorPureCoefficient

/-! The exact marked pure-x coefficient for actual binary rows (a_i,a_i z_i). -/
set_option autoImplicit false
open scoped BigOperators
open BapatFiniteRank
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def binaryRows (a z : V → ℂ) : V → Fin 2 → ℂ := fun i => ![a i,a i*z i]

theorem complement_product_mul (a : V → ℂ) (i : V) :
    (∏ j : {j : V // j ≠ i}, a j.val) * a i = ∏ j, a j := by
  classical
  have he : (∏ j ∈ Finset.univ.erase i, a j) = ∏ j : {j : V // j ≠ i}, a j.val :=
    Finset.prod_subtype (p := fun j => j ≠ i) (F := inferInstance)
      (Finset.univ.erase i) (fun j => by simp) a
  rw [← he]
  exact Finset.prod_erase_mul Finset.univ a (Finset.mem_univ i)

theorem binaryRows_marked_pure_coefficient (a z w : V → ℂ) :
    (markedSum (binaryRows a z) w (1 : Fin 2)).coeff
      (Finsupp.single (0 : Fin 2) (Fintype.card V-1)) =
        (∏ i, a i) * ∑ i, star (w i)*z i := by
  rw [markedSum_pure_coefficient]
  simp only [binaryRows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := complement_product_mul a i
  calc
    _ = ((∏ j : {j : V // j ≠ i}, a j.val)*a i) * (star (w i)*z i) := by ring
    _ = _ := by rw [h]

theorem binaryRows_marked_quadratic_lower (a z w : V → ℂ) :
    ((Fintype.card V-1).factorial : ℝ) * Complex.normSq (∏ i, a i) *
      Complex.normSq (∑ i, star (w i)*z i) ≤
        (∑ i,∑ j,star (w i)*compound (complexGram (binaryRows a z)) i j*w j).re := by
  have h := marked_coefficient_quadratic_lower (binaryRows a z) w (1 : Fin 2)
    (Finsupp.single (0 : Fin 2) (Fintype.card V-1))
  rw [binaryRows_marked_pure_coefficient,Complex.normSq_mul] at h
  simpa only [multiFactorial,Fin.prod_univ_two,Finsupp.single_apply,Fin.zero_ne_one,
    if_pos rfl,if_neg,if_true,if_false,mul_one,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,mul_assoc] using h

end
end CofactorSpectral
