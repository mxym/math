import CofactorMarkedCoefficientLower

/-! Pure-coordinate coefficients of actual products of linear forms. -/
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial BapatFiniteRank
namespace CofactorSpectral
noncomputable section
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem assignmentDegree_pure_iff (f : V → C) (c : C) :
    assignmentDegree f = Finsupp.single c (Fintype.card V) ↔ f = fun _ => c := by
  constructor
  · intro h
    funext i
    change f i = c
    by_contra hi
    have hpos : 0 < colorCounts f (f i) := by
      unfold colorCounts
      exact Fintype.card_pos_iff.mpr ⟨⟨i,rfl⟩⟩
    have he := congrArg (fun α : C →₀ ℕ => α (f i)) h
    simp only [assignmentDegree_apply,Finsupp.single_apply] at he
    have hci : c ≠ f i := fun he => hi he.symm
    have hzero : colorCounts f (f i) = 0 := by simpa only [if_neg hci] using he
    omega
  · rintro rfl
    ext d
    simp [assignmentDegree,Finsupp.single_apply]

theorem formsProduct_pure_coefficient (v : V → C → ℂ) (c : C) :
    (formsProduct v).coeff (Finsupp.single c (Fintype.card V)) = ∏ i, v i c := by
  classical
  rw [formsProduct_expand]
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  simp_rw [assignmentDegree_pure_iff]
  simp [assignmentWeight]

theorem markedSum_pure_coefficient (v : V → C → ℂ) (w : V → ℂ) (c d : C) :
    (markedSum v w d).coeff (Finsupp.single c (Fintype.card V-1)) =
      ∑ i, star (w i) * v i d * ∏ j : {j : V // j ≠ i}, v j.val c := by
  classical
  unfold markedSum weightedPolynomial markedProduct omittedProduct
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Fintype.card {j : V // j ≠ i} = Fintype.card V-1 := by
    simp [Fintype.card_subtype_compl]
  rw [← hc,formsProduct_pure_coefficient]

end
end CofactorSpectral
