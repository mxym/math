import CofactorBinaryNorm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-! Exact sorting of finitely many real coordinates, retaining every tied coordinate. -/
set_option autoImplicit false
namespace CofactorSpectral
noncomputable section

theorem exists_antitone_permutation (n : ℕ) (x : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), Antitone (fun i => x (σ i)) := by
  classical
  let K := {p : ℝ ×ₗ Fin n // (ofLex p).1 = x (ofLex p).2}
  let e : Fin n ≃ K :=
    { toFun i := ⟨toLex (x i,i), rfl⟩
      invFun p := (ofLex p.val).2
      left_inv _ := rfl
      right_inv p := by
        apply Subtype.ext
        have hp : (x (ofLex p.val).2,(ofLex p.val).2) = ofLex p.val :=
          Prod.ext p.property.symm rfl
        exact congrArg toLex hp }
  letI : Fintype K := Fintype.ofEquiv (Fin n) e
  have hc : Fintype.card K = n := (Fintype.card_congr e).symm.trans (Fintype.card_fin n)
  let r := Fintype.orderIsoFinOfCardEq K hc
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.trans (r.toEquiv.trans e.symm)
  refine ⟨σ,?_⟩
  intro i j hij
  have hrev : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
  have hr : (r (Fin.rev j)).val ≤ (r (Fin.rev i)).val := r.monotone hrev
  have hfst := Prod.Lex.monotone_fst _ _ hr
  change x (ofLex (r (Fin.rev j)).val).2 ≤ x (ofLex (r (Fin.rev i)).val).2
  simpa only [(r (Fin.rev j)).property,
    (r (Fin.rev i)).property] using hfst

end
end CofactorSpectral
