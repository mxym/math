import APPT.OrderedSpectrum
open scoped BigOperators
namespace APPT

def CornerConditions {D : ℕ} (lam : Fin D → ℝ) : Prop :=
  ∀ x : Fin 9 → Fin D, Function.Injective x →
    (matA (lam ∘ x)).PosSemidef ∧ (matB (lam ∘ x)).PosSemidef

theorem outerIndex_val (M : ℕ) (i : Fin 9) :
    (outerIndex M i).val = if i.val < 3 then i.val else M+i.val := by
  fin_cases i <;> rfl

theorem outerIndex_injective (M : ℕ) : Function.Injective (outerIndex M) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [outerIndex_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem spectrum_bound_large {D : ℕ} (hD : 27 ≤ D)
    (lam : Fin D → ℝ) (horder : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (hC : CornerConditions lam) : (∑ i, (lam i)^2) ≤ 9/(8*(D : ℝ)) := by
  let M := D-9
  have hm : 18 ≤ M := by dsimp [M]; omega
  have hd : 3+(M+6)=D := by dsimp [M]; omega
  let e := finCongr hd
  let l : Fin (3+(M+6)) → ℝ := lam ∘ e
  have hl : Antitone l := by
    intro i j hij
    exact horder hij
  have ht : ∑ i, l i = 1 := by
    exact (e.sum_comp lam).trans hsum
  have hp : ∀ i, 0 ≤ l i := fun i => hpos (e i)
  have hAB := hC (e ∘ outerIndex M) (e.injective.comp (outerIndex_injective M))
  have h := ordered_spectrum_large hm l hl hp ht hAB.1 hAB.2
  have hsq : (∑ i, (l i)^2) = ∑ i, (lam i)^2 := e.sum_comp (fun i => (lam i)^2)
  have hdR : 9+(M : ℝ) = (D : ℝ) := by
    have hnat : 9+M=D := by omega
    exact_mod_cast hnat
  rwa [hsq,hdR] at h

end APPT
