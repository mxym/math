import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace GaussianFour

lemma exists_perm_strictMono_of_injective (a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    ∃ e : Equiv.Perm (Fin 4), StrictMono (a ∘ e) := by
  classical
  let s : Finset ℝ := Finset.univ.image a
  have hs : s.card = 4 := by
    simpa [s] using (Finset.card_image_of_injective Finset.univ ha)
  let o : Fin 4 ≃o s := s.orderIsoOfFin hs
  let f : Fin 4 → Fin 4 := fun i =>
    Classical.choose (Finset.mem_image.mp (o i).property)
  have hf : ∀ i, a (f i) = (o i : ℝ) :=
    fun i => (Classical.choose_spec (Finset.mem_image.mp (o i).property)).2
  have hfi : Function.Injective f := by
    intro i j hij
    apply o.injective
    apply Subtype.ext
    rw [← hf i, ← hf j, hij]
  have hfs : Function.Surjective f :=
    hfi.surjective_of_finite (Equiv.refl (Fin 4))
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e, ?_⟩
  intro i j hij
  change a (f i) < a (f j)
  rw [hf, hf]
  exact o.lt_iff_lt.mpr hij

end GaussianFour
