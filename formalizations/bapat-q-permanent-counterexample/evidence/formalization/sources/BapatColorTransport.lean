import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-!
Two-color permutation fibers. This is the counting step which produces the
factorials in the rank-two permanent/Fischer identity.
-/

namespace BapatFischer

set_option autoImplicit false

open Equiv Fintype
open scoped Nat

variable {ι : Type*}

/-- A permutation transporting one selected color class onto another. -/
abbrev ColorTransport (p q : ι → Prop) :=
  {σ : Equiv.Perm ι // ∀ i, p i ↔ q (σ i)}

section Equivalence

variable (p q : ι → Prop) [DecidablePred p] [DecidablePred q]

/-- The two restrictions determine, and can freely be assembled into, a
color-preserving permutation. No ordering of either color class is used. -/
def colorTransportEquiv : ColorTransport p q ≃
    ({i // p i} ≃ {i // q i}) × ({i // ¬ p i} ≃ {i // ¬ q i}) where
  toFun σ := (σ.1.subtypeEquiv σ.2,
    σ.1.subtypeEquiv (fun i => not_congr (σ.2 i)))
  invFun ef := ⟨Equiv.subtypeCongr ef.1 ef.2, by
    intro i
    by_cases hi : p i
    · have he : Equiv.subtypeCongr ef.1 ef.2 i = ef.1 ⟨i, hi⟩ := by
        simp [Equiv.subtypeCongr, hi]
      rw [he]
      exact iff_of_true hi (ef.1 ⟨i, hi⟩).2
    · have he : Equiv.subtypeCongr ef.1 ef.2 i = ef.2 ⟨i, hi⟩ := by
        simp [Equiv.subtypeCongr, hi]
      rw [he]
      exact iff_of_false hi (ef.2 ⟨i, hi⟩).2⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : p i <;> simp [Equiv.subtypeCongr, Equiv.subtypeEquiv, hi]
  right_inv ef := by
    rcases ef with ⟨e, f⟩
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp [Equiv.subtypeCongr, Equiv.subtypeEquiv, i.2]
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp [Equiv.subtypeCongr, Equiv.subtypeEquiv, i.2]

end Equivalence

section Cardinality

variable [Fintype ι] [DecidableEq ι]
variable (p q : ι → Prop) [DecidablePred p] [DecidablePred q]

/-- There are (Nat.factorial k) (n-k)! bijections sending a specified k-element color
class onto any other specified k-element color class. -/
theorem card_colorTransport_of_eq
    (h : Fintype.card {i // p i} = Fintype.card {i // q i}) :
    Fintype.card (ColorTransport p q) =
      (Nat.factorial (Fintype.card {i // p i})) *
        (Nat.factorial (Fintype.card ι - Fintype.card {i // p i})) := by
  classical
  let e : {i // p i} ≃ {i // q i} := Fintype.equivOfCardEq h
  let f : {i // ¬ p i} ≃ {i // ¬ q i} :=
    Fintype.equivOfCardEq (Fintype.card_compl_eq_card_compl p q h)
  rw [Fintype.card_congr (colorTransportEquiv p q), Fintype.card_prod,
    Fintype.card_equiv e, Fintype.card_equiv f, Fintype.card_subtype_compl]

theorem card_colorTransport_of_ne
    (h : Fintype.card {i // p i} ≠ Fintype.card {i // q i}) :
    Fintype.card (ColorTransport p q) = 0 := by
  classical
  letI : IsEmpty (ColorTransport p q) :=
    ⟨fun σ => h (Fintype.card_congr (σ.1.subtypeEquiv σ.2))⟩
  exact Fintype.card_of_isEmpty

theorem card_colorTransport :
    Fintype.card (ColorTransport p q) =
      if Fintype.card {i // p i} = Fintype.card {i // q i} then
        (Nat.factorial (Fintype.card {i // p i})) *
          (Nat.factorial (Fintype.card ι - Fintype.card {i // p i}))
      else 0 := by
  classical
  split_ifs with h
  · exact card_colorTransport_of_eq p q h
  · exact card_colorTransport_of_ne p q h

theorem card_colorTransport_finset (s t : Finset ι) :
    Fintype.card (ColorTransport (· ∈ s) (· ∈ t)) =
      if s.card = t.card then (Nat.factorial s.card) * (Nat.factorial (Fintype.card ι - s.card)) else 0 := by
  classical
  simpa only [Fintype.card_coe] using card_colorTransport (· ∈ s) (· ∈ t)

end Cardinality

end BapatFischer
