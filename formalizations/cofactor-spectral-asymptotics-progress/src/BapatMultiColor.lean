import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace BapatFiniteRank

variable {ι κ C : Type*}

/-- Bijections preserving every color, for an arbitrary finite color set. -/
abbrev ColorTransport (f : ι → C) (g : κ → C) :=
  {e : ι ≃ κ // ∀ i, g (e i) = f i}

/-- A color-preserving bijection is exactly one independent bijection per fiber. -/
def colorTransportEquiv (f : ι → C) (g : κ → C) :
    ColorTransport f g ≃ (∀ c, {i // f i = c} ≃ {j // g j = c}) where
  toFun e c := e.1.subtypeEquiv (fun i => by rw [e.2 i])
  invFun es := ⟨Equiv.ofFiberEquiv es, Equiv.ofFiberEquiv_map es⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl
  right_inv es := by
    funext c
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rcases i with ⟨i, hi⟩
    subst c
    rfl

variable [Fintype ι] [Fintype κ] [Fintype C]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq C]

def colorCounts (f : ι → C) (c : C) : ℕ := Fintype.card {i // f i = c}

/-- The multi-index factorial counts the matching bijections exactly. -/
theorem card_colorTransport_eq (f : ι → C) (g : κ → C)
    (h : colorCounts f = colorCounts g) :
    Fintype.card (ColorTransport f g) = ∏ c, (colorCounts f c).factorial := by
  classical
  rw [Fintype.card_congr (colorTransportEquiv f g), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c hc
  let e : {i // f i = c} ≃ {j // g j = c} :=
    Fintype.equivOfCardEq (congrFun h c)
  exact Fintype.card_equiv e

theorem card_colorTransport_ne (f : ι → C) (g : κ → C)
    (h : colorCounts f ≠ colorCounts g) :
    Fintype.card (ColorTransport f g) = 0 := by
  classical
  letI : IsEmpty (ColorTransport f g) := ⟨fun e => h (by
    funext c
    exact Fintype.card_congr (colorTransportEquiv f g e c))⟩
  exact Fintype.card_of_isEmpty

theorem card_colorTransport (f : ι → C) (g : κ → C) :
    Fintype.card (ColorTransport f g) =
      if colorCounts f = colorCounts g then ∏ c, (colorCounts f c).factorial else 0 := by
  classical
  split_ifs with h
  · exact card_colorTransport_eq f g h
  · exact card_colorTransport_ne f g h

end BapatFiniteRank
