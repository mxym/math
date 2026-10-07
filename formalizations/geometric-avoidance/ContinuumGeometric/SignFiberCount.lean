import ContinuumGeometric.Interfaces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ContinuumGeometric
open Finset

/-- Forgetting the final sign gives the previously realized patterns. -/
def oldPatterns {α : Type*} [DecidableEq α] (S : Finset (α × CutSign)) : Finset α :=
  S.image Prod.fst

/-- Patterns that occur on the new zero stratum. -/
def zeroPatterns {α : Type*} [DecidableEq α] (S : Finset (α × CutSign)) : Finset α :=
  (S.filter (fun x => x.2 = CutSign.zero)).image Prod.fst

@[simp] theorem mem_zeroPatterns {α : Type*} [DecidableEq α]
    {S : Finset (α × CutSign)} {a : α} :
    a ∈ zeroPatterns S ↔ (a, CutSign.zero) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨b, s⟩, hb, hab⟩ := mem_image.mp h
    obtain ⟨hbs, hs⟩ := mem_filter.mp hb
    cases hs
    simpa only [Prod.fst] using hab ▸ hbs
  · intro h
    exact mem_image.mpr ⟨(a, CutSign.zero), mem_filter.mpr ⟨h, rfl⟩, rfl⟩

private theorem fiber_card_le {α : Type*} [DecidableEq α]
    (S : Finset (α × CutSign)) (a : α)
    (hcross : (a, CutSign.negative) ∈ S → (a, CutSign.positive) ∈ S →
      (a, CutSign.zero) ∈ S) :
    (S.filter (fun x => x.1 = a)).card ≤
      1 + if (a, CutSign.zero) ∈ S then 2 else 0 := by
  by_cases hz : (a, CutSign.zero) ∈ S
  · simp only [hz, ite_true]
    have hsub : S.filter (fun x => x.1 = a) ⊆
        {(a, CutSign.negative), (a, CutSign.zero), (a, CutSign.positive)} := by
      intro x hx
      obtain ⟨hxS, hxa⟩ := mem_filter.mp hx
      rcases x with ⟨b, s⟩
      change b = a at hxa
      subst b
      cases s <;> simp
    have h := card_le_card hsub
    simpa using h
  · simp only [hz, ite_false, Nat.add_zero]
    by_cases hn : (a, CutSign.negative) ∈ S
    · have hp : (a, CutSign.positive) ∉ S := fun hp => hz (hcross hn hp)
      have hsub : S.filter (fun x => x.1 = a) ⊆ {(a, CutSign.negative)} := by
        intro x hx
        obtain ⟨hxS, hxa⟩ := mem_filter.mp hx
        rcases x with ⟨b, s⟩
        change b = a at hxa
        subst b
        cases s with
        | negative => simp
        | zero => exact False.elim (hz hxS)
        | positive => exact False.elim (hp hxS)
      simpa using card_le_card hsub
    · have hsub : S.filter (fun x => x.1 = a) ⊆ {(a, CutSign.positive)} := by
        intro x hx
        obtain ⟨hxS, hxa⟩ := mem_filter.mp hx
        rcases x with ⟨b, s⟩
        change b = a at hxa
        subst b
        cases s with
        | negative => exact False.elim (hn hxS)
        | zero => exact False.elim (hz hxS)
        | positive => simp
      simpa using card_le_card hsub

/-- A new affine cut adds at most two patterns per realized old pattern on
its zero stratum. The only geometric input is that crossing signs force zero. -/
theorem card_le_oldPatterns_add_two_zeroPatterns {α : Type*} [DecidableEq α]
    (S : Finset (α × CutSign))
    (hcross : ∀ a, (a, CutSign.negative) ∈ S → (a, CutSign.positive) ∈ S →
      (a, CutSign.zero) ∈ S) :
    S.card ≤ (oldPatterns S).card + 2 * (zeroPatterns S).card := by
  have hfib : S.card = ∑ a ∈ oldPatterns S, (S.filter (fun x => x.1 = a)).card :=
    card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem Prod.fst hx)
  have hfilter : (oldPatterns S).filter (fun a => (a, CutSign.zero) ∈ S) =
      zeroPatterns S := by
    ext a
    simp only [mem_filter, mem_zeroPatterns]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨mem_image_of_mem Prod.fst h, h⟩
  calc
    S.card = ∑ a ∈ oldPatterns S, (S.filter (fun x => x.1 = a)).card := hfib
    _ ≤ ∑ a ∈ oldPatterns S, (1 + if (a, CutSign.zero) ∈ S then 2 else 0) :=
      sum_le_sum (fun a _ => fiber_card_le S a (hcross a))
    _ = (oldPatterns S).card + 2 * (zeroPatterns S).card := by
      rw [sum_add_distrib]
      simp only [sum_const, smul_eq_mul, Nat.mul_one]
      rw [← sum_filter]
      simp [hfilter, Nat.mul_comm]

/-- The explicit image/filter form, convenient when avoiding helper definitions. -/
theorem card_le_image_add_two_zero_image {α : Type*} [DecidableEq α]
    (S : Finset (α × CutSign))
    (hcross : ∀ a, (a, CutSign.negative) ∈ S → (a, CutSign.positive) ∈ S →
      (a, CutSign.zero) ∈ S) :
    S.card ≤ (S.image Prod.fst).card +
      2 * ((S.filter (fun x => x.2 = CutSign.zero)).image Prod.fst).card :=
  card_le_oldPatterns_add_two_zeroPatterns S hcross

/-- Combine the fiber count with independent old-pattern and zero-stratum bounds. -/
theorem card_le_of_old_and_zero_bounds {α : Type*} [DecidableEq α]
    (S : Finset (α × CutSign)) (oldBound zeroBound : ℕ)
    (hcross : ∀ a, (a, CutSign.negative) ∈ S → (a, CutSign.positive) ∈ S →
      (a, CutSign.zero) ∈ S)
    (hold : (oldPatterns S).card ≤ oldBound)
    (hzero : (zeroPatterns S).card ≤ zeroBound) :
    S.card ≤ oldBound + 2 * zeroBound :=
  (card_le_oldPatterns_add_two_zeroPatterns S hcross).trans
    (Nat.add_le_add hold (Nat.mul_le_mul_left 2 hzero))

#print axioms card_le_oldPatterns_add_two_zeroPatterns
#print axioms card_le_image_add_two_zero_image
#print axioms card_le_of_old_and_zero_bounds
end ContinuumGeometric
