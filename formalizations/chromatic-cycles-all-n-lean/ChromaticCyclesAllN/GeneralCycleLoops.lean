import ChromaticCyclesAllN.GeneralCycleWalk

namespace ChromaticCycleAll
open SimpleGraph

theorem colorSupport_ne_nil {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) : colorSupport f ≠ [] := by
  simp [colorSupport]

theorem colorSupport_head {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) :
    (colorSupport f).head (colorSupport_ne_nil f) = f 0 := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [List.head_eq_getElem_zero]
  simpa using colorSupport_get f 0 hpos

theorem colorSupport_last {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) :
    (colorSupport f).getLast (colorSupport_ne_nil f) = f 0 := by
  simp [colorSupport, List.getLast_append_singleton]

def succClosedWalk {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) :
    (completeGraph α).Walk (f 0) (f 0) :=
  (Walk.ofSupport (colorSupport f) (colorSupport_ne_nil f)
      (colorSupport_chain hn f h)).copy (colorSupport_head f)
        (colorSupport_last f)

theorem succClosedWalk_support {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) :
    (succClosedWalk hn f h).support = colorSupport f := by
  simp [succClosedWalk, Walk.support_copy, Walk.support_ofSupport]

theorem succClosedWalk_length {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) :
    (succClosedWalk hn f h).length = n := by
  have hs := (succClosedWalk hn f h).length_support
  rw [succClosedWalk_support] at hs
  rw [colorSupport_length] at hs
  omega

end ChromaticCycleAll
