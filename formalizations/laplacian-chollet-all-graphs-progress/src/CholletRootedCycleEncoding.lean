import CholletClosedWalkTrace
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! Encode a simple directed cycle and its root as a finite vertex tuple.
The encoding is injective, so weighted rooted simple cycles may be compared
to the arbitrary closed walks in the matrix-power trace formula. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

abbrev RootedCycle (k : ℕ) := {p : Equiv.Perm V × V //
  p.1.IsCycle ∧ p.2 ∈ p.1.support ∧ p.1.support.card = k}

instance rootedCycleFintype (k : ℕ) : Fintype (RootedCycle (V := V) k) :=
  Fintype.ofFinite _

theorem rootedCycle_list_length (k : ℕ) (r : RootedCycle (V := V) k) :
    (r.val.1.toList r.val.2).length = k := by
  rw [Equiv.Perm.length_toList,r.property.1.cycleOf_eq
    (Equiv.Perm.mem_support.mp r.property.2.1)]
  exact r.property.2.2

def rootedCycleTuple (k : ℕ) (r : RootedCycle (V := V) k) : Fin k → V :=
  fun i => (r.val.1.toList r.val.2)[i.val]'(by
    rw [rootedCycle_list_length]; exact i.isLt)

theorem rootedCycleTuple_injective (k : ℕ) :
    Function.Injective (rootedCycleTuple (V := V) k) := by
  intro r s h
  have hl : r.val.1.toList r.val.2 = s.val.1.toList s.val.2 := by
    apply List.ext_getElem
    · rw [rootedCycle_list_length,rootedCycle_list_length]
    · intro n hn hm
      have hk : n < k := by rwa [rootedCycle_list_length] at hn
      exact congrFun h ⟨n,hk⟩
  have hp := congrArg List.formPerm hl
  rw [Equiv.Perm.formPerm_toList,Equiv.Perm.formPerm_toList,
    r.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp r.property.2.1),
    s.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp s.property.2.1)] at hp
  have hk : 0 < k := by
    have htwo := r.property.1.two_le_card_support
    rw [r.property.2.2] at htwo
    omega
  have hx := congrFun h ⟨0,hk⟩
  have hr : 0 < (r.val.1.toList r.val.2).length := by rw [rootedCycle_list_length]; exact hk
  have hs : 0 < (s.val.1.toList s.val.2).length := by rw [rootedCycle_list_length]; exact hk
  change (r.val.1.toList r.val.2)[0]'hr = (s.val.1.toList s.val.2)[0]'hs at hx
  rw [Equiv.Perm.toList_getElem_zero _ _ r.property.2.1,
    Equiv.Perm.toList_getElem_zero _ _ s.property.2.1] at hx
  exact Subtype.ext (Prod.ext hp hx)

end
end Chollet
