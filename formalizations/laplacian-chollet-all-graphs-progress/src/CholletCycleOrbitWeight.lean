import CholletRootedCycleEncoding

/-! Relate weighted walks along a permutation orbit to its edge products. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

def orbitTail (σ : Equiv.Perm V) (x : V) (n : ℕ) : Fin n → V :=
  fun i => (σ^(i.val+1)) x

theorem perm_power_apply_next (σ : Equiv.Perm V) (x : V) (n : ℕ) :
    (σ^n) (σ x) = (σ^(n+1)) x := by
  rw [pow_succ,Equiv.Perm.mul_apply]

theorem orbitTail_tail (σ : Equiv.Perm V) (x : V) (n : ℕ) :
    Fin.tail (orbitTail σ x (n+1)) = orbitTail σ (σ x) n := by
  ext i
  simp [orbitTail,Fin.tail,perm_power_apply_next,Nat.add_assoc]

theorem walkWeight_orbit_product (C : Matrix V V ℝ) (hs : ∀ i j,C i j = C j i)
    (σ : Equiv.Perm V) (x : V) (n : ℕ) :
    walkWeight C n (orbitTail σ x n) x ((σ^(n+1)) x) =
      ∏ i ∈ Finset.range (n+1),C ((σ^(i+1)) x) ((σ^i) x) := by
  induction n generalizing x with
  | zero => simpa [walkWeight] using hs x (σ x)
  | succ n ih =>
    change C x (σ x) * walkWeight C n (Fin.tail (orbitTail σ x (n+1))) (σ x)
      ((σ^(n+1+1)) x) = _
    rw [orbitTail_tail,← perm_power_apply_next σ x (n+1),ih]
    rw [Finset.prod_range_succ' (fun i => C ((σ^(i+1)) x) ((σ^i) x)) (n+1)]
    simp_rw [perm_power_apply_next]
    change C x (σ x) * (∏ i ∈ Finset.range (n+1),
      C ((σ^(i+1+1)) x) ((σ^(i+1)) x)) =
      (∏ i ∈ Finset.range (n+1),C ((σ^(i+1+1)) x) ((σ^(i+1)) x)) * C (σ x) x
    rw [hs x (σ x),mul_comm]

theorem rootedCycleTuple_apply (k : ℕ) (r : RootedCycle (V := V) k) (i : Fin k) :
    rootedCycleTuple k r i = (r.val.1^i.val) r.val.2 := by
  unfold rootedCycleTuple
  rw [Equiv.Perm.getElem_toList]

theorem rootedCycle_list_support (k : ℕ) (r : RootedCycle (V := V) k) :
    (r.val.1.toList r.val.2).toFinset = r.val.1.support := by
  rw [← List.support_formPerm_of_nodup _
    (Equiv.Perm.nodup_toList _ _) (fun y => Equiv.Perm.toList_ne_singleton _ _ y),
    Equiv.Perm.formPerm_toList,
    r.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp r.property.2.1)]

theorem rootedCycle_orbit_product (C : Matrix V V ℝ) (k : ℕ)
    (r : RootedCycle (V := V) k) :
    (∏ i ∈ Finset.range k,C ((r.val.1^(i+1)) r.val.2) ((r.val.1^i) r.val.2)) =
      cycleWeight C r.val.1 := by
  unfold cycleWeight
  apply Finset.prod_bij (fun i _ => (r.val.1^i) r.val.2)
  · intro i hi
    have hib : i < (r.val.1.toList r.val.2).length := by
      rw [rootedCycle_list_length]; exact Finset.mem_range.mp hi
    rw [← rootedCycle_list_support,List.mem_toFinset,← Equiv.Perm.getElem_toList _ _ i hib]
    exact List.getElem_mem hib
  · intro i hi j hj he
    have hib : i < (r.val.1.toList r.val.2).length := by
      rw [rootedCycle_list_length]; exact Finset.mem_range.mp hi
    have hjb : j < (r.val.1.toList r.val.2).length := by
      rw [rootedCycle_list_length]; exact Finset.mem_range.mp hj
    have hget := List.nodup_iff_injective_getElem.mp (Equiv.Perm.nodup_toList r.val.1 r.val.2)
    have hidx : (⟨i,hib⟩ : Fin (r.val.1.toList r.val.2).length) = ⟨j,hjb⟩ := by
      apply hget
      simpa only [Equiv.Perm.getElem_toList] using he
    exact congrArg Fin.val hidx
  · intro v hv
    rw [← rootedCycle_list_support,List.mem_toFinset] at hv
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hv
    refine ⟨i,Finset.mem_range.mpr ?_,?_⟩
    · rwa [rootedCycle_list_length] at hi
    · simpa only [Equiv.Perm.getElem_toList] using he
  · intro i _
    rw [pow_succ',Equiv.Perm.mul_apply]

end
end Chollet
