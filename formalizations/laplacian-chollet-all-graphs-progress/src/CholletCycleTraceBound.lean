import CholletCycleOrbitWeight
import CholletMatchingRestriction

/-! Weighted rooted simple cycles are a subset of arbitrary closed walks.
The factor k counts the possible roots of one length-k directed cycle. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

def cyclesOfLength (k : ℕ) : Finset (Equiv.Perm V) :=
  allCycles.filter (fun σ => σ.support.card = k)

theorem rootedCycle_closed_weight (C : Matrix V V ℝ) (hs : ∀ i j,C i j = C j i)
    (n : ℕ) (r : RootedCycle (V := V) (n+2)) :
    walkWeight C (n+1) (Fin.tail (rootedCycleTuple (n+2) r))
      (rootedCycleTuple (n+2) r 0) (rootedCycleTuple (n+2) r 0) =
      cycleWeight C r.val.1 := by
  have ht : Fin.tail (rootedCycleTuple (n+2) r) = orbitTail r.val.1 r.val.2 (n+1) := by
    ext i
    simp only [Fin.tail,rootedCycleTuple_apply,orbitTail,Fin.val_succ]
  have hh : rootedCycleTuple (n+2) r 0 = r.val.2 := by
    rw [rootedCycleTuple_apply]
    simp
  have hp : r.val.1^(n+2) = 1 := by
    have ho : orderOf r.val.1 = n+2 := r.property.1.orderOf.trans r.property.2.2
    simpa only [ho] using pow_orderOf_eq_one r.val.1
  rw [ht,hh]
  calc
    _ = walkWeight C (n+1) (orbitTail r.val.1 r.val.2 (n+1)) r.val.2
        ((r.val.1^(n+2)) r.val.2) := by rw [hp]; rfl
    _ = _ := (walkWeight_orbit_product C hs r.val.1 r.val.2 (n+1)).trans
      (rootedCycle_orbit_product C (n+2) r)

theorem rootedCycle_weight_sum (C : Matrix V V ℝ) (k : ℕ) :
    (∑ r : RootedCycle (V := V) k,cycleWeight C r.val.1) =
      (k : ℝ) * (∑ σ ∈ cyclesOfLength (V := V) k,cycleWeight C σ) := by
  classical
  have h := Finset.sum_subtype
    (s := (Finset.univ : Finset (Equiv.Perm V × V)).filter
      (fun p => p.1.IsCycle ∧ p.2 ∈ p.1.support ∧ p.1.support.card = k))
    (p := fun p : Equiv.Perm V × V => p.1.IsCycle ∧ p.2 ∈ p.1.support ∧ p.1.support.card = k)
    (F := inferInstance) (fun _ => by simp) (fun p => cycleWeight C p.1)
  rw [← h,Finset.sum_filter,Fintype.sum_prod_type]
  have hi (σ : Equiv.Perm V) :
      (∑ x,if σ.IsCycle ∧ x ∈ σ.support ∧ σ.support.card = k then cycleWeight C σ else 0) =
      (if σ.IsCycle ∧ σ.support.card = k then (k : ℝ) * cycleWeight C σ else 0) := by
    by_cases hc : σ.IsCycle <;> by_cases hk : σ.support.card = k
    · simp only [hc,hk,and_true,true_and]
      rw [← Finset.sum_filter]
      have hf : (Finset.univ.filter (fun x : V => x ∈ σ.support)) = σ.support := by
        ext x
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hf]
      simp only [Finset.sum_const,nsmul_eq_mul,hk,ite_true]
    · simp [hc,hk]
    · simp [hc]
    · simp [hc]
  simp_rw [hi]
  simp only [cyclesOfLength,allCycles,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hc : σ.IsCycle <;> by_cases hk : σ.support.card = k <;> simp [hc,hk]

theorem cyclesOfLength_weight_le_trace (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j = C j i) (n : ℕ) :
    (∑ σ ∈ cyclesOfLength (V := V) (n+2),cycleWeight C σ) ≤
      (C^(n+2)).trace / (n+2 : ℕ) := by
  classical
  let e : RootedCycle (V := V) (n+2) ↪ (Fin (n+2) → V) :=
    ⟨rootedCycleTuple (n+2),rootedCycleTuple_injective (n+2)⟩
  have h := Matching.sum_embedding_le e
    (fun f => walkWeight C (n+1) (Fin.tail f) (f 0) (f 0))
    (fun f => walkWeight_nonneg C hc _ _ _ _)
  change (∑ r : RootedCycle (V := V) (n+2),
    walkWeight C (n+1) (Fin.tail (rootedCycleTuple (n+2) r))
      (rootedCycleTuple (n+2) r 0) (rootedCycleTuple (n+2) r 0)) ≤ _ at h
  simp_rw [rootedCycle_closed_weight C hs] at h
  rw [rootedCycle_weight_sum,← matrix_trace_closed_walk_sum C (n+1)] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mpr
  linarith

end
end Chollet
