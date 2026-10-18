import CircuitCompletion.IndexedCompression
import CircuitCompletion.ActiveWidth

open scoped BigOperators
namespace CircuitCompletion

noncomputable def branchPivot {k : ℕ} (ν : Sym (Fin 4) (k+1)) : {i : Fin 4 // i∈ν} :=
  ⟨Classical.choose (Sym.exists_mem ν),Classical.choose_spec (Sym.exists_mem ν)⟩

noncomputable def pivotCoordinates {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : Bits (2+q) := (branchEmbedding enc ν) (branchPivot ν)

theorem pivotCoordinates_injective {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    Function.Injective (pivotCoordinates enc) := by
  intro ν μ h
  exact (branchCoordinates_equal enc ν μ _ _ _ _ h).1

noncomputable def branchCircuit {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : Circuit (2+q) :=
  indexedCompression (by omega) (branchEmbedding enc ν) (fun i => occupationMass ν i.1)
    (fun i => occupationMass_nonneg ν i.1) (branchPivot ν)

theorem branchCircuit_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    run (branchCircuit enc ν) (encodedBranch enc ν)=Pi.single (pivotCoordinates enc ν) 1 :=
  indexedCompression_action (by omega) _ _ _ (occupationMass_occupied_sum ν) _

theorem branchCircuit_fixes_other {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (h : ν≠μ) :
    run (branchCircuit enc μ) (encodedBranch enc ν)=encodedBranch enc ν := by
  apply indexedCompression_fixes_zero
  intro i
  exact encodedBranch_disjoint_zero enc ν μ h i.1 i.2

theorem branchCircuit_fixes_other_pivot {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (h : ν≠μ) :
    run (branchCircuit enc μ) (Pi.single (pivotCoordinates enc ν) 1)=
      Pi.single (pivotCoordinates enc ν) 1 := by
  apply indexedCompression_fixes_zero
  intro i
  have hn := branchCoordinates_disjoint enc ν μ h (branchPivot ν).1 i.1 (branchPivot ν).2 i.2
  simp only [Pi.single_apply]
  rw [if_neg]
  exact Ne.symm hn

theorem branchCircuit_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    (branchCircuit enc ν).length≤60*(2+q)^2*2^(2+q) := by
  have h := indexedCompression_length (by omega) (branchEmbedding enc ν)
    (fun i => occupationMass ν i.1) (fun i => occupationMass_nonneg ν i.1) (branchPivot ν)
  have hc : Fintype.card {i : Fin 4 // i∈ν}≤4 := by
    exact (Fintype.card_le_of_injective (fun i : {i : Fin 4 // i∈ν} => i.1) Subtype.val_injective)
  have h' := Nat.mul_le_mul_right (20*(2+q)^2*2^(2+q)) (show Fintype.card {i : Fin 4 // i∈ν}-1≤3 by omega)
  change (branchCircuit enc ν).length≤_ at h
  nlinarith

theorem run_flatMap_fixes {ι : Type*} {n : ℕ} (f : ι → Circuit n) (xs : List ι)
    (v : Bits n → ℂ) (hf : ∀ i∈xs,run (f i) v=v) : run (xs.flatMap f) v=v := by
  induction xs with
  | nil => simp [run,denote]
  | cons i xs ih =>
    rw [List.flatMap_cons,run_append,hf i (by simp)]
    apply ih
    intro j hj
    exact hf j (by simp [hj])

theorem run_flatMap_unique {ι : Type*} [DecidableEq ι] {n : ℕ} (f : ι → Circuit n)
    (xs : List ι) (hx : xs.Nodup) (t : ι) (ht : t∈xs) (v w : Bits n → ℂ)
    (hmain : run (f t) v=w)
    (hfixv : ∀ i∈xs,i≠t → run (f i) v=v)
    (hfixw : ∀ i∈xs,i≠t → run (f i) w=w) : run (xs.flatMap f) v=w := by
  induction xs with
  | nil => simp at ht
  | cons i xs ih =>
    rw [List.flatMap_cons,run_append]
    by_cases hi : i=t
    · subst i
      rw [hmain]
      apply run_flatMap_fixes
      intro j hj
      exact hfixw j (by simp [hj]) (fun h => (List.nodup_cons.mp hx).1 (h ▸ hj))
    · rw [hfixv i (by simp) hi]
      apply ih (List.nodup_cons.mp hx).2 (List.mem_of_ne_of_mem (Ne.symm hi) ht)
      · intro j hj;exact hfixv j (by simp [hj])
      · intro j hj;exact hfixw j (by simp [hj])

noncomputable def allBranchCircuit {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) : Circuit (2+q) :=
  (Finset.univ : Finset (Sym (Fin 4) (k+1))).toList.flatMap (branchCircuit enc)

/-- One fixed literal word compresses every actual normalized occupation
branch simultaneously, with no commutation or disjointness premise supplied. -/
theorem allBranchCircuit_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    run (allBranchCircuit enc) (encodedBranch enc ν)=Pi.single (pivotCoordinates enc ν) 1 := by
  apply run_flatMap_unique _ _ (Finset.nodup_toList _) ν (by simp)
    _ _ (branchCircuit_action enc ν)
  · intro μ hμ h
    exact branchCircuit_fixes_other enc ν μ (Ne.symm h)
  · intro μ hμ h
    exact branchCircuit_fixes_other_pivot enc ν μ (Ne.symm h)

theorem allBranchCircuit_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    (allBranchCircuit enc).length≤occupationRank (k+1)*(60*(2+q)^2*2^(2+q)) := by
  unfold allBranchCircuit
  rw [List.length_flatMap]
  calc
    _ ≤ (((Finset.univ : Finset (Sym (Fin 4) (k+1))).toList).map
        (fun _ => 60*(2+q)^2*2^(2+q))).sum := by
      apply List.sum_le_sum
      intro ν hν
      exact branchCircuit_length enc ν
    _ = _ := by simp [occupationRank_card]

end CircuitCompletion
