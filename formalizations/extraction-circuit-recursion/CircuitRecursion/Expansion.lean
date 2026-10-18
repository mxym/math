import CircuitRecursion.Prefix

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

theorem coordinateIsometry_single {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (x : α) (a : ℂ) :
    Extraction.coordinateIsometry e*ᵥPi.single x a=Pi.single (e x) a := by
  ext w
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,Extraction.coordinateIsometry]

theorem run_scalar {n : ℕ} (c : Circuit n) (a : ℂ) (v : Bits n → ℂ) :
    run c (fun b => a*v b)=fun b => a*run c v b := by
  ext w
  simp only [run,Matrix.mulVec,dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem run_zero {n : ℕ} (c : Circuit n) : run c (0 : Bits n → ℂ)=0 := by
  simp [run]

theorem encodedBranch_extend {k q n : ℕ} (h : q≤n) (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    encodedBranch (extendEmbedding h enc) ν=
      Extraction.coordinateIsometry (extendEmbedding (Nat.add_le_add_left h 2)
        (Function.Embedding.refl (Bits (2+q))))*ᵥencodedBranch enc ν := by
  classical
  simp only [encodedBranch]
  rw [coordinateIsometry_sum (branchEmbedding (extendEmbedding h enc) ν),
    coordinateIsometry_sum (branchEmbedding enc ν),Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateIsometry_single]
  congr 1
  exact (extendBits_append h (letterBits i.1) (enc (ν.erase i.1 i.2))).symm

theorem shifted_occupation {k : ℕ} (enc : Sym (Fin 4) k ↪ Bits (originalWireCount k))
    (c : Circuit (originalWireCount k))
    (hc : ∀ μ,run c (bitOccupation μ)=Pi.single (enc μ) 1)
    (ν : Sym (Fin 4) (k+1)) :
    run (shiftCircuit 2 c) (bitOccupation ν)=encodedBranch enc ν := by
  classical
  funext w
  obtain ⟨⟨x,b⟩,rfl⟩ := (splitRegister 2 (originalWireCount k)).symm.surjective w
  obtain ⟨i,rfl⟩ := letterBits.surjective x
  change run (shiftCircuit 2 c) (bitOccupation ν) (Fin.append (letterBits i) b)=
    encodedBranch enc ν (Fin.append (letterBits i) b)
  erw [run_shift_slice,encodedBranch_apply_append]
  simp only [bitOccupation_branch]
  by_cases hi : i∈ν
  · simp only [dif_pos hi]
    rw [run_scalar,hc]
  · simp only [dif_neg hi]
    exact congrFun (run_zero c) b

end CircuitRecursion
