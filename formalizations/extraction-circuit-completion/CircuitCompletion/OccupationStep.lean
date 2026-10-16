import CircuitCompletion.OccupationCircuits
import CircuitCompletion.EmbeddingPermutation

open scoped BigOperators
open Matrix
namespace CircuitCompletion

noncomputable def pivotEmbedding {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    Sym (Fin 4) (k+1) ↪ Bits (2+q) := ⟨pivotCoordinates enc,pivotCoordinates_injective enc⟩

/-- The actual elementary one-step occupation compressor, including a
permutation completion to the prescribed next code and no supplied ancilla. -/
noncomputable def occupationStepCircuit {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : Circuit (2+q) :=
  allBranchCircuit enc++permutationWord (by omega) (embeddingPermutation (pivotEmbedding enc) next)

theorem occupationStepCircuit_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) (ν : Sym (Fin 4) (k+1)) :
    run (occupationStepCircuit enc next) (encodedBranch enc ν)=Pi.single (next ν) 1 := by
  rw [occupationStepCircuit,run_append,allBranchCircuit_action]
  exact embeddingPermutation_word (by omega) (pivotEmbedding enc) next ν 1

theorem branchRank_le_active_dimension {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    occupationRank (k+1)≤2^(2+q) := by
  have h := Fintype.card_le_of_injective (pivotCoordinates enc) (pivotCoordinates_injective enc)
  simpa [occupationRank_card,Bits] using h

theorem occupationStepCircuit_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    (occupationStepCircuit enc next).length≤80*(2+q)^2*(2^(2+q))^2 := by
  have h1 := allBranchCircuit_length enc
  have h2 := permutationWord_length (by omega : 0<2+q) (embeddingPermutation (pivotEmbedding enc) next)
  have hr := Nat.mul_le_mul_right (60*(2+q)^2*2^(2+q)) (branchRank_le_active_dimension enc)
  simp only [occupationStepCircuit,List.length_append]
  nlinarith

noncomputable def branchMatrix {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    Matrix (Bits (2+q)) (Sym (Fin 4) (k+1)) ℂ := fun w ν => encodedBranch enc ν w

/-- The simultaneously verified action is an actual matrix identity for
all normalized occupation columns, not a block-decomposition assumption. -/
theorem occupationStepCircuit_matrix {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    (denote (occupationStepCircuit enc next) : Matrix (Bits (2+q)) (Bits (2+q)) ℂ)*
      branchMatrix enc=Extraction.coordinateIsometry next := by
  ext w ν
  have h := congrFun (occupationStepCircuit_action enc next ν) w
  simpa only [run,branchMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,
    Extraction.coordinateIsometry,Pi.single_apply,eq_comm] using h

theorem branchMatrix_isometry {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : (branchMatrix enc)ᴴ*branchMatrix enc=1 := by
  let U := denote (occupationStepCircuit enc next)
  have hU : (U : Matrix (Bits (2+q)) (Bits (2+q)) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have h := Extraction.coordinateIsometry_isometry next
  rw [← occupationStepCircuit_matrix enc next] at h
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc] at h
  change (branchMatrix enc)ᴴ*((U : Matrix (Bits (2+q)) (Bits (2+q)) ℂ)ᴴ*
    ((U : Matrix (Bits (2+q)) (Bits (2+q)) ℂ)*branchMatrix enc))=1 at h
  rw [← Matrix.mul_assoc (U : Matrix (Bits (2+q)) (Bits (2+q)) ℂ)ᴴ,hU,
    Matrix.one_mul] at h
  exact h

end CircuitCompletion
