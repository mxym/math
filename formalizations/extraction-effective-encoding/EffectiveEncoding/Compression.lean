import EffectiveEncoding.Occupation
import CircuitRecursion.Compression
import CircuitRecursion.PureInput

open scoped BigOperators
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 800000

theorem interpret_flatMap {ι : Type*} {n : ℕ} (xs : List ι) (f : ι → WordCode n) :
    interpret (xs.flatMap f)=xs.flatMap (fun i => interpret (f i)) := by
  simp only [interpret,List.map_flatMap]

def allBranchCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) : WordCode (2+q) :=
  (occupations (k+1)).flatMap (branchCode enc)

theorem allBranchCode_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    run (interpret (allBranchCode enc)) (encodedBranch enc ν)=
      Pi.single (pivotCoordinates enc ν) 1 := by
  rw [allBranchCode,interpret_flatMap]
  refine run_flatMap_unique
    (fun μ : Sym (Fin 4) (k+1) => interpret (branchCode enc μ))
    (occupations (k+1)) (occupations_nodup (k+1)) ν (mem_occupations ν)
    (encodedBranch enc ν) (Pi.single (pivotCoordinates enc ν) 1)
    (branchCode_action enc ν) ?_ ?_
  · intro μ hμ h
    exact branchCode_fixes_other enc ν μ (Ne.symm h)
  · intro μ hμ h
    exact branchCode_fixes_other_pivot enc ν μ (Ne.symm h)

theorem allBranchCode_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    (allBranchCode enc).length≤occupationRank (k+1)*(60*(2+q)^2*2^(2+q)) := by
  unfold allBranchCode
  rw [List.length_flatMap]
  calc
    _ ≤ ((occupations (k+1)).map (fun _ => 60*(2+q)^2*2^(2+q))).sum := by
      apply List.sum_le_sum
      intro ν hν
      exact branchCode_length enc ν
    _ = _ := by simp [occupations_length]

def occupationStepCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : WordCode (2+q) :=
  allBranchCode enc++
    alignmentCode (by omega) (pivotEmbedding enc) next (occupations (k+1)) 1

theorem occupationStepCode_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) (ν : Sym (Fin 4) (k+1)) :
    run (interpret (occupationStepCode enc next)) (encodedBranch enc ν)=
      Pi.single (next ν) 1 := by
  rw [occupationStepCode,interpret_append,run_append,allBranchCode_action]
  exact alignmentCode_on_embedding (by omega) (pivotEmbedding enc) next _
    mem_occupations ν 1

theorem occupationStepCode_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    (occupationStepCode enc next).length≤80*(2+q)^2*(2^(2+q))^2 := by
  have h1 := allBranchCode_length enc
  have h2 := alignmentCode_length (by omega) (pivotEmbedding enc) next (occupations (k+1)) 1
  rw [occupations_length] at h2
  have hr := Nat.mul_le_mul_right (80*(2+q)^2*2^(2+q)) (branchRank_le_active_dimension enc)
  simp only [occupationStepCode,List.length_append]
  nlinarith

def GateCode.extend {q n : ℕ} (h : q≤n) : GateCode q → GateCode n
  | .single i u => .single (Fin.castLE h i) u
  | .cnot c t hct => .cnot (Fin.castLE h c) (Fin.castLE h t)
      (fun he => hct (Fin.ext (congrArg (fun x : Fin n => x.val) he)))

def prefixCode {q n : ℕ} (h : q≤n) (xs : WordCode q) : WordCode n :=
  xs.map (GateCode.extend h)

@[simp] theorem prefixCode_length {q n : ℕ} (h : q≤n) (xs : WordCode q) :
    (prefixCode h xs).length=xs.length := List.length_map _

@[simp] theorem interpret_prefix {q n : ℕ} (h : q≤n) (xs : WordCode q) :
    interpret (prefixCode h xs)=prefixCircuit h (interpret xs) := by
  unfold interpret prefixCode prefixCircuit
  simp only [List.map_map]
  apply List.map_congr_left
  intro g hg
  cases g <;> rfl

def GateCode.shift {q : ℕ} (s : ℕ) : GateCode q → GateCode (s+q)
  | .single i u => .single (Fin.natAdd s i) u
  | .cnot c t hct => .cnot (Fin.natAdd s c) (Fin.natAdd s t)
      (fun he => hct (Fin.ext (by
        have h := congrArg (fun x : Fin (s+q) => x.val) he
        simpa using h)))

def shiftCode {q : ℕ} (s : ℕ) (xs : WordCode q) : WordCode (s+q) :=
  xs.map (GateCode.shift s)

@[simp] theorem shiftCode_length {q : ℕ} (s : ℕ) (xs : WordCode q) :
    (shiftCode s xs).length=xs.length := List.length_map _

@[simp] theorem interpret_shift {q : ℕ} (s : ℕ) (xs : WordCode q) :
    interpret (shiftCode s xs)=shiftCircuit s (interpret xs) := by
  unfold interpret shiftCode shiftCircuit
  simp only [List.map_map]
  apply List.map_congr_left
  intro g hg
  cases g <;> rfl

def stageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k)
    (occupationStepCode (compactEncoding k) (nextEncoding k))

noncomputable def stageCircuit (k : ℕ) : Circuit (originalWireCount (k+1)) :=
  interpret (stageCode k)

theorem stageCircuit_action (k : ℕ) (ν : Sym (Fin 4) (k+1)) :
    run (stageCircuit k) (encodedBranch (originalEncoding k) ν)=
      Pi.single (originalEncoding (k+1) ν) 1 := by
  rw [originalEncoding,encodedBranch_extend]
  unfold stageCircuit stageCode
  erw [interpret_prefix,prefixCircuit_action,occupationStepCode_action,coordinateIsometry_single]
  congr 1
  exact extendBits_trans (codeWires_step k) (active_available k) _

def compressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (compressionCode k))++stageCode k

noncomputable def compressionCircuit (k : ℕ) : Circuit (originalWireCount k) :=
  interpret (compressionCode k)

theorem compressionCircuit_succ (k : ℕ) :
    compressionCircuit (k+1)=
      (show Circuit (originalWireCount (k+1)) from shiftCircuit 2 (compressionCircuit k))++
        stageCircuit k := by
  unfold compressionCircuit
  rw [compressionCode,interpret_append]
  erw [interpret_shift]
  rfl

theorem bitOccupation_zero (ν : Sym (Fin 4) 0) :
    bitOccupation ν=Pi.single (originalEncoding 0 ν) 1 := by
  classical
  have he : ∀ w : Word 4 0,occupation 4 0 w=ν := fun _ => Subsingleton.elim _ _
  funext w
  have hw : originalEncoding 0 ν=w := by funext i; exact Fin.elim0 i
  simp [bitOccupation,occupationVector,he,fiberCard,Word,Pi.single_apply,hw]

/-- A generated finite description acts on exactly the original 2k wires
and compresses every actual occupation basis vector into the explicit code. -/
theorem compressionCircuit_action (k : ℕ) (ν : Sym (Fin 4) k) :
    run (compressionCircuit k) (bitOccupation ν)=Pi.single (originalEncoding k ν) 1 := by
  induction k with
  | zero => simpa [compressionCircuit,compressionCode,interpret,run,denote] using bitOccupation_zero ν
  | succ k ih =>
    rw [compressionCircuit_succ,run_append]
    have hs := shifted_occupation (k:=k) (originalEncoding k) (compressionCircuit k) ih ν
    exact (congrArg (run (stageCircuit k)) hs).trans (stageCircuit_action k ν)

theorem stageCode_length (k : ℕ) : (stageCode k).length≤stageGateBudget k := by
  rw [stageCode,prefixCode_length]
  have he : 2+codeWires k=activeWires k := by unfold codeWires activeWires;omega
  simpa only [stageGateBudget,he] using
    occupationStepCode_length (compactEncoding k) (nextEncoding k)

theorem compressionCode_length (k : ℕ) :
    (compressionCode k).length≤∑ j∈Finset.range k,stageGateBudget j := by
  induction k with
  | zero => simp [compressionCode]
  | succ k ih =>
    rw [compressionCode]
    erw [List.length_append,shiftCode_length,Finset.sum_range_succ]
    exact Nat.add_le_add ih (stageCode_length k)

theorem compressionCircuit_matrix (k : ℕ) :
    (denote (compressionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)*bitOccupationMatrix k=
        Extraction.coordinateIsometry (originalEncoding k) := by
  ext b ν
  have h := congrFun (compressionCircuit_action k ν) b
  simpa only [run,bitOccupationMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,
    Extraction.coordinateIsometry,Pi.single_apply,eq_comm] using h

theorem compressionCircuit_coherent (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    run (compressionCircuit k) (bitOccupationMatrix k*ᵥa)=
      Extraction.coordinateIsometry (originalEncoding k)*ᵥa := by
  change (denote (compressionCircuit k) : Matrix (Bits (originalWireCount k))
    (Bits (originalWireCount k)) ℂ)*ᵥ(bitOccupationMatrix k*ᵥa)=_
  rw [Matrix.mulVec_mulVec,compressionCircuit_matrix]

theorem compressionCircuit_purePower (k : ℕ) (z : Fin 4 → ℂ) :
    run (compressionCircuit k) (bitPurePower k z)=
      Extraction.coordinateIsometry (originalEncoding k)*ᵥpureOccupationCoefficients k z := by
  rw [← bitPurePower_expansion,compressionCircuit_coherent]

end EffectiveEncoding

