import CircuitRecursion.Expansion
import CircuitCompletion.Budget

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

theorem active_available (k : ℕ) : 2+codeWires k≤originalWireCount (k+1) := by
  change 2+codeWires k≤2+originalWireCount k
  exact Nat.add_le_add_left (codeWires_available k) 2

/-- This is a literal word on the original register. Only the fresh pair
and the compact old code participate in the new occupation step. -/
noncomputable def stageCircuit (k : ℕ) : Circuit (originalWireCount (k+1)) :=
  prefixCircuit (active_available k)
    (occupationStepCircuit (compactEncoding k) (nextEncoding k))

theorem stageCircuit_action (k : ℕ) (ν : Sym (Fin 4) (k+1)) :
    run (stageCircuit k) (encodedBranch (originalEncoding k) ν)=
      Pi.single (originalEncoding (k+1) ν) 1 := by
  rw [originalEncoding,encodedBranch_extend]
  unfold stageCircuit
  erw [prefixCircuit_action,occupationStepCircuit_action,coordinateIsometry_single]
  congr 1
  change extendBits (active_available k)
    (extendBits (codeWires_step k) (compactEncoding (k+1) ν))=
    extendBits (codeWires_available (k+1)) (compactEncoding (k+1) ν)
  exact extendBits_trans _ _ _

/-- The same, input-independent circuit is defined for every block length.
Every successor first executes the old word on the original suffix. -/
noncomputable def compressionCircuit : (k : ℕ) → Circuit (originalWireCount k)
  | 0 => []
  | k+1 => (show Circuit (originalWireCount (k+1)) from
      shiftCircuit 2 (compressionCircuit k))++stageCircuit k

theorem bitOccupation_zero (ν : Sym (Fin 4) 0) :
    bitOccupation ν=Pi.single (originalEncoding 0 ν) 1 := by
  classical
  have he : ∀ w : Word 4 0,occupation 4 0 w=ν := fun _ => Subsingleton.elim _ _
  funext w
  have hw : originalEncoding 0 ν=w := by funext i; exact Fin.elim0 i
  simp [bitOccupation,occupationVector,he,fiberCard,Word,Pi.single_apply,hw]

/-- Full coherent all-k compression of the actual normalized occupation
basis on exactly the original 2k qubits, with no supplied zero ancillas. -/
theorem compressionCircuit_action (k : ℕ) (ν : Sym (Fin 4) k) :
    run (compressionCircuit k) (bitOccupation ν)=Pi.single (originalEncoding k ν) 1 := by
  induction k with
  | zero => simpa [compressionCircuit,run,denote] using bitOccupation_zero ν
  | succ k ih =>
    rw [compressionCircuit,run_append]
    erw [shifted_occupation (originalEncoding k) (compressionCircuit k) ih,
      stageCircuit_action]

theorem stageCircuit_length (k : ℕ) : (stageCircuit k).length≤stageGateBudget k := by
  rw [stageCircuit,prefixCircuit_length]
  have he : 2+codeWires k=activeWires k := by unfold codeWires activeWires; omega
  simpa only [stageGateBudget,he] using
    occupationStepCircuit_length (compactEncoding k) (nextEncoding k)

/-- This bound concerns the actual recursively assembled list, rather than
an unbound sum of hypothetical one-step budgets. -/
theorem compressionCircuit_length (k : ℕ) :
    (compressionCircuit k).length≤∑ j∈Finset.range k,stageGateBudget j := by
  induction k with
  | zero => simp [compressionCircuit]
  | succ k ih =>
    rw [compressionCircuit]
    erw [List.length_append,shiftCircuit_length,Finset.sum_range_succ]
    exact Nat.add_le_add ih (stageCircuit_length k)

theorem compressionCircuit_polynomial_bound (k : ℕ) :
    (compressionCircuit k).length≤
      20480*k*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2+100*k^2 := by
  exact (compressionCircuit_length k).trans
    ((Nat.le_add_right _ _).trans (recursiveGateBudget_bound k))

end CircuitRecursion
