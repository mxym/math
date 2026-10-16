import CircuitCompletion.Hadamard
import CircuitCompletion.FidelityError
import CircuitCompletion.TrailingSpectators

open scoped BigOperators
namespace CircuitCompletion

def zeroBits (n : ℕ) : Bits n := fun _ => false

theorem zeroBits_two_iff (w : Bits 2) : w=zeroBits 2 ↔ w 0=false ∧ w 1=false := by
  constructor
  · intro h;subst w;exact ⟨rfl,rfl⟩
  · intro h
    funext i
    fin_cases i
    · exact h.1
    · exact h.2

noncomputable def bellPreparationWord : Circuit 2 :=
  [Gate.single 0 hadamard,Gate.cnot 0 1 (by decide)]

theorem bellPreparationWord_action :
    run bellPreparationWord (Pi.single (zeroBits 2) 1)=
      fun w => Extraction.bellVector (d := Bool) (invSqrtTwo : ℂ) (w 0,w 1) := by
  change run ([Gate.single (0 : Fin 2) hadamard]++[Gate.cnot (0 : Fin 2) 1 (by decide)]) _=_
  rw [run_append,run_singleton,cnot_action,run_hadamard]
  funext w
  have hz (u : Bits 2) : zeroBits 2=u ↔ u 0=false ∧ u 1=false := by
    rw [eq_comm];exact zeroBits_two_iff u
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    simp [cnotFunction,Pi.single_apply,hz,zeroBits_two_iff,Extraction.bellVector,h0,h1]

theorem bellPreparationWord_length : bellPreparationWord.length=2 := rfl

/-- Bell preparation uses two existing zero wires while preserving an
arbitrary original spectator vector, with an actual two-gate word. -/
theorem bellPreparation_with_spectators (r : ℕ) (z : Bits r → ℂ) :
    run (liftCircuit r bellPreparationWord)
      (fun w => (Pi.single (zeroBits 2) 1 : Bits 2 → ℂ) (prefixBits w)*z (suffixBits w))=
      fun w => Extraction.bellVector (d := Bool) (invSqrtTwo : ℂ)
        ((prefixBits w) 0,(prefixBits w) 1)*z (suffixBits w) := by
  rw [run_liftCircuit,bellPreparationWord_action]

def bitPair : Bits 2 ≃ Bool×Bool where
  toFun w := (w 0,w 1)
  invFun p := ![p.1,p.2]
  left_inv w := by funext i;fin_cases i <;> rfl
  right_inv p := by cases p;rfl

theorem invSqrtTwo_bellCoeff : (invSqrtTwo : ℂ)=Extraction.bellCoeff Bool := by
  have hs : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have he : Real.sqrt 2/2=1/Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  simpa only [invSqrtTwo,Extraction.bellCoeff,Fintype.card_bool,Nat.cast_ofNat] using
    congrArg Complex.ofReal he

theorem bellPreparationWord_density :
    Matrix.reindex bitPair bitPair
      (pureMatrix (run bellPreparationWord (Pi.single (zeroBits 2) 1)))=
      Extraction.bellProjector (d := Bool) := by
  rw [bellPreparationWord_action]
  ext p q
  simp [Matrix.reindex_apply,pureMatrix,Matrix.vecMulVec_apply,bitPair,
    Extraction.bellProjector,invSqrtTwo_bellCoeff]

end CircuitCompletion
