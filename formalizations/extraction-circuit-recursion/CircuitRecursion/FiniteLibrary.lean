import CircuitRecursion.NormalizedWord

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def libraryWireCircuit {m n : ℕ} (G : Fin m → SU2) (i : Fin n) :
    List (Fin m) → Circuit n
  | [] => []
  | j::w => Gate.single i (su2ToBool (G j))::libraryWireCircuit G i w

theorem libraryWireCircuit_value {m n : ℕ} (G : Fin m → SU2) (i : Fin n) (w : List (Fin m)) :
    denote (libraryWireCircuit G i w)=singleWire i (su2ToBool (instructionWordValue G w)) := by
  induction w with
  | nil =>
    apply Subtype.ext
    change (1 : Matrix (Bits n) (Bits n) ℂ)=
      wireStarAlgHom i (Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [map_one,map_one]
  | cons j w ih =>
    rw [libraryWireCircuit,denote_cons,ih]
    apply Subtype.ext
    change wireStarAlgHom i (Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv (instructionWordValue G w).val)*
      wireStarAlgHom i (Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv (G j).val)=
      wireStarAlgHom i (Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv
        ((instructionWordValue G w).val*(G j).val))
    rw [map_mul,map_mul]

theorem libraryWireCircuit_length {m n : ℕ} (G : Fin m → SU2) (i : Fin n) (w : List (Fin m)) :
    (libraryWireCircuit G i w).length=w.length := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [libraryWireCircuit,List.length_cons,ih]

def usesFiniteLibrary {m n : ℕ} (G : Fin m → SU2) : Gate n → Prop
  | .single _ U => ∃ j,U=su2ToBool (G j)
  | .cnot _ _ _ => True

theorem libraryWireCircuit_uses {m n : ℕ} (G : Fin m → SU2) (i : Fin n) (w : List (Fin m)) :
    ∀ g∈libraryWireCircuit G i w,usesFiniteLibrary G g := by
  induction w with
  | nil => simp [libraryWireCircuit]
  | cons j w ih =>
    intro g hg
    rcases List.mem_cons.mp hg with he|hg
    · subst g; exact ⟨j,rfl⟩
    · exact ih g hg

noncomputable def libraryGateCompiler {m n : ℕ} (G : Fin m → SU2)
    (approx : SU2 → List (Fin m)) : Gate n → Circuit n
  | .single i U => libraryWireCircuit G i (approx (qubitRepresentative U).2)
  | .cnot c t h => [Gate.cnot c t h]

theorem libraryGateCompiler_error {m n : ℕ} (G : Fin m → SU2) (approx : SU2 → List (Fin m))
    (ε : ℝ) (hε : 0≤ε)
    (heach : ∀ U,‖U.val-(instructionWordValue G (approx U)).val‖≤ε) (g : Gate n) :
    ‖(denote (libraryGateCompiler G approx g) : Matrix (Bits n) (Bits n) ℂ)-
      (normalizedGate g).denote‖≤ε := by
  cases g with
  | single i U =>
    rw [libraryGateCompiler,libraryWireCircuit_value]
    change ‖(singleWire i (su2ToBool (instructionWordValue G (approx (qubitRepresentative U).2))) :
      Matrix (Bits n) (Bits n) ℂ)-singleWire i (su2ToBool (qubitRepresentative U).2)‖≤ε
    apply (singleWire_error i _ _).trans
    rw [su2ToBool_error,norm_sub_rev]
    exact heach _
  | cnot c t h => simp [libraryGateCompiler,normalizedGate,denote,hε]

theorem libraryGateCompiler_length {m n : ℕ} (G : Fin m → SU2) (approx : SU2 → List (Fin m))
    (L : ℕ) (hL : 1≤L) (heach : ∀ U,(approx U).length≤L) (g : Gate n) :
    (libraryGateCompiler G approx g).length≤L := by
  cases g with
  | single i U => simpa only [libraryGateCompiler,libraryWireCircuit_length] using heach (qubitRepresentative U).2
  | cnot c t h => exact hL

theorem libraryGateCompiler_uses {m n : ℕ} (G : Fin m → SU2) (approx : SU2 → List (Fin m))
    (g : Gate n) : ∀ f∈libraryGateCompiler G approx g,usesFiniteLibrary G f := by
  cases g with
  | single i U => exact libraryWireCircuit_uses G i _
  | cnot c t h => simp [libraryGateCompiler,usesFiniteLibrary]

/-- Any literal original-wire circuit admits finite-library replacement with
the SK precision overhead. Every output gate is actually in G or is a CNOT;
the total phase, matrix error and actual word length are all retained. -/
theorem finiteLibrary_wordApproximation {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ C : ℕ,1≤C ∧ ∀ (n : ℕ) (a : Circuit n) (p : ℕ),∃ b : Circuit n,
      (∀ g∈b,usesFiniteLibrary G g) ∧
      b.length≤C*a.length*(p+1)^5 ∧
      ‖(denote a : Matrix (Bits n) (Bits n) ℂ)-circuitPhase a •
        (denote b : Matrix (Bits n) (Bits n) ℂ)‖≤a.length*(1/2 : ℝ)^p := by
  classical
  obtain ⟨C,hC⟩ := su2_synthesis_dyadic G hinv huniversal
  refine ⟨max 1 C,le_max_left _ _,fun n a p => ?_⟩
  let approx (U : SU2) := Classical.choose (hC p U)
  let L := max 1 C*(p+1)^5
  have hL : 1≤L := by
    have hCpos : 0<max 1 C := by omega
    dsimp [L]
    apply Nat.succ_le_iff.mpr
    positivity
  have hlen : ∀ U,(approx U).length≤L := fun U =>
    (Classical.choose_spec (hC p U)).1.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
  have herr : ∀ U,‖U.val-(instructionWordValue G (approx U)).val‖≤(1/2 : ℝ)^p :=
    fun U => (Classical.choose_spec (hC p U)).2
  let compile : Gate n → Circuit n := libraryGateCompiler G approx
  refine ⟨a.flatMap compile,?_,?_,?_⟩
  · intro g hg
    obtain ⟨f,hf,hg⟩ := List.mem_flatMap.mp hg
    exact libraryGateCompiler_uses G approx f g hg
  · rw [compiled_word_length]
    have ht := List.sum_le_length_nsmul (a.map (fun g => (compile g).length)) L (by
      intro x hx
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
      exact libraryGateCompiler_length G approx L hL hlen g)
    have hs : (a.map (fun g => (compile g).length)).sum≤a.length*L := by
      simpa [List.length_map,nsmul_eq_mul] using ht
    simpa only [L,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs
  · exact normalized_word_uniform_error compile a _
      (fun g _ => libraryGateCompiler_error G approx _ (by positivity) herr g)

/-- The actual full extraction family now has finite-library approximants
with the same original 2k wires and the same physical local discard channel. -/
theorem finiteLibrary_extraction_dyadic {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ C : ℕ,∀ k p : ℕ,∃ b : Circuit (originalWireCount k),
      (∀ g∈b,usesFiniteLibrary G g) ∧
      b.length≤C*recursiveGateBudget k*(p+1)^5 ∧
      (∀ z : Fin 4 → ℂ,IsUnitVector z →
        1-2*((extractionCircuit k).length*(1/2 : ℝ)^p)≤
          (Extraction.bellProjector (d := Bits (bellPairYield k))*
            approximateExtractionOutput k (denote b) (pureMatrix (bitPurePower k z))).trace.re) := by
  obtain ⟨C,hC,ha⟩ := finiteLibrary_wordApproximation G hinv huniversal
  refine ⟨C,fun k p => ?_⟩
  obtain ⟨b,huses,hlen,herr⟩ := ha (originalWireCount k) (extractionCircuit k) p
  refine ⟨b,huses,hlen.trans ?_,?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (extractionCircuit_length k))
  · intro z hz
    exact extractionOutput_robust_up_to_phase k (denote b) z hz _ (by positivity)
      (circuitPhase (extractionCircuit k)) (circuitPhase_normalized _) herr

end CircuitRecursion
