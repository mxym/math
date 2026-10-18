import EffectiveEncoding.Normalized
import CircuitRecursion.FiniteLibrary
import CircuitRecursion.Robustness

open scoped BigOperators Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- A finite-library output instruction contains only a dictionary label
and an original-wire index, or an original-wire CNOT. -/
inductive LabelGate (m n : ℕ) where
  | single (wire : Fin n) (label : Fin m)
  | cnot (control target : Fin n) (hne : control≠target)

noncomputable def LabelGate.value {m n : ℕ} (G : Fin m → SU2) : LabelGate m n → Gate n
  | .single i j => .single i (su2ToBool (G j))
  | .cnot c t h => .cnot c t h

noncomputable def labelCircuit {m n : ℕ} (G : Fin m → SU2) (w : List (LabelGate m n)) : Circuit n :=
  w.map (LabelGate.value G)

def wireLabels {m n : ℕ} (i : Fin n) (w : List (Fin m)) : List (LabelGate m n) :=
  w.map (.single i)

theorem wireLabels_value {m n : ℕ} (G : Fin m → SU2) (i : Fin n) (w : List (Fin m)) :
    labelCircuit G (wireLabels i w)=libraryWireCircuit G i w := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change Gate.single i (su2ToBool (G j))::labelCircuit G (wireLabels i w)=
      Gate.single i (su2ToBool (G j))::libraryWireCircuit G i w
    exact congrArg (List.cons (Gate.single i (su2ToBool (G j)))) ih

def compileLabels {m n : ℕ} (synth : SingleCode → List (Fin m)) : GateCode n → List (LabelGate m n)
  | .single i u => wireLabels i (synth u)
  | .cnot c t h => [.cnot c t h]

def compileLabelWord {m n : ℕ} (synth : SingleCode → List (Fin m)) (w : WordCode n) :
    List (LabelGate m n) := w.flatMap (compileLabels synth)

theorem labelCircuit_flatMap {α : Type*} {m n : ℕ} (G : Fin m → SU2)
    (w : List α) (f : α → List (LabelGate m n)) :
    labelCircuit G (w.flatMap f)=w.flatMap (fun g => labelCircuit G (f g)) := by
  simp only [labelCircuit,List.map_flatMap]

theorem labelCircuit_uses {m n : ℕ} (G : Fin m → SU2) (w : List (LabelGate m n)) :
    ∀ g∈labelCircuit G w,usesFiniteLibrary G g := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  cases a with
  | single i j => exact ⟨j,rfl⟩
  | cnot c t h => trivial

theorem compileLabels_error {m n : ℕ} (G : Fin m → SU2)
    (synth : SingleCode → List (Fin m)) (ε : ℝ) (hε : 0≤ε)
    (he : ∀ u,unitaryDistance (su2AsUnitary u.representative)
      (su2AsUnitary (instructionWordValue G (synth u)))≤ε) (g : GateCode n) :
    ‖(denote (labelCircuit G (compileLabels synth g)) : Matrix (Bits n) (Bits n) ℂ)-
      g.representative.denote‖≤ε := by
  cases g with
  | single i u =>
    rw [compileLabels,wireLabels_value,libraryWireCircuit_value]
    change ‖(singleWire i (su2ToBool (instructionWordValue G (synth u))) :
      Matrix (Bits n) (Bits n) ℂ)-singleWire i (su2ToBool u.representative)‖≤ε
    apply (singleWire_error i _ _).trans
    rw [su2ToBool_error,norm_sub_rev]
    exact he u
  | cnot c t h =>
    simp [compileLabels,labelCircuit,LabelGate.value,GateCode.representative,denote,hε]

theorem compileLabelWord_error {m n : ℕ} (G : Fin m → SU2)
    (synth : SingleCode → List (Fin m)) (w : WordCode n) (ε : ℝ) (hε : 0≤ε)
    (he : ∀ u,unitaryDistance (su2AsUnitary u.representative)
      (su2AsUnitary (instructionWordValue G (synth u)))≤ε) :
    ‖(denote (interpret w) : Matrix (Bits n) (Bits n) ℂ)-wordPhase w •
      (denote (labelCircuit G (compileLabelWord synth w)) : Matrix (Bits n) (Bits n) ℂ)‖≤
        w.length*ε := by
  rw [compileLabelWord,labelCircuit_flatMap]
  exact descriptor_word_uniform_error _ w ε (by intro g hg;exact compileLabels_error G synth ε hε he g)

theorem compileLabels_length {m n : ℕ} (synth : SingleCode → List (Fin m))
    (L : ℕ) (hL : 1≤L) (hs : ∀ u,(synth u).length≤L) (g : GateCode n) :
    (compileLabels synth g).length≤L := by
  cases g with
  | single i u => simpa [compileLabels,wireLabels] using hs u
  | cnot c t h => exact hL

theorem compileLabelWord_length {m n : ℕ} (synth : SingleCode → List (Fin m))
    (L : ℕ) (hL : 1≤L) (hs : ∀ u,(synth u).length≤L) (w : WordCode n) :
    (compileLabelWord synth w).length≤w.length*L := by
  unfold compileLabelWord
  rw [List.length_flatMap]
  calc
    _ ≤ (w.map (fun _ => L)).sum := by
      apply List.sum_le_sum
      intro g hg
      exact compileLabels_length synth L hL hs g
    _ = _ := by simp

theorem extractionOutput_fidelity_one (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    (Extraction.bellProjector (d := Bits (bellPairYield k))*
      extractionOutput k (pureMatrix (bitPurePower k z))).trace.re=1 := by
  rw [extractionOutput_purePower k z hz]
  change (Extraction.bellProjector (d := Bits (bellPairYield k))*Extraction.bellProjector).trace.re=1
  rw [Extraction.bellProjector_idempotent]
  exact congrArg Complex.re (Extraction.bellProjector_density (d := Bits (bellPairYield k))).2

theorem extractionOutput_robust (k : ℕ)
    (V : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ)
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) (δ : ℝ) (hδ : 0≤δ)
    (hUV : ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-V‖≤δ) :
    1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k V (pureMatrix (bitPurePower k z))).trace.re := by
  have hpre (W : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ) :
      (discardEffect k*pureMatrix ((W : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)*ᵥbitPurePower k z)).trace.re=
      (Extraction.bellProjector (d := Bits (bellPairYield k))*
        approximateExtractionOutput k W (pureMatrix (bitPurePower k z))).trace.re := by
    rw [discardEffect_pairing]
    have hc : pureMatrix ((W : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)*ᵥbitPurePower k z)=
        (W : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)*
          pureMatrix (bitPurePower k z)*(W : Matrix (Bits (originalWireCount k))
            (Bits (originalWireCount k)) ℂ)ᴴ := (Extraction.congruence_pure _ _).symm
    rw [hc]
    rfl
  have hb := discardEffect_bounds k
  have hz' := bitPurePower_square k z hz
  rw [← hpre V]
  apply exact_effect_fidelity_lower_delta (discardEffect k) hb.1 hb.2 _ _
    ((vectorSquare_unitary (denote (extractionCircuit k)) _).trans hz')
    ((vectorSquare_unitary V _).trans hz') ?_ δ hδ
    (operator_error_controls_vector _ _ _ hz' δ hδ hUV)
  rw [hpre]
  exact extractionOutput_fidelity_one k z hz

theorem extractionOutput_robust_up_to_phase (k : ℕ)
    (V : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ)
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) (δ : ℝ) (hδ : 0≤δ)
    (c : ℂ) (hc : Complex.normSq c=1)
    (hUV : ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-c • (V : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)‖≤δ) :
    1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k V (pureMatrix (bitPurePower k z))).trace.re := by
  have ht := extractionOutput_robust k (phaseUnitary c hc V) z hz δ hδ hUV
  simpa only [approximateExtractionOutput,phaseUnitary_congruence] using ht

/-- The actual finite-label output is related to the exact generated word
and the same physical local discard, uniformly over the unknown pure input. -/
theorem finiteLabels_fidelity {m : ℕ} (G : Fin m → SU2)
    (synth : SingleCode → List (Fin m)) (k : ℕ) (ε : ℝ) (hε : 0≤ε)
    (he : ∀ u,unitaryDistance (su2AsUnitary u.representative)
      (su2AsUnitary (instructionWordValue G (synth u)))≤ε)
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-2*((extractionCode k).length*ε)≤
      (Extraction.bellProjector (d := Bits (bellPairYield k))*
        approximateExtractionOutput k
          (denote (labelCircuit G (compileLabelWord synth (extractionCode k))))
          (pureMatrix (bitPurePower k z))).trace.re := by
  exact extractionOutput_robust_up_to_phase k _ z hz _ (by positivity)
    (wordPhase (extractionCode k)) (wordPhase_norm _)
    (compileLabelWord_error G synth (extractionCode k) ε hε he)

end EffectiveEncoding

