import CircuitRecursion.QubitPhase

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix CircuitCompletion
namespace CircuitRecursion

theorem qubitRepresentative_exists (U : Matrix.unitaryGroup Bool ℂ) :
    ∃ p : ℂ×SU2,Complex.normSq p.1=1 ∧
      (U : Matrix Bool Bool ℂ)=p.1 • (su2ToBool p.2 : Matrix Bool Bool ℂ) := by
  obtain ⟨c,hc,V,he⟩ := qubit_phase_special U
  exact ⟨(c,V),hc,he⟩

noncomputable def qubitRepresentative (U : Matrix.unitaryGroup Bool ℂ) : ℂ×SU2 :=
  Classical.choose (qubitRepresentative_exists U)

theorem qubitRepresentative_spec (U : Matrix.unitaryGroup Bool ℂ) :
    Complex.normSq (qubitRepresentative U).1=1 ∧
      (U : Matrix Bool Bool ℂ)=(qubitRepresentative U).1 •
        (su2ToBool (qubitRepresentative U).2 : Matrix Bool Bool ℂ) :=
  Classical.choose_spec (qubitRepresentative_exists U)

noncomputable def normalizedGate {n : ℕ} : Gate n → Gate n
  | .single i U => .single i (su2ToBool (qubitRepresentative U).2)
  | .cnot c t h => .cnot c t h

noncomputable def gatePhase {n : ℕ} : Gate n → ℂ
  | .single _ U => (qubitRepresentative U).1
  | .cnot _ _ _ => 1

theorem gatePhase_normalized {n : ℕ} (g : Gate n) : Complex.normSq (gatePhase g)=1 := by
  cases g with
  | single i U => exact (qubitRepresentative_spec U).1
  | cnot c t h => simp [gatePhase]

theorem normalizedGate_phase {n : ℕ} (g : Gate n) :
    (g.denote : Matrix (Bits n) (Bits n) ℂ)=gatePhase g •
      ((normalizedGate g).denote : Matrix (Bits n) (Bits n) ℂ) := by
  cases g with
  | single i U => exact singleWire_phase i U _ _ (qubitRepresentative_spec U).2
  | cnot c t h => simp [gatePhase,normalizedGate]

noncomputable def circuitPhase {n : ℕ} (a : Circuit n) : ℂ := (a.map gatePhase).prod

theorem circuitPhase_normalized {n : ℕ} (a : Circuit n) : Complex.normSq (circuitPhase a)=1 := by
  induction a with
  | nil => simp [circuitPhase]
  | cons g a ih => simpa [circuitPhase,gatePhase_normalized] using ih

theorem normalizedCircuit_phase {n : ℕ} (a : Circuit n) :
    (denote a : Matrix (Bits n) (Bits n) ℂ)=circuitPhase a •
      (denote (a.map normalizedGate) : Matrix (Bits n) (Bits n) ℂ) := by
  induction a with
  | nil => simp [denote,circuitPhase]
  | cons g a ih =>
    simp only [denote_cons,List.map_cons,Matrix.UnitaryGroup.mul_val]
    rw [ih,normalizedGate_phase]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,circuitPhase,List.map_cons,List.prod_cons]

/-- Literal-word error telescoping against the normalized representatives,
retaining the original gate labels for their finite-library replacements. -/
theorem normalized_word_error {n : ℕ} (compile : Gate n → Circuit n) (a : Circuit n) :
    ‖(denote (a.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-denote (a.map normalizedGate)‖≤
      (a.map (fun g => ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-
        (normalizedGate g).denote‖)).sum := by
  induction a with
  | nil => simp [denote]
  | cons g a ih =>
    simp only [List.flatMap_cons,List.map_cons,denote_append,denote_cons,
      Matrix.UnitaryGroup.mul_val,List.sum_cons]
    have he :
        (denote (a.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)*denote (compile g)-
          (denote (a.map normalizedGate) : Matrix (Bits n) (Bits n) ℂ)*(normalizedGate g).denote=
        ((denote (a.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-denote (a.map normalizedGate))*
          denote (compile g)+(denote (a.map normalizedGate) : Matrix (Bits n) (Bits n) ℂ)*
            ((denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-(normalizedGate g).denote) := by
      noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
    simpa only [add_comm] using add_le_add_right ih
      ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-(normalizedGate g).denote‖

theorem normalized_word_uniform_error {n : ℕ} (compile : Gate n → Circuit n) (a : Circuit n)
    (ε : ℝ) (heach : ∀ g∈a,‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-
      (normalizedGate g).denote‖≤ε) :
    ‖(denote a : Matrix (Bits n) (Bits n) ℂ)-circuitPhase a •
      (denote (a.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)‖≤a.length*ε := by
  have hc : ‖circuitPhase a‖=1 := by
    have hs : ‖circuitPhase a‖^2=1 := (Complex.sq_norm _).trans (circuitPhase_normalized a)
    nlinarith [norm_nonneg (circuitPhase a)]
  rw [normalizedCircuit_phase,← smul_sub,norm_smul,hc,one_mul,norm_sub_rev]
  apply (normalized_word_error compile a).trans
  have ht := List.sum_le_length_nsmul
    (a.map (fun g => ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-(normalizedGate g).denote‖)) ε (by
      intro x hx
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
      exact heach g hg)
  simpa only [List.length_map,nsmul_eq_mul] using ht

end CircuitRecursion
