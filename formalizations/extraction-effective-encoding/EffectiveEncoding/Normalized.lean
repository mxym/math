import EffectiveEncoding.Representatives
import EffectiveEncoding.Extraction

open scoped BigOperators Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

noncomputable def GateCode.representative {n : ℕ} : GateCode n → Gate n
  | .single i u => .single i (su2ToBool u.representative)
  | .cnot c t h => .cnot c t h

noncomputable def GateCode.globalPhase {n : ℕ} : GateCode n → ℂ
  | .single _ u => u.globalPhase
  | .cnot _ _ _ => 1

theorem GateCode.globalPhase_norm {n : ℕ} (g : GateCode n) :
    Complex.normSq g.globalPhase=1 := by
  cases g with
  | single i u => exact u.globalPhase_norm
  | cnot c t h => simp [GateCode.globalPhase]

theorem GateCode.representative_spec {n : ℕ} (g : GateCode n) :
    (g.value.denote : Matrix (Bits n) (Bits n) ℂ)=g.globalPhase •
      (g.representative.denote : Matrix (Bits n) (Bits n) ℂ) := by
  cases g with
  | single i u => exact singleWire_phase i u.value _ _ u.representative_spec
  | cnot c t h => simp [GateCode.value,GateCode.globalPhase,GateCode.representative]

noncomputable def representativeCircuit {n : ℕ} (w : WordCode n) : Circuit n :=
  w.map GateCode.representative

noncomputable def wordPhase {n : ℕ} (w : WordCode n) : ℂ :=
  (w.map GateCode.globalPhase).prod

theorem wordPhase_norm {n : ℕ} (w : WordCode n) : Complex.normSq (wordPhase w)=1 := by
  induction w with
  | nil => simp [wordPhase]
  | cons g w ih => simpa [wordPhase,GateCode.globalPhase_norm] using ih

@[simp] theorem interpret_cons {n : ℕ} (g : GateCode n) (w : WordCode n) :
    interpret (g::w)=g.value::interpret w := rfl

@[simp] theorem representativeCircuit_cons {n : ℕ} (g : GateCode n) (w : WordCode n) :
    representativeCircuit (g::w)=g.representative::representativeCircuit w := rfl

/-- The product is the explicit phase belonging to every actual generated
gate, including all inverse nodes and original-wire CNOTs. -/
theorem representativeCircuit_phase {n : ℕ} (w : WordCode n) :
    (denote (interpret w) : Matrix (Bits n) (Bits n) ℂ)=wordPhase w •
      (denote (representativeCircuit w) : Matrix (Bits n) (Bits n) ℂ) := by
  induction w with
  | nil => simp [interpret,representativeCircuit,denote,wordPhase]
  | cons g w ih =>
    simp only [interpret_cons,representativeCircuit_cons,denote_cons,Matrix.UnitaryGroup.mul_val]
    rw [ih,GateCode.representative_spec]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      wordPhase,List.map_cons,List.prod_cons]

theorem descriptor_word_error {n : ℕ} (compile : GateCode n → Circuit n) (w : WordCode n) :
    ‖(denote (w.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-
        denote (representativeCircuit w)‖≤
      (w.map (fun g => ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-
        g.representative.denote‖)).sum := by
  induction w with
  | nil => simp [representativeCircuit,denote]
  | cons g w ih =>
    simp only [List.flatMap_cons,representativeCircuit_cons,List.map_cons,denote_append,
      denote_cons,Matrix.UnitaryGroup.mul_val,List.sum_cons]
    have he :
        (denote (w.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)*denote (compile g)-
          (denote (representativeCircuit w) : Matrix (Bits n) (Bits n) ℂ)*g.representative.denote=
        ((denote (w.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-
            denote (representativeCircuit w))*denote (compile g)+
          (denote (representativeCircuit w) : Matrix (Bits n) (Bits n) ℂ)*
            ((denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-g.representative.denote) := by
      noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
    simpa only [add_comm] using add_le_add_right ih
      ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-g.representative.denote‖

theorem descriptor_word_uniform_error {n : ℕ} (compile : GateCode n → Circuit n)
    (w : WordCode n) (ε : ℝ)
    (heach : ∀ g∈w,‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-
      g.representative.denote‖≤ε) :
    ‖(denote (interpret w) : Matrix (Bits n) (Bits n) ℂ)-wordPhase w •
      (denote (w.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)‖≤w.length*ε := by
  have hc : ‖wordPhase w‖=1 := by
    have hs : ‖wordPhase w‖^2=1 := (Complex.sq_norm _).trans (wordPhase_norm w)
    nlinarith [norm_nonneg (wordPhase w)]
  rw [representativeCircuit_phase,← smul_sub,norm_smul,hc,one_mul,norm_sub_rev]
  apply (descriptor_word_error compile w).trans
  have ht := List.sum_le_length_nsmul
    (w.map (fun g => ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-
      g.representative.denote‖)) ε (by
        intro x hx
        obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
        exact heach g hg)
  simpa only [List.length_map,nsmul_eq_mul] using ht

end EffectiveEncoding

