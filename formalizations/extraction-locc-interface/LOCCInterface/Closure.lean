import LOCCInterface.Protocol

open scoped BigOperators ComplexOrder
open Matrix MinimaxProfile
namespace ExtractionLOCC
noncomputable section

abbrev ChannelMap (a b c d : ℕ) :=
  Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
    Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ

/-- The actual finite coefficient topology: all output entries on all matrix
units converge. Choi is simply a rearrangement of this complete coefficient list. -/
@[instance_reducible] def coefficientTopology (a b c d : ℕ) : TopologicalSpace (ChannelMap a b c d) :=
  TopologicalSpace.induced ExtractionCP.choi inferInstance

local instance {a b c d : ℕ} : TopologicalSpace (ChannelMap a b c d) :=
  coefficientTopology a b c d

variable {a b c d : ℕ}

theorem choi_injective : Function.Injective (ExtractionCP.choi : ChannelMap a b c d → _) := by
  intro Φ Ψ h
  ext X o p
  rw [ExtractionCP.map_eq_choi_sum Φ, ExtractionCP.map_eq_choi_sum Ψ, h]

theorem continuous_choi : Continuous (ExtractionCP.choi : ChannelMap a b c d → _) :=
  continuous_induced_dom

/-- Evaluation on any actual input matrix is continuous in the full coefficient
topology; this is proved from the matrix-unit expansion. -/
theorem continuous_evaluation (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Continuous (fun Φ : ChannelMap a b c d => Φ X) := by
  have hc := continuous_choi (a := a) (b := b) (c := c) (d := d)
  apply continuous_pi
  intro o
  apply continuous_pi
  intro p
  simp_rw [ExtractionCP.map_eq_choi_sum]
  fun_prop

theorem isClosed_completelyPositive :
    IsClosed {Φ : ChannelMap a b c d | ExtractionCP.CompletelyPositive Φ} := by
  have h := Matrix.posSemidef_is_closed.preimage
    (continuous_choi (a := a) (b := b) (c := c) (d := d))
  simpa only [Set.preimage_ofPred_eq, ← ExtractionCP.completelyPositive_iff_choi_posSemidef] using h

theorem isClosed_tracePreserving :
    IsClosed {Φ : ChannelMap a b c d | ExtractionCP.TracePreserving Φ} := by
  have he : {Φ : ChannelMap a b c d | ExtractionCP.TracePreserving Φ} =
      ⋂ X, {Φ : ChannelMap a b c d | (Φ X).trace = X.trace} := by
    ext Φ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ExtractionCP.TracePreserving]
  rw [he]
  apply isClosed_iInter
  intro X
  apply isClosed_eq _ continuous_const
  have hc := continuous_evaluation (c := c) (d := d) X
  change Continuous (fun Φ : ChannelMap a b c d => ∑ o, Φ X o o)
  apply continuous_finset_sum
  intro o _
  exact (continuous_apply o).comp ((continuous_apply o).comp hc)

/-- Partial transpose sends a matrix unit to the corresponding swapped unit. -/
theorem partialTranspose_single (i j : Fin a × Fin b) :
    APPT.Quantum.partialTranspose (Matrix.single i j (1 : ℂ)) =
      Matrix.single (j.1,i.2) (i.1,j.2) 1 := by
  ext ⟨x,y⟩ ⟨z,w⟩
  simp [APPT.Quantum.partialTranspose, Matrix.single_apply, Prod.ext_iff,
    and_left_comm, and_assoc]

theorem choi_ptConjugate (Φ : ChannelMap a b c d)
    (o p : Fin c × Fin d) (i j : Fin a × Fin b) :
    ExtractionCP.choi (ExtractionCP.ptConjugate Φ) (o,i) (p,j) =
      ExtractionCP.choi Φ ((p.1,o.2),(j.1,i.2)) ((o.1,p.2),(i.1,j.2)) := by
  simp only [ExtractionCP.choi, ExtractionCP.ptConjugate_apply,
    partialTranspose_single, APPT.Quantum.partialTranspose]

theorem continuous_choi_ptConjugate :
    Continuous (fun Φ : ChannelMap a b c d => ExtractionCP.choi (ExtractionCP.ptConjugate Φ)) := by
  have hc := continuous_choi (a := a) (b := b) (c := c) (d := d)
  apply continuous_pi
  intro ⟨o,i⟩
  apply continuous_pi
  intro ⟨p,j⟩
  simp_rw [choi_ptConjugate]
  fun_prop

theorem isClosed_pt_completelyPositive :
    IsClosed {Φ : ChannelMap a b c d |
      ExtractionCP.CompletelyPositive (ExtractionCP.ptConjugate Φ)} := by
  have h := Matrix.posSemidef_is_closed.preimage
    (continuous_choi_ptConjugate (a := a) (b := b) (c := c) (d := d))
  simpa only [Set.preimage_ofPred_eq, ← ExtractionCP.completelyPositive_iff_choi_posSemidef] using h

/-- The topological closure of the actual finite-round execution-tree channels,
in the full matrix-unit coefficient topology, with fixed input/output systems. -/
def IsClosureLOCC (Φ : ChannelMap a b c d) : Prop :=
  Φ ∈ closure {Ψ : ChannelMap a b c d | IsFiniteLOCC Ψ}

theorem IsFiniteLOCC.isClosureLOCC {Φ : ChannelMap a b c d} (h : IsFiniteLOCC Φ) :
    IsClosureLOCC Φ := subset_closure h

theorem IsClosureLOCC.completelyPositive {Φ : ChannelMap a b c d} (h : IsClosureLOCC Φ) :
    ExtractionCP.CompletelyPositive Φ :=
  closure_minimal (fun _ hΨ => hΨ.completelyPositive) isClosed_completelyPositive h

theorem IsClosureLOCC.tracePreserving {Φ : ChannelMap a b c d} (h : IsClosureLOCC Φ) :
    ExtractionCP.TracePreserving Φ :=
  closure_minimal (fun _ hΨ => hΨ.tracePreserving) isClosed_tracePreserving h

theorem IsClosureLOCC.pt_completelyPositive {Φ : ChannelMap a b c d} (h : IsClosureLOCC Φ) :
    ExtractionCP.CompletelyPositive (ExtractionCP.ptConjugate Φ) :=
  closure_minimal (fun _ hΨ => hΨ.pt_completelyPositive) isClosed_pt_completelyPositive h

/-- Closure LOCC is imposed on the actual postprocessing map, separately from U. -/
def IsClosureLOCCProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K) : Prop :=
  IsClosureLOCC (ExtractionCP.krausLinearMap P.A)

theorem finiteLOCC_isClosureLOCCProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K)
    (h : IsFiniteLOCCProtocol P) : IsClosureLOCCProtocol P := h.isClosureLOCC

theorem productLocal_isClosureLOCCProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K)
    (h : P.IsProductLocal) : IsClosureLOCCProtocol P :=
  finiteLOCC_isClosureLOCCProtocol P (productLocal_isFiniteLOCCProtocol P h)

/-- Even a limit channel has complete actual finite Kraus representatives for
both it and its transpose conjugate, derived from the closed CP constraints. -/
theorem IsClosureLOCC.exists_actual_protocol {a b K : ℕ}
    {Φ : ChannelMap a b K K} (h : IsClosureLOCC Φ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    ∃ P : KrausPPTProtocol a b K, P.U = U ∧ IsClosureLOCCProtocol P ∧
      ∀ X, Extraction.krausApply P.A X = Φ X := by
  let C : ExtractionCP.PPTChannel a b K :=
    ⟨Φ,h.completelyPositive,h.tracePreserving,h.pt_completelyPositive⟩
  let P := C.toKrausPPTProtocol U
  have he : ExtractionCP.krausLinearMap P.A = Φ := by
    ext X o p
    exact congrFun (congrFun (C.toKrausPPTProtocol_apply U X) o) p
  refine ⟨P,rfl,?_,C.toKrausPPTProtocol_apply U⟩
  change IsClosureLOCC (ExtractionCP.krausLinearMap P.A)
  rw [he]
  exact h

end
end ExtractionLOCC
