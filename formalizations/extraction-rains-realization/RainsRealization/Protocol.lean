import RainsRealization.PPT

open scoped BigOperators ComplexOrder
open Matrix MinimaxProfile
namespace ExtractionRains
noncomputable section
variable {a b K : ℕ}

/-- The Rains effect inequalities themselves prove all physical channel axioms. -/
def pptChannel (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M) :
    ExtractionCP.PPTChannel a b K where
  map := channel K M
  cp := channel_completelyPositive K hK M hM
  tp := channel_tracePreserving K hK M
  ppt := channel_pt_completelyPositive K hK M hM

/-- Both complete finite Kraus families are constructed by the proved Choi
square-root theorem, including the transpose-conjugate family. -/
def protocol (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) : KrausPPTProtocol a b K :=
  (pptChannel K hK M hM).toKrausPPTProtocol U

theorem protocol_apply (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Extraction.krausApply (protocol K hK M hM U).A X =
      (M * X).trace • Extraction.bellProjector + ((1-M)*X).trace • failureState K :=
  (pptChannel K hK M hM).toKrausPPTProtocol_apply U X

/-- Exact Heisenberg fidelity effect of the constructed actual cPPT protocol. -/
theorem protocol_targetEffect (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    Extraction.targetEffect (protocol K hK M hM U).A = M := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  change (Extraction.krausApply (fun j => ((protocol K hK M hM U).A j)ᴴ)
    Extraction.bellProjector * X).trace = _
  rw [← Extraction.krausApply_trace_duality]
  change (Extraction.bellProjector *
    Extraction.krausApply ((pptChannel K hK M hM).toKrausPPTProtocol U).A X).trace = _
  rw [(pptChannel K hK M hM).toKrausPPTProtocol_apply U X]
  exact channel_target_overlap K hK M X

theorem protocol_fidelity (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (protocol K hK M hM U).fidelity X =
      (M * ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).trace.re := by
  unfold protocol
  rw [ExtractionCP.PPTChannel.toKrausPPTProtocol_fidelity]
  exact congrArg Complex.re (channel_target_overlap K hK M _)

/-- Reverse Rains realization with the actual measure-and-prepare action and
exact target effect, retaining every supplied preprocessing unitary. -/
theorem rainsEffect_exists_actual_protocol (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    ∃ P : KrausPPTProtocol a b K, P.U = U ∧ Extraction.targetEffect P.A = M ∧
      ∀ X, Extraction.krausApply P.A X =
        (M * X).trace • Extraction.bellProjector + ((1-M)*X).trace • failureState K :=
  ⟨protocol K hK M hM U,rfl,protocol_targetEffect K hK M hM U,protocol_apply K hK M hM U⟩

/-- For K at least two, the Rains spectrahedron is precisely the set of fidelity
effects of actual complete-PPT channels, rather than only an outer relaxation. -/
theorem rainsEffect_iff_actual_protocol_effect (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    Extraction.RainsEffect K M ↔
      ∃ P : KrausPPTProtocol a b K, P.U = U ∧ Extraction.targetEffect P.A = M := by
  constructor
  · intro hM
    exact ⟨protocol K hK M hM U,rfl,protocol_targetEffect K hK M hM U⟩
  · rintro ⟨P,_,hM⟩
    letI : NeZero K := ⟨by omega⟩
    have h := Extraction.targetEffect_rains P.A P.complete P.ptPositive
    rw [Fintype.card_fin,hM] at h
    exact h

end
end ExtractionRains
