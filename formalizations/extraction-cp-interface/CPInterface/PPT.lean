import CPInterface.Choi

open scoped BigOperators ComplexOrder
open Matrix MinimaxProfile
namespace ExtractionCP
noncomputable section

variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

/-- Partial transpose is complex-linear even though it need not be positive. -/
def partialTransposeLinearMap : Matrix (a×b) (a×b) ℂ →ₗ[ℂ] Matrix (a×b) (a×b) ℂ where
  toFun := APPT.Quantum.partialTranspose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual Schrödinger partial-transpose conjugation on the two product spaces. -/
def ptConjugate (Φ : Matrix (a×b) (a×b) ℂ →ₗ[ℂ] Matrix (c×d) (c×d) ℂ) :
    Matrix (a×b) (a×b) ℂ →ₗ[ℂ] Matrix (c×d) (c×d) ℂ :=
  partialTransposeLinearMap.comp (Φ.comp partialTransposeLinearMap)

@[simp] theorem ptConjugate_apply
    (Φ : Matrix (a×b) (a×b) ℂ →ₗ[ℂ] Matrix (c×d) (c×d) ℂ) (X) :
    ptConjugate Φ X=APPT.Quantum.partialTranspose (Φ (APPT.Quantum.partialTranspose X)) := rfl

 theorem TracePreserving.ptConjugate
    {Φ : Matrix (a×b) (a×b) ℂ →ₗ[ℂ] Matrix (c×d) (c×d) ℂ}
    (ht : TracePreserving Φ) : TracePreserving (ptConjugate Φ) := by
  intro X
  rw [ptConjugate_apply,APPT.Quantum.partialTranspose_trace,ht,
    APPT.Quantum.partialTranspose_trace]

variable {ι ο : Type} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

/-- Canonical natural-index Kraus family, with at most input times output branches. -/
def finiteKraus (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    Fin (Fintype.card (ο×ι)) → Matrix ο ι ℂ :=
  fun a => choiKraus Φ ((Fintype.equivFin (ο×ι)).symm a)

 theorem finiteKraus_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : CompletelyPositive Φ) (X) : Extraction.krausApply (finiteKraus Φ) X=Φ X := by
  unfold finiteKraus
  rw [MinimaxProfile.krausApply_equiv]
  exact choiKraus_apply Φ hΦ.choi_posSemidef X

 theorem finiteKraus_complete (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : CompletelyPositive Φ) (ht : TracePreserving Φ) :
    ∑ a, (finiteKraus Φ a)ᴴ*finiteKraus Φ a=1 := by
  unfold finiteKraus
  exact ((Fintype.equivFin (ο×ι)).symm.sum_comp
    (fun a => (choiKraus Φ a)ᴴ*choiKraus Φ a)).trans
      (choiKraus_complete Φ hΦ.choi_posSemidef ht)

/-- An abstract deterministic cPPT channel is specified using genuine complete
positivity of its two matrix amplifications and ordinary trace preservation. -/
structure PPTChannel (a b K : ℕ) where
  map : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ →ₗ[ℂ]
    Matrix (Fin K×Fin K) (Fin K×Fin K) ℂ
  cp : CompletelyPositive map
  tp : TracePreserving map
  ppt : CompletelyPositive (ptConjugate map)

/-- Full bridge: Choi square-root decomposition supplies both actual complete
Kraus families required by the existing extraction protocol model. -/
def PPTChannel.toKrausPPTProtocol {a b K : ℕ} (C : PPTChannel a b K)
    (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ) : KrausPPTProtocol a b K where
  U := U
  branches := Fintype.card ((Fin K×Fin K)×(Fin a×Fin b))
  A := finiteKraus C.map
  complete := finiteKraus_complete C.map C.cp C.tp
  ptBranches := Fintype.card ((Fin K×Fin K)×(Fin a×Fin b))
  ptA := finiteKraus (ptConjugate C.map)
  ptComplete := finiteKraus_complete (ptConjugate C.map) C.ppt C.tp.ptConjugate
  ptIdentity X := by
    rw [finiteKraus_apply C.map C.cp,finiteKraus_apply (ptConjugate C.map) C.ppt]
    rfl

 theorem PPTChannel.toKrausPPTProtocol_apply {a b K : ℕ} (C : PPTChannel a b K)
    (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ) (X) :
    Extraction.krausApply (C.toKrausPPTProtocol U).A X=C.map X :=
  finiteKraus_apply C.map C.cp X

 theorem PPTChannel.toKrausPPTProtocol_fidelity {a b K : ℕ} (C : PPTChannel a b K)
    (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ) (X) :
    (C.toKrausPPTProtocol U).fidelity X=
      (Extraction.bellProjector (d := Fin K)*C.map ((U:Matrix _ _ ℂ)*X*(U:Matrix _ _ ℂ)ᴴ)).trace.re := by
  unfold KrausPPTProtocol.fidelity MinimaxProfile.overlap
  rw [C.toKrausPPTProtocol_apply]
  rfl

/-- Every existing actual protocol conversely gives the abstract cPPT channel. -/
def ofKrausPPTProtocol {a b K : ℕ} (P : KrausPPTProtocol a b K) : PPTChannel a b K where
  map := krausLinearMap P.A
  cp := krausLinearMap_completelyPositive P.A
  tp := Extraction.krausApply_trace P.A P.complete
  ppt := by
    have he : ptConjugate (krausLinearMap P.A)=krausLinearMap P.ptA := by
      ext X o p
      exact congrArg (fun Y => Y o p) (P.ptIdentity X)
    rw [he]
    exact krausLinearMap_completelyPositive P.ptA

/-- Abstract CP is equivalent to an actual finite natural-index Kraus family. -/
 theorem completelyPositive_iff_exists_finiteKraus
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    CompletelyPositive Φ ↔ ∃ (r : ℕ) (A : Fin r → Matrix ο ι ℂ),
      ∀ X, Extraction.krausApply A X=Φ X := by
  refine ⟨fun hΦ => ⟨_,finiteKraus Φ,finiteKraus_apply Φ hΦ⟩,?_⟩
  rintro ⟨r,A,hA⟩
  have he : krausLinearMap A=Φ := by
    ext X o p
    exact congrArg (fun Y => Y o p) (hA X)
  rw [← he]
  exact krausLinearMap_completelyPositive A

/-- CP/TP is precisely the class of complete actual finite Kraus maps. -/
 theorem completelyPositive_tracePreserving_iff_exists_complete_finiteKraus
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) :
    (CompletelyPositive Φ ∧ TracePreserving Φ) ↔
      ∃ (r : ℕ) (A : Fin r → Matrix ο ι ℂ),
        (∑ a, (A a)ᴴ*A a=1) ∧ ∀ X, Extraction.krausApply A X=Φ X := by
  refine ⟨fun hΦ => ⟨_,finiteKraus Φ,finiteKraus_complete Φ hΦ.1 hΦ.2,
    finiteKraus_apply Φ hΦ.1⟩,?_⟩
  rintro ⟨r,A,hcomplete,hA⟩
  refine ⟨(completelyPositive_iff_exists_finiteKraus Φ).mpr ⟨r,A,hA⟩,?_⟩
  intro X
  rw [← hA X]
  exact Extraction.krausApply_trace A hcomplete X

/-- Exact equivalence with the extraction model, preserving an arbitrary
preprocessing unitary and the action on every complex matrix. No Kraus data
are assumed on the abstract side. -/
 theorem abstract_ppt_iff_actual_protocol (a b K : ℕ)
    (U : Matrix.unitaryGroup (Fin a×Fin b) ℂ)
    (Φ : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin K×Fin K) (Fin K×Fin K) ℂ) :
    (CompletelyPositive Φ ∧ TracePreserving Φ ∧ CompletelyPositive (ptConjugate Φ)) ↔
      ∃ P : KrausPPTProtocol a b K,P.U=U ∧
        ∀ X, Extraction.krausApply P.A X=Φ X := by
  constructor
  · rintro ⟨hcp,htp,hppt⟩
    let C : PPTChannel a b K := ⟨Φ,hcp,htp,hppt⟩
    exact ⟨C.toKrausPPTProtocol U,rfl,C.toKrausPPTProtocol_apply U⟩
  · rintro ⟨P,hU,hmap⟩
    let C := ofKrausPPTProtocol P
    have he : C.map=Φ := by
      ext X o p
      exact congrArg (fun Y => Y o p) (hmap X)
    rw [← he]
    exact ⟨C.cp,C.tp,C.ppt⟩

/-- Reconstructing an actual protocol through its abstract channel preserves
its original unitary and overlap on every matrix, including singular states. -/
 theorem actual_abstract_actual_fidelity {a b K : ℕ} (P : KrausPPTProtocol a b K) (X) :
    ((ofKrausPPTProtocol P).toKrausPPTProtocol P.U).fidelity X=P.fidelity X := by
  rw [PPTChannel.toKrausPPTProtocol_fidelity]
  rfl

end
end ExtractionCP
