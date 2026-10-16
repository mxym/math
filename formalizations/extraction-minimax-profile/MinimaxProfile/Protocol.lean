import MinimaxProfile.Average

open scoped BigOperators ComplexOrder
open Matrix
namespace MinimaxProfile

variable {a b K : ℕ}

/-- An actual deterministic finite-dimensional PPT channel, with explicit
Kraus representations both for the channel and its transpose conjugate.
All conditions are physical matrix identities; no performance budget appears. -/
structure KrausPPTProtocol (a b K : ℕ) where
  U : Matrix.unitaryGroup (Fin a × Fin b) ℂ
  branches : ℕ
  A : Fin branches → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ
  complete : ∑ j, (A j)ᴴ * A j = 1
  ptBranches : ℕ
  ptA : Fin ptBranches → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ
  ptComplete : ∑ j, (ptA j)ᴴ * ptA j = 1
  ptIdentity : ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
    APPT.Quantum.partialTranspose (Extraction.krausApply A (APPT.Quantum.partialTranspose X)) =
      Extraction.krausApply ptA X

theorem KrausPPTProtocol.ptPositive (P : KrausPPTProtocol a b K) :
    Extraction.PTConjugatePositive P.A := by
  intro X hX
  rw [P.ptIdentity]
  exact Extraction.krausApply_posSemidef _ X hX

noncomputable def KrausPPTProtocol.fidelity (P : KrausPPTProtocol a b K)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ := overlap P.A P.U X

/-- Both maps are completely positive on every actual finite auxiliary space. -/
theorem KrausPPTProtocol.amplified_positive (P : KrausPPTProtocol a b K)
    (τ : Type*) [Fintype τ] [DecidableEq τ]
    (X : Matrix ((Fin a × Fin b) × τ) ((Fin a × Fin b) × τ) ℂ)
    (hX : X.PosSemidef) :
    (Extraction.krausAmplification P.A τ X).PosSemidef ∧
    (Extraction.krausAmplification P.ptA τ X).PosSemidef :=
  ⟨Extraction.krausAmplification_posSemidef _ _ _ hX,
    Extraction.krausAmplification_posSemidef _ _ _ hX⟩

theorem krausApply_equiv {ι ο κ τ : Type*} [Fintype ι] [Fintype ο]
    [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq ο]
    (A : κ → Matrix ο ι ℂ) (e : τ ≃ κ) (X : Matrix ι ι ℂ) :
    Extraction.krausApply (fun j => A (e j)) X = Extraction.krausApply A X := by
  unfold Extraction.krausApply
  exact e.sum_comp (fun j => A j * X * (A j)ᴴ)

/-- Products of actual complete local channels give a protocol in the physical
class, including its completely positive transpose-conjugated channel. -/
noncomputable def localProtocol {κ τ : Type*} [Fintype κ] [Fintype τ]
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (A : κ → Matrix (Fin K) (Fin a) ℂ) (B : τ → Matrix (Fin K) (Fin b) ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    KrausPPTProtocol a b K := by
  classical
  let e : Fin (Fintype.card (κ × τ)) ≃ κ × τ := (Fintype.equivFin (κ × τ)).symm
  let C := Extraction.productKraus A B
  let D := Extraction.productKraus (fun j => SpectralProtocol.conjugateMatrix (A j)) B
  refine { U := U
           branches := Fintype.card (κ × τ)
           A := fun j => C (e j)
           complete := ?_
           ptBranches := Fintype.card (κ × τ)
           ptA := fun j => D (e j)
           ptComplete := ?_
           ptIdentity := ?_ }
  · rw [e.sum_comp (fun j => (C j)ᴴ * C j)]
    exact Extraction.productKraus_complete A B hA hB
  · rw [e.sum_comp (fun j => (D j)ᴴ * D j)]
    exact Extraction.productKraus_complete _ B
      (SpectralProtocol.conjugateMatrix_complete A hA) hB
  · intro X
    rw [krausApply_equiv, krausApply_equiv]
    exact SpectralProtocol.product_kraus_partialTranspose A B X

theorem localProtocol_fidelity {κ τ : Type*} [Fintype κ] [Fintype τ]
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (A : κ → Matrix (Fin K) (Fin a) ℂ) (B : τ → Matrix (Fin K) (Fin b) ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (localProtocol U A B hA hB).fidelity X =
      overlap (Extraction.productKraus A B) U X := by
  unfold KrausPPTProtocol.fidelity overlap localProtocol
  rw [krausApply_equiv]

/-- The common projector promise yields one actual protocol before every input,
including complete PPT resource accounting, with exact d/K overlap. -/
theorem common_support_protocol (a b d K : ℕ) (hd : 0 < d) (hdk : d ≤ K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) :
    ∃ V : KrausPPTProtocol a b K,
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        APPT.Quantum.IsDensity X → P * X * P = X → V.fidelity X = (d : ℝ) / K := by
  obtain ⟨U,A,B,hA,hB,h⟩ := Extraction.finite_projection_fidelity_extractor
    a b d K hd hdk P hP hPP hr
  refine ⟨localProtocol U A B hA hB, ?_⟩
  intro X hX hPX
  rw [localProtocol_fidelity]
  exact h X hX hPX

end MinimaxProfile
