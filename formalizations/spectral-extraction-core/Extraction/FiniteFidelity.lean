import Extraction.OutputEmbedding

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

/-- Exact finite integer-rank packing into any larger requested output.
One fixed global unitary and two deterministic local channels achieve d/K
on every actual density supported by P. -/
theorem finite_projection_fidelity_extractor (a b d K : ℕ)
    (hd : 0 < d) (hdk : d ≤ K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a / d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b / d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        APPT.Quantum.IsDensity X → P * X * P = X →
        (bellProjector (d := Fin K) *
          krausApply (productKraus A B)
            ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
              (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re =
        (d : ℝ) / K := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin K) := ⟨⟨0,lt_of_lt_of_le hd hdk⟩⟩
  obtain ⟨U,A,B,hA,hB,h⟩ := finite_projection_density_extractor a b d hd P hP hPP hr
  let f : Fin d ↪ Fin K := cardEmbedding (by simpa only [Fintype.card_fin] using hdk)
  let E := coordinateIsometry f
  have hE : Eᴴ * E = 1 := coordinateIsometry_isometry f
  refine ⟨U, (fun j => E * A j), (fun j => E * B j),
    postcomposeKraus_complete A hA E hE,
    postcomposeKraus_complete B hB E hE, ?_⟩
  intro X hX hPX
  have hp : productKraus (fun j => E * A j) (fun j => E * B j) =
      fun j => (E ⊗ₖ E) * productKraus A B j := by
    funext j
    exact Matrix.mul_kronecker_mul E (A j.1) E (B j.2)
  rw [hp, postcomposeKraus_apply, h X hX hPX]
  simpa only [Fintype.card_fin] using embedded_bell_overlap f

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [Nonempty d]

/-- The physical converse is uniform over every initial global unitary. -/
theorem kraus_target_overlap_unitary_le
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1) (hpt : PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : X.IsHermitian)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    (bellProjector (d := d) *
      krausApply A ((U : Matrix (a × b) (a × b) ℂ) * X *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re ≤
      Real.sqrt ((X * X).trace.re *
        ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2)) := by
  have hh : ((U : Matrix (a × b) (a × b) ℂ) * X *
      (U : Matrix (a × b) (a × b) ℂ)ᴴ).IsHermitian := by
    change ((U : Matrix (a × b) (a × b) ℂ) * X *
      (U : Matrix (a × b) (a × b) ℂ)ᴴ)ᴴ =
        (U : Matrix (a × b) (a × b) ℂ) * X *
          (U : Matrix (a × b) (a × b) ℂ)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hX.eq, Matrix.mul_assoc]
  have h := kraus_target_overlap_le A hcomplete hpt _ hh
  rwa [trace_square_unitary] at h

end Extraction
