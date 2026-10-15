import Extraction.ProjectionFactor
import Extraction.OverlapConverse

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

/-- The actual common-subspace extraction theorem in arbitrary integer input
dimensions. Integer floors and all unused coordinates are retained. -/
theorem finite_projection_exact_extractor (a b d : ℕ) (hd : 0 < d)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a / d) ⊕ Fin a → Matrix (Fin d) (Fin a) ℂ)
      (B : Fin (b / d) ⊕ Fin b → Matrix (Fin d) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        P * X * P = X →
        krausApply (productKraus A B)
          ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
            (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ) =
        X.trace • bellProjector (d := Fin d) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨κ, iκ, eκ, C, hC, hCP, hcard⟩ := exists_projection_factor P hP hPP
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  have ha : Fintype.card (Fin d × Fin (a / d)) ≤ Fintype.card (Fin a) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm d] using Nat.div_mul_le_self a d
  have hb : Fintype.card (Fin d × Fin (b / d)) ≤ Fintype.card (Fin b) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm d] using Nat.div_mul_le_self b d
  let EA := coordinateIsometry (cardEmbedding ha)
  let EB := coordinateIsometry (cardEmbedding hb)
  have hκ : Fintype.card κ ≤ Fintype.card (Fin (a / d) × Fin (b / d)) := by
    simpa only [hcard, Fintype.card_prod, Fintype.card_fin] using hr
  obtain ⟨U,A,B,hA,hB,h⟩ := exists_common_subspace_exact_extractor C hC EA EB
    (coordinateIsometry_isometry _) (coordinateIsometry_isometry _) hκ
  refine ⟨U,A,B,hA,hB,?_⟩
  intro X hX
  exact h X (by simpa only [hCP] using hX)

/-- The special target-dimension equality criterion has no asymptotic premise. -/
theorem finite_projection_density_extractor (a b d : ℕ) (hd : 0 < d)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a / d) ⊕ Fin a → Matrix (Fin d) (Fin a) ℂ)
      (B : Fin (b / d) ⊕ Fin b → Matrix (Fin d) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        APPT.Quantum.IsDensity X → P * X * P = X →
        krausApply (productKraus A B)
          ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
            (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ) =
        bellProjector (d := Fin d) := by
  obtain ⟨U,A,B,hA,hB,h⟩ := finite_projection_exact_extractor a b d hd P hP hPP hr
  refine ⟨U,A,B,hA,hB,?_⟩
  intro X hX hPX
  simpa only [hX.2, one_smul] using h X hPX

end Extraction
