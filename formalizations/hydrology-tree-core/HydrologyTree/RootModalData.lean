import HydrologyTree.LinearForcedODE

/-! A finite modal coordinate witness for an actual root-driven matrix system.
Its existence for the physical tree is separately proved, not assumed globally. -/
open Matrix
noncomputable section
namespace HydrologyTree

structure RootModalData {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) where
  rates : Fin (n+1) → ℝ
  amplitudes : Fin (n+1) → ℝ
  synthesis : Matrix (Fin (n+1)) (Fin (n+1)) ℝ
  analysis : Matrix (Fin (n+1)) (Fin (n+1)) ℝ
  synth_analysis : synthesis*analysis=1
  analysis_synth : analysis*synthesis=1
  intertwine : A*synthesis=synthesis*Matrix.diagonal (fun i => -rates i)
  input_analysis : analysis *ᵥ Pi.single 0 1=amplitudes
  root_output : ∀ y : Fin (n+1) → ℝ,
    (synthesis*ᵥy) 0 = ∑ i, amplitudes i*y i


variable {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (M : RootModalData A)

lemma rootModal_synthesis_input : M.synthesis *ᵥ M.amplitudes=Pi.single 0 1 := by
  rw [← M.input_analysis,Matrix.mulVec_mulVec,M.synth_analysis,Matrix.one_mulVec]

lemma rootModal_synthesis_rhs (y : Fin (n+1) → ℝ) (u : ℝ) :
    M.synthesis *ᵥ (Matrix.diagonal (fun i => -M.rates i)*ᵥ y + u • M.amplitudes) =
      A *ᵥ (M.synthesis*ᵥy)+u • Pi.single 0 1 := by
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    ← M.intertwine,rootModal_synthesis_input M,Matrix.mulVec_mulVec]

end HydrologyTree
