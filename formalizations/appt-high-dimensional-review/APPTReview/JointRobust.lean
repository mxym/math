import APPTReview.JointControls
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def counterexample1038Interior :=
  stateMix (1/1000:ℝ) counterexample1038 (maximallyMixed 10 38)

theorem counterexample1038Interior_density : APPT.Quantum.IsDensity counterexample1038Interior :=
  stateMix_density (by norm_num) (by norm_num) counterexample1038_isDensity
    (maximallyMixed_density (by omega) (by omega))

theorem counterexample1038Interior_appt : APPT.Quantum.AbsolutelyPPT counterexample1038Interior :=
  stateMix_appt (by norm_num) (by norm_num) counterexample1038_absolutelyPPT (maximallyMixed_appt 10 38)

/-- Uniform positive distance from loss of PPT on every global unitary orbit. -/
theorem counterexample1038Interior_margin (U : Matrix.unitaryGroup (Fin 10 × Fin 38) ℂ) :
    (APPT.Quantum.partialTranspose ((U:Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)*
      counterexample1038Interior*(U:Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)ᴴ)-
      (1/380000:ℝ) • (1 : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)).PosSemidef := by
  have h := (counterexample1038_absolutelyPPT U).smul (by norm_num : (0:ℝ)≤999/1000)
  have hu : (U:Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)*(U:Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  convert h using 1
  simp only [counterexample1038Interior,stateMix,maximallyMixed,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hu,APPT.Quantum.partialTranspose_add,
    APPT.Quantum.partialTranspose_smul,APPT.Quantum.partialTranspose_one,smul_smul]
  norm_num

theorem counterexample1038Interior_formula_gap :
    proposedAPPTPurity 10 38 < APPT.Quantum.purity counterexample1038Interior := by
  rw [counterexample1038Interior,stateMix_purity,
    density_centered_purity (by omega) (by omega) counterexample1038_isDensity,
    counterexample1038_purity,maximallyMixed_purity (by omega) (by omega)]
  norm_num [proposedAPPTPurity]

end APPTReview
