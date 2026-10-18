import APPTApplications.SpikeState

open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator
open Matrix
namespace ExtractionAPPT
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The spectrum of an actual Hermitian idempotent consists of zero and one. -/
theorem projection_spectrum_zero_one (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P*P=P)
    (x : ℝ) (hx : x ∈ spectrum ℝ P) : x=0 ∨ x=1 := by
  have he : cfc (fun t : ℝ => t^2) P = cfc (fun t : ℝ => t) P := by
    rw [cfc_pow_id P 2 hP.isSelfAdjoint, cfc_id' ℝ P hP.isSelfAdjoint]
    simpa only [pow_two] using hPP
  have hs := eqOn_of_cfc_eq_cfc he (by fun_prop) continuous_id.continuousOn hP.isSelfAdjoint
  have ht := hs hx
  have hp : x*(x-1)=0 := by dsimp at ht; nlinarith
  rcases mul_eq_zero.mp hp with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

theorem cfc_affine (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (α β : ℝ) :
    cfc (fun t : ℝ => α+β*t) P = α • (1 : Matrix ι ι ℂ) + β • P := by
  rw [cfc_const_add α (fun t : ℝ => β*t) P (by fun_prop) hP.isSelfAdjoint,
    cfc_const_mul_id β P hP.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

/-- Exact two-point interpolation in the real CFC of a genuine projection. -/
theorem cfc_affine_projection (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P*P=P)
    (α β : ℝ) : cfc Real.negMulLog (α • (1 : Matrix ι ι ℂ) + β • P) =
      Real.negMulLog α • (1 : Matrix ι ι ℂ) +
        (Real.negMulLog (α+β)-Real.negMulLog α) • P := by
  calc
    _ = cfc (Real.negMulLog ∘ (fun t : ℝ => α+β*t)) P := by
      rw [cfc_comp Real.negMulLog (fun t : ℝ => α+β*t) P hP.isSelfAdjoint
        Real.continuous_negMulLog.continuousOn (by fun_prop), cfc_affine P hP α β]
    _ = cfc (fun t : ℝ => Real.negMulLog α +
        (Real.negMulLog (α+β)-Real.negMulLog α)*t) P := by
      apply cfc_congr
      intro t ht
      rcases projection_spectrum_zero_one P hP hPP t ht with rfl | rfl <;> simp
    _ = _ := cfc_affine P hP _ _

theorem quantumEntropy_affine_rankOne (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P*P=P) (htr : P.trace=1) (α β : ℝ) :
    quantumEntropy (α • (1 : Matrix ι ι ℂ) + β • P) =
      (Fintype.card ι : ℝ)*Real.negMulLog α + Real.negMulLog (α+β)-Real.negMulLog α := by
  rw [quantumEntropy, cfc_affine_projection P hP hPP, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, htr, Matrix.trace_one]
  simp [Complex.add_re, Complex.smul_re]
  <;> ring

/-- Exact entropy of (I+2 vv*)/(D+2), proved for every unit vector. -/
theorem spikeState_entropy (m n : ℕ) (v : Fin m × Fin n → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) :
    quantumEntropy (spikeState m n v) =
      Real.log ((m:ℝ)*n+2) - 3*Real.log 3/((m:ℝ)*n+2) := by
  have hP := (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  have hPP : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec v (star v) := by
    have hn : star v ⬝ᵥ v = 1 := hv
    simp [Matrix.vecMulVec_mul_vecMulVec, hn]
  have hZ : (m:ℝ)*n+2 ≠ 0 := by positivity
  have he : spikeState m n v = (1/((m:ℝ)*n+2)) • (1 : Matrix _ _ ℂ) +
      (2/((m:ℝ)*n+2)) • Matrix.vecMulVec v (star v) := by
    simp [spikeState, smul_add, smul_smul, div_eq_mul_inv, mul_comm]
  rw [he, quantumEntropy_affine_rankOne _ hP hPP (pure_trace v hv)]
  have ha : 1/((m:ℝ)*n+2)+2/((m:ℝ)*n+2)=3/((m:ℝ)*n+2) := by ring
  rw [ha]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Real.negMulLog,
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) hZ, Real.log_one,
    Real.log_div (by norm_num : (3:ℝ) ≠ 0) hZ]
  field_simp
  <;> ring

end
end ExtractionAPPT
