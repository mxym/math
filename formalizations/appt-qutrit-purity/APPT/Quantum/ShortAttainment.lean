import APPT.Quantum.PureOrbit
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

theorem rankOne_trace (v : Fin 3 × b → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) : (rankOne v).trace = 1 := by
  change (∑ k, v k*star (v k)) = 1
  simpa [mul_comm] using hv

theorem rankOne_sq (v : Fin 3 × b → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) : rankOne v*rankOne v=rankOne v := by
  have hd : star v ⬝ᵥ v = 1 := hv
  simp [rankOne, Matrix.vecMulVec_mul_vecMulVec, hd]

noncomputable def shortState (n : ℕ) (v : Fin 3 × Fin n → ℂ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  (1/(3*(n : ℝ)+2)) • (1+(2 : ℝ) • rankOne v)

theorem shortState_absolutelyPPT (n : ℕ) (v : Fin 3 × Fin n → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) : AbsolutelyPPT (shortState n v) := by
  apply absolutelyPPT_smul (absolutelyPPT_one_add_twice_rankOne v hv)
  positivity

theorem shortState_isDensity (n : ℕ) (v : Fin 3 × Fin n → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) : IsDensity (shortState n v) := by
  have hp : (0 : ℝ) < 3*(n : ℝ)+2 := by positivity
  constructor
  · exact (Matrix.PosSemidef.one.add ((rankOne_posSemidef v).smul
      (by norm_num : (0 : ℝ) ≤ 2))).smul (by positivity)
  · simp [shortState, Matrix.trace_smul, Matrix.trace_add,
      rankOne_trace v hv, Matrix.trace_one, Complex.real_smul]
    field_simp
    <;> norm_num

theorem shortState_purity (n : ℕ) (v : Fin 3 × Fin n → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) :
    purity (shortState n v) = (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
  have hp : (0 : ℝ) < 3*(n : ℝ)+2 := by positivity
  have he : (1+(2 : ℝ) • rankOne v)*(1+(2 : ℝ) • rankOne v) =
      1+(8 : ℝ) • rankOne v := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, rankOne_sq v hv]
    module
  unfold purity shortState
  rw [Matrix.smul_mul, Matrix.mul_smul, he]
  simp only [Matrix.trace_smul, Matrix.trace_add, rankOne_trace v hv,
    Matrix.trace_one, Complex.smul_re, Complex.add_re, Complex.one_re,
    Complex.natCast_re, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  simp [Complex.mul_re]
  <;> field_simp
  <;> ring

theorem exists_shortState (n : ℕ) (hn : 0<n) :
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ AbsolutelyPPT A ∧
      purity A = (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
  let e : Fin 3 × Fin n := (0,⟨0,hn⟩)
  let v : Fin 3 × Fin n → ℂ := Pi.single e 1
  have hv : (∑ k, star (v k)*v k) = 1 := by simp [v, Pi.single_apply]
  exact ⟨shortState n v, shortState_isDensity n v hv,
    shortState_absolutelyPPT n v hv, shortState_purity n v hv⟩

end APPT.Quantum
