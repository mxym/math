import TensorSharp

namespace ComplexPencilTensor
noncomputable section

def tensorNormBound (ts : List ℝ) (K : ℝ) : Prop :=
  ∀ f g h : List (Fin 3) → ℂ,
    ‖tensor ts f g h‖ ≤
      K * Real.sqrt (energy ts f) *
        Real.sqrt (energy ts g) * Real.sqrt (energy ts h)

private theorem scalar_root_square
    (ts : List ℝ) (K : ℝ)
    (f g h : List (Fin 3) → ℂ) :
    (K * Real.sqrt (energy ts f) *
       Real.sqrt (energy ts g) * Real.sqrt (energy ts h)) ^ 2 =
      K^2 * energy ts f * energy ts g * energy ts h := by
  rw [mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (energy_nonneg ts f),
    Real.sq_sqrt (energy_nonneg ts g),
    Real.sq_sqrt (energy_nonneg ts h)] <;> ring

theorem tensorNormBound_iff (ts : List ℝ)
    (hvalid : ∀ t ∈ ts, |t| ≤ (1/6 : ℝ))
    (K : ℝ) (hK : 0 ≤ K) :
    tensorNormBound ts K ↔ productK ts ≤ K := by
  constructor
  · intro h
    have hSq : tensorSquaredBound ts (K^2) := by
      intro f g j
      have hh := h f g j
      have hp : 0 ≤ K * Real.sqrt (energy ts f) *
          Real.sqrt (energy ts g) *
          Real.sqrt (energy ts j) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hK (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
      have hs := scalar_root_square ts K f g j
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (tensor ts f g j)]
    have hk := (tensorSquaredBound_iff ts hvalid (K^2)).mp hSq
    nlinarith [productK_nonneg ts]
  · intro hk f g j
    have hbase := tensorized_complex_norm_bound ts hvalid f g j
    have hp : 0 ≤ Real.sqrt (energy ts f) *
        Real.sqrt (energy ts g) *
        Real.sqrt (energy ts j) := by
      exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hk hp
    calc
      _ ≤ productK ts * Real.sqrt (energy ts f) *
          Real.sqrt (energy ts g) *
          Real.sqrt (energy ts j) := hbase
      _ = productK ts *
          (Real.sqrt (energy ts f) *
            Real.sqrt (energy ts g) *
            Real.sqrt (energy ts j)) := by ring
      _ ≤ K *
          (Real.sqrt (energy ts f) *
            Real.sqrt (energy ts g) *
            Real.sqrt (energy ts j)) := hm
      _ = _ := by ring

#print axioms ComplexPencilTensor.tensorNormBound_iff

end
end ComplexPencilTensor
