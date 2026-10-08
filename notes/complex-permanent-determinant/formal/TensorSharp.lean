import TensorWitnessExact

namespace ComplexPencilTensor
noncomputable section

def tensorSquaredBound (ts : List ℝ) (B : ℝ) : Prop :=
  ∀ f g h : List (Fin 3) → ℂ,
    Complex.normSq (tensor ts f g h) ≤
      B * energy ts f * energy ts g * energy ts h

theorem tensor_normSq_upper (ts : List ℝ)
    (hvalid : ∀ t ∈ ts, |t| ≤ (1/6 : ℝ))
    (f g h : List (Fin 3) → ℂ) :
    Complex.normSq (tensor ts f g h) ≤
      (productK ts)^2 * energy ts f *
        energy ts g * energy ts h := by
  have hb := tensorized_complex_norm_bound ts hvalid f g h
  have hn : 0 ≤ ‖tensor ts f g h‖ := norm_nonneg _
  have hp : 0 ≤ productK ts *
      Real.sqrt (energy ts f) *
      Real.sqrt (energy ts g) *
      Real.sqrt (energy ts h) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (productK_nonneg ts) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hSq :
      (productK ts * Real.sqrt (energy ts f) *
        Real.sqrt (energy ts g) *
        Real.sqrt (energy ts h)) ^ 2 =
      (productK ts)^2 * energy ts f *
        energy ts g * energy ts h := by
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (energy_nonneg ts f),
      Real.sq_sqrt (energy_nonneg ts g),
      Real.sq_sqrt (energy_nonneg ts h)]
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

theorem tensor_witness_energy_pos (ts : List ℝ) :
  0 < energy ts (productEntries extF ts) ∧
  0 < energy ts (productEntries extG ts) ∧
  0 < energy ts (productEntries extH ts) := by
  rw [energy_productEntries, energy_productEntries,
      energy_productEntries]
  exact ⟨productEnergy_pos extF localEnergy_extF_pos ts,
    productEnergy_pos extG localEnergy_extG_pos ts,
    productEnergy_pos extH localEnergy_extH_pos ts⟩

theorem tensorSquaredBound_lower (ts : List ℝ) (B : ℝ)
    (h : tensorSquaredBound ts B) :
    (productK ts)^2 ≤ B := by
  let f := productEntries extF ts
  let g := productEntries extG ts
  let j := productEntries extH ts
  have hf : 0 < energy ts f := (tensor_witness_energy_pos ts).1
  have hg : 0 < energy ts g := (tensor_witness_energy_pos ts).2.1
  have hj : 0 < energy ts j := (tensor_witness_energy_pos ts).2.2
  have hp : 0 < energy ts f * energy ts g * energy ts j :=
    mul_pos (mul_pos hf hg) hj
  have heq : Complex.normSq (tensor ts f g j) =
      (productK ts)^2 * energy ts f * energy ts g *
        energy ts j := tensor_extremal_normSq ts
  have hineq := h f g j
  rw [heq] at hineq
  have hmul :
      (productK ts)^2 *
        (energy ts f * energy ts g * energy ts j) ≤
      B * (energy ts f * energy ts g * energy ts j) := by
    simpa only [mul_assoc] using hineq
  by_contra hnot
  have hlt : B < (productK ts)^2 := lt_of_not_ge hnot
  have ht := mul_lt_mul_of_pos_right hlt hp
  exact (not_lt_of_ge hmul) ht

/-- Full sharp tensor result for all finite lengths and all
    nonidentical legal S₃ permutation laws: no real squared
    coefficient B works universally unless B >= the exact
    squared product of all optimal single-column coefficients. -/
theorem tensorSquaredBound_iff (ts : List ℝ)
    (hvalid : ∀ t ∈ ts, |t| ≤ (1/6 : ℝ))
    (B : ℝ) :
    tensorSquaredBound ts B ↔ (productK ts)^2 ≤ B := by
  constructor
  · exact tensorSquaredBound_lower ts B
  · intro hB f g h
    have hE : 0 ≤ energy ts f * energy ts g *
        energy ts h :=
      mul_nonneg
        (mul_nonneg (energy_nonneg ts f)
          (energy_nonneg ts g)) (energy_nonneg ts h)
    calc
      _ ≤ (productK ts)^2 * energy ts f *
        energy ts g * energy ts h :=
          tensor_normSq_upper ts hvalid f g h
      _ = (productK ts)^2 *
          (energy ts f * energy ts g * energy ts h) := by ring
      _ ≤ B * (energy ts f * energy ts g * energy ts h) :=
          mul_le_mul_of_nonneg_right hB hE
      _ = _ := by ring

#print axioms ComplexPencilTensor.tensorSquaredBound_iff

end
end ComplexPencilTensor
