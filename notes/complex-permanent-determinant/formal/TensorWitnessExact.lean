import TensorFactor

namespace ComplexPencilTensor

noncomputable section

def extF (t : ℝ) (j : Fin 3) : ℂ := (extremalF t j : ℂ)
def extG (t : ℝ) (j : Fin 3) : ℂ := (extremalG t j : ℂ)
def extH (t : ℝ) (j : Fin 3) : ℂ := (extremalH t j : ℂ)

theorem localEnergy_extF (t : ℝ) :
    localEnergy extF t = realEnergy (extremalF t) := by
  simp [localEnergy, realEnergy, extF, Complex.normSq_ofReal]
  ring

theorem localEnergy_extG (t : ℝ) :
    localEnergy extG t = realEnergy (extremalG t) := by
  simp [localEnergy, realEnergy, extG, Complex.normSq_ofReal]
  ring

theorem localEnergy_extH (t : ℝ) :
    localEnergy extH t = realEnergy (extremalH t) := by
  simp [localEnergy, realEnergy, extH, Complex.normSq_ofReal]
  ring

theorem weightedVal_ext (t : ℝ) :
    weightedVal t extF extG extH =
       (realWeighted t (extremalF t) (extremalG t)
          (extremalH t) : ℂ) := by
  unfold weightedVal
  rw [weightedSix_explicit, realWeighted_explicit]
  simp only [extF,extG,extH,Complex.ofReal_add,Complex.ofReal_mul]
  push_cast
  simp [first, second, third] <;> ring

theorem weightedVal_ext_normSq (t : ℝ) :
    Complex.normSq (weightedVal t extF extG extH) =
      kappaSq t * localEnergy extF t *
       localEnergy extG t * localEnergy extH t := by
  rw [weightedVal_ext, Complex.normSq_ofReal,
      localEnergy_extF, localEnergy_extG, localEnergy_extH]
  simpa only [pow_two] using extremal_square_saturation t

theorem localEnergy_extF_pos (t : ℝ) : 0 < localEnergy extF t := by
  rw [localEnergy_extF]
  exact (extremal_energy_pos t).1

theorem localEnergy_extG_pos (t : ℝ) : 0 < localEnergy extG t := by
  rw [localEnergy_extG]
  exact (extremal_energy_pos t).2.1

theorem localEnergy_extH_pos (t : ℝ) : 0 < localEnergy extH t := by
  rw [localEnergy_extH]
  exact (extremal_energy_pos t).2.2

theorem productEnergy_pos (fa : ℝ → Fin 3 → ℂ)
    (hfa : ∀ t, 0 < localEnergy fa t) (ts : List ℝ) :
    0 < productEnergy fa ts := by
  induction ts with
  | nil => simp [productEnergy]
  | cons t ts ih =>
    simp only [productEnergy]
    exact mul_pos (hfa t) ih

theorem momentProduct_ext_normSq (ts : List ℝ) :
    Complex.normSq (momentProduct extF extG extH ts) =
       productKSq ts * productEnergy extF ts *
         productEnergy extG ts * productEnergy extH ts := by
  induction ts with
  | nil =>
    simp [momentProduct, productKSq, productEnergy]
  | cons t ts ih =>
    simp only [momentProduct, productKSq, productEnergy,
      Complex.normSq_mul]
    rw [weightedVal_ext_normSq, ih]
    ring

theorem tensor_extremal_normSq (ts : List ℝ) :
    Complex.normSq
      (tensor ts (productEntries extF ts)
        (productEntries extG ts) (productEntries extH ts)) =
    (productK ts)^2 *
      energy ts (productEntries extF ts) *
      energy ts (productEntries extG ts) *
      energy ts (productEntries extH ts) := by
  rw [tensor_productEntries,
      energy_productEntries, energy_productEntries,
      energy_productEntries, productK_sq]
  exact momentProduct_ext_normSq ts

#print axioms ComplexPencilTensor.tensor_extremal_normSq

end
end ComplexPencilTensor
