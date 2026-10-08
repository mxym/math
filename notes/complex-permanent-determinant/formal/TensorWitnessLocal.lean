import TensorSemantics

namespace ComplexPencilTensor
noncomputable section
open ComplexPencilReal
attribute [local instance] Classical.propDecidable

def constWins (t : ℝ) : Prop :=
    ((3/4:ℝ)*(1+|6*t|)^2) ≤ 1

def extremalF (t : ℝ) (j : Fin 3) : ℝ := by
  classical
  exact if constWins t then 1 else if j=0 then 1 else 0

def extremalG (t : ℝ) (j : Fin 3) : ℝ := by
  classical
  exact if constWins t then 1 else
    if 0≤t then (if j=1 then 1 else 0)
    else (if j=2 then 1 else 0)

def extremalH (t : ℝ) (j : Fin 3) : ℝ := by
  classical
  exact if constWins t then 1 else
    if 0≤t then (if j=2 then 1 else 0)
    else (if j=1 then 1 else 0)

theorem extremalF_nonneg (t : ℝ) (j : Fin 3) :
    0≤extremalF t j := by
  classical
  unfold extremalF
  split_ifs <;> norm_num

theorem extremalG_nonneg (t : ℝ) (j : Fin 3) :
    0≤extremalG t j := by
  classical
  unfold extremalG
  split_ifs <;> norm_num

theorem extremalH_nonneg (t : ℝ) (j : Fin 3) :
    0≤extremalH t j := by
  classical
  unfold extremalH
  split_ifs <;> norm_num

theorem extremalF_energy (t : ℝ) :
 realEnergy (extremalF t) =
   if constWins t then 1 else (1/3:ℝ) := by
 classical
 by_cases hb : constWins t
 · simp [realEnergy, extremalF, hb] <;> norm_num
 · simp [realEnergy, extremalF, hb] <;> norm_num

theorem extremalG_energy (t : ℝ) :
 realEnergy (extremalG t) =
   if constWins t then 1 else (1/3:ℝ) := by
 classical
 by_cases hb : constWins t
 · simp [realEnergy, extremalG, hb] <;> norm_num
 · by_cases ht : 0≤t
   · simp [realEnergy, extremalG, hb, ht] <;> norm_num
   · simp [realEnergy, extremalG, hb, ht] <;> norm_num

theorem extremalH_energy (t : ℝ) :
 realEnergy (extremalH t) =
   if constWins t then 1 else (1/3:ℝ) := by
 classical
 by_cases hb : constWins t
 · simp [realEnergy, extremalH, hb] <;> norm_num
 · by_cases ht : 0≤t
   · simp [realEnergy, extremalH, hb, ht] <;> norm_num
   · simp [realEnergy, extremalH, hb, ht] <;> norm_num

theorem extremal_weighted_value (t : ℝ) :
 realWeighted t (extremalF t) (extremalG t) (extremalH t) =
    if constWins t then 1 else (1/6+|t|) := by
 classical
 by_cases hb : constWins t
 · rw [realWeighted_explicit]
   simp [extremalF,extremalG,extremalH,hb]
   ring
 · by_cases ht : 0≤t
   · rw [realWeighted_explicit]
     simp [extremalF,extremalG,extremalH,hb,ht,
       abs_of_nonneg ht]
   · rw [realWeighted_explicit]
     simp [extremalF,extremalG,extremalH,hb,ht,
       abs_of_nonpos (le_of_not_ge ht)]
     ring

theorem extremal_energy_pos (t : ℝ) :
  0<realEnergy (extremalF t) ∧
  0<realEnergy (extremalG t) ∧
  0<realEnergy (extremalH t) := by
  rw [extremalF_energy,extremalG_energy,extremalH_energy]
  split_ifs <;> norm_num

theorem extremal_weighted_nonneg (t : ℝ) :
    0≤realWeighted t (extremalF t) (extremalG t)
      (extremalH t) := by
  rw [extremal_weighted_value]
  split_ifs <;> positivity

theorem extremal_square_saturation (t : ℝ) :
  (realWeighted t (extremalF t) (extremalG t)
     (extremalH t))^2 =
  kappaSq t * realEnergy (extremalF t) *
    realEnergy (extremalG t) *
    realEnergy (extremalH t) := by
  rw [extremal_weighted_value,extremalF_energy,
    extremalG_energy,extremalH_energy]
  by_cases hb : constWins t
  · have hk : kappaSq t = 1 := by
      unfold kappaSq
      exact max_eq_left hb
    simp [hb,hk]
  · have hlarge : 1≤(3/4:ℝ)*(1+|6*t|)^2 :=
       le_of_not_ge hb
    have hk : kappaSq t = (3/4:ℝ)*(1+|6*t|)^2 := by
      unfold kappaSq
      exact max_eq_right hlarge
    simp [hb,hk,abs_mul]
    ring

#print axioms ComplexPencilTensor.extremal_square_saturation

end
end ComplexPencilTensor
