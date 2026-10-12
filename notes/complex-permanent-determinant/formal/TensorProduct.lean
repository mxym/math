import TensorWitnessLocal

namespace ComplexPencilTensor

noncomputable section

theorem weightedSix_const_mul (t : ℝ) (c : ℂ)
    (z : Fin 6 → ℂ) :
    weightedSix t (fun j => c*z j) = c*weightedSix t z := by
  unfold weightedSix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tensor_scale
    (ts : List ℝ) (c d e : ℂ)
    (f g h : List (Fin 3) → ℂ) :
 tensor ts (fun xs => c*f xs)
           (fun xs => d*g xs) (fun xs => e*h xs) =
    c*d*e*tensor ts f g h := by
  induction ts generalizing f g h with
  | nil =>
      simp only [tensor]
      ring
  | cons t ts ih =>
      change weightedSix t (fun j =>
        tensor ts (fun xs => c*(slice f (first j) xs))
          (fun xs => d*(slice g (second j) xs))
          (fun xs => e*(slice h (third j) xs))) =
        c*d*e*weightedSix t (fun j =>
          tensor ts (slice f (first j))
            (slice g (second j)) (slice h (third j)))
      simp only [ih]
      exact weightedSix_const_mul t (c*d*e) _

theorem energy_scale
    (ts : List ℝ) (c : ℂ) (f : List (Fin 3) → ℂ) :
    energy ts (fun xs => c*f xs) =
       Complex.normSq c * energy ts f := by
  induction ts generalizing f with
  | nil =>
      simp only [energy]
      rw [Complex.normSq_mul]
  | cons t ts ih =>
      simp only [energy]
      have h0 : energy ts (slice (fun xs => c*f xs) 0) =
        Complex.normSq c * energy ts (slice f 0) := by
          exact ih (slice f 0)
      have h1 : energy ts (slice (fun xs => c*f xs) 1) =
        Complex.normSq c * energy ts (slice f 1) := by
          exact ih (slice f 1)
      have h2 : energy ts (slice (fun xs => c*f xs) 2) =
        Complex.normSq c * energy ts (slice f 2) := by
          exact ih (slice f 2)
      rw [h0, h1, h2]
      ring


def productEntries (valF : ℝ → Fin 3 → ℂ) :
    (ts : List ℝ) → (List (Fin 3) → ℂ)
| [], _ => 1
| _::_, [] => 0
| t::ts, j::xs => valF t j * productEntries valF ts xs

def localEnergy (valF : ℝ → Fin 3 → ℂ) (t : ℝ) : ℝ :=
   (Complex.normSq (valF t 0)+Complex.normSq (valF t 1)+
    Complex.normSq (valF t 2))/3

def productEnergy (valF : ℝ → Fin 3 → ℂ) : List ℝ → ℝ
| [] => 1
| t::ts => localEnergy valF t * productEnergy valF ts

theorem productEntries_slice (valF : ℝ → Fin 3 → ℂ)
    (t : ℝ) (ts : List ℝ) (j : Fin 3) :
    slice (productEntries valF (t::ts)) j =
      fun xs => valF t j * productEntries valF ts xs := by
  funext xs
  rfl

theorem energy_productEntries (valF : ℝ → Fin 3 → ℂ)
    (ts : List ℝ) :
 energy ts (productEntries valF ts) =
   productEnergy valF ts := by
  induction ts with
  | nil =>
      simp [productEntries,productEnergy,energy]
  | cons t ts ih =>
      change
        (energy ts (slice (productEntries valF (t::ts)) 0)+
         energy ts (slice (productEntries valF (t::ts)) 1)+
         energy ts (slice (productEntries valF (t::ts)) 2))/3 =
          localEnergy valF t * productEnergy valF ts
      rw [productEntries_slice,productEntries_slice,productEntries_slice]
      rw [energy_scale,energy_scale,energy_scale]
      rw [ih]
      unfold localEnergy
      ring

#print axioms ComplexPencilTensor.tensor_scale
#print axioms ComplexPencilTensor.energy_productEntries

end
end ComplexPencilTensor
