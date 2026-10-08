import TensorProduct

namespace ComplexPencilTensor
noncomputable section

def weightedVal (t : ℝ) (fa fb fc : ℝ → Fin 3 → ℂ) : ℂ :=
  weightedSix t (fun j => fa t (first j) * fb t (second j) * fc t (third j))

def momentProduct (fa fb fc : ℝ → Fin 3 → ℂ) : List ℝ → ℂ
| [] => 1
| t :: ts => weightedVal t fa fb fc * momentProduct fa fb fc ts

theorem tensor_productEntries (fa fb fc : ℝ → Fin 3 → ℂ)
    (ts : List ℝ) :
    tensor ts (productEntries fa ts) (productEntries fb ts)
      (productEntries fc ts) = momentProduct fa fb fc ts := by
  induction ts with
  | nil =>
    simp [tensor, productEntries, momentProduct]
  | cons t ts ih =>
    change weightedSix t (fun j =>
      tensor ts
        (slice (productEntries fa (t :: ts)) (first j))
        (slice (productEntries fb (t :: ts)) (second j))
        (slice (productEntries fc (t :: ts)) (third j))) =
      weightedVal t fa fb fc * momentProduct fa fb fc ts
    have hterm (j : Fin 6) :
        tensor ts
          (slice (productEntries fa (t :: ts)) (first j))
          (slice (productEntries fb (t :: ts)) (second j))
          (slice (productEntries fc (t :: ts)) (third j)) =
        (fa t (first j) * fb t (second j) * fc t (third j)) *
          momentProduct fa fb fc ts := by
      rw [productEntries_slice, productEntries_slice, productEntries_slice]
      rw [tensor_scale]
      rw [ih]
    calc
      _ = weightedSix t (fun j =>
          (fa t (first j) * fb t (second j) * fc t (third j)) *
             momentProduct fa fb fc ts) := by
            unfold weightedSix
            apply Finset.sum_congr rfl
            intro j _
            exact congrArg
              (fun z : ℂ => ((weight t j : ℝ) : ℂ) * z)
              (hterm j)
      _ = weightedVal t fa fb fc * momentProduct fa fb fc ts := by
            unfold weightedVal weightedSix
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring

def productKSq : List ℝ → ℝ
| [] => 1
| t :: ts => kappaSq t * productKSq ts

theorem productK_sq (ts : List ℝ) :
    (productK ts)^2 = productKSq ts := by
  induction ts with
  | nil =>
    simp [productK, productKSq]
  | cons t ts ih =>
    simp only [productK, productKSq, mul_pow, kappa_sq, ih]

#print axioms ComplexPencilTensor.tensor_productEntries
#print axioms ComplexPencilTensor.productK_sq

end
end ComplexPencilTensor
