import TensorOne

namespace ComplexPencilTensor

noncomputable section

theorem norm_eq_sqrt_complex_normSq (z : ℂ) :
    ‖z‖=Real.sqrt (Complex.normSq z) := by
  rw [Complex.normSq_eq_norm_sq]
  rw [Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (norm_nonneg z)).symm

theorem tensorized_complex_norm_bound
    (ts : List ℝ)
    (hvalid : ∀ t ∈ ts, |t|≤(1/6:ℝ))
    (f g h : List (Fin 3) → ℂ) :
    ‖tensor ts f g h‖ ≤
       productK ts*Real.sqrt (energy ts f)*
         Real.sqrt (energy ts g)*Real.sqrt (energy ts h) := by
  induction ts generalizing f g h with
  | nil =>
    simp only [tensor,productK,energy,one_mul]
    rw [norm_mul,norm_mul,
        norm_eq_sqrt_complex_normSq,
        norm_eq_sqrt_complex_normSq,
        norm_eq_sqrt_complex_normSq] <;> ring
  | cons t ts ih =>
    have ht : |t|≤(1/6:ℝ) := hvalid t (by simp)
    have htail : ∀ r ∈ ts, |r|≤(1/6:ℝ) := by
      intro r hr
      exact hvalid r (by simp [hr])
    let ff : Fin 3 → ℝ :=
      fun j => Real.sqrt (energy ts (slice f j))
    let gg : Fin 3 → ℝ :=
      fun j => Real.sqrt (energy ts (slice g j))
    let hh : Fin 3 → ℝ :=
      fun j => Real.sqrt (energy ts (slice h j))
    have hff : ∀ j,0≤ff j := by intro j; exact Real.sqrt_nonneg _
    have hgg : ∀ j,0≤gg j := by intro j; exact Real.sqrt_nonneg _
    have hhh : ∀ j,0≤hh j := by intro j; exact Real.sqrt_nonneg _
    have hj (j : Fin 6) :
      ‖tensor ts (slice f (first j))
          (slice g (second j)) (slice h (third j))‖ ≤
      productK ts*ff (first j)*gg (second j)*hh (third j) := by
        simpa only [ff,gg,hh] using
          ih htail (slice f (first j))
            (slice g (second j)) (slice h (third j))
    have hfE : realEnergy ff=energy (t::ts) f := by
      unfold realEnergy
      change
        ((Real.sqrt (energy ts (slice f 0)))^2+
         (Real.sqrt (energy ts (slice f 1)))^2+
         (Real.sqrt (energy ts (slice f 2)))^2)/3 =
           energy (t::ts) f
      rw [Real.sq_sqrt (energy_nonneg ts (slice f 0)),
        Real.sq_sqrt (energy_nonneg ts (slice f 1)),
        Real.sq_sqrt (energy_nonneg ts (slice f 2))]
      rfl
    have hgE : realEnergy gg=energy (t::ts) g := by
      unfold realEnergy
      change
        ((Real.sqrt (energy ts (slice g 0)))^2+
         (Real.sqrt (energy ts (slice g 1)))^2+
         (Real.sqrt (energy ts (slice g 2)))^2)/3 =
           energy (t::ts) g
      rw [Real.sq_sqrt (energy_nonneg ts (slice g 0)),
        Real.sq_sqrt (energy_nonneg ts (slice g 1)),
        Real.sq_sqrt (energy_nonneg ts (slice g 2))]
      rfl
    have hhE : realEnergy hh=energy (t::ts) h := by
      unfold realEnergy
      change
        ((Real.sqrt (energy ts (slice h 0)))^2+
         (Real.sqrt (energy ts (slice h 1)))^2+
         (Real.sqrt (energy ts (slice h 2)))^2)/3 =
           energy (t::ts) h
      rw [Real.sq_sqrt (energy_nonneg ts (slice h 0)),
        Real.sq_sqrt (energy_nonneg ts (slice h 1)),
        Real.sq_sqrt (energy_nonneg ts (slice h 2))]
      rfl
    calc
      ‖tensor (t::ts) f g h‖ =
       ‖weightedSix t (fun j=>
          tensor ts (slice f (first j))
            (slice g (second j)) (slice h (third j)))‖ := rfl
      _ ≤ ∑ j : Fin 6, weight t j*
           ‖tensor ts (slice f (first j))
             (slice g (second j)) (slice h (third j))‖ :=
          weightedSix_norm_le t ht _
      _ ≤ ∑ j : Fin 6, weight t j*
          (productK ts*ff (first j)*gg (second j)*hh (third j)) := by
          apply Finset.sum_le_sum
          intro j hjmem
          exact mul_le_mul_of_nonneg_left (hj j)
             (weight_nonneg t ht j)
      _ = productK ts*realWeighted t ff gg hh := by
          unfold realWeighted
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hjmem
          ring
      _ ≤ productK ts*(kappa t*Real.sqrt (realEnergy ff)*
             Real.sqrt (realEnergy gg)*Real.sqrt (realEnergy hh)) :=
          mul_le_mul_of_nonneg_left
             (realWeighted_root_bound t ht ff gg hh hff hgg hhh)
             (productK_nonneg ts)
      _ = productK (t::ts)*Real.sqrt (energy (t::ts) f)*
          Real.sqrt (energy (t::ts) g)*Real.sqrt (energy (t::ts) h) := by
          rw [hfE,hgE,hhE]
          simp only [productK]
          ring

#print axioms ComplexPencilTensor.tensorized_complex_norm_bound

end
end ComplexPencilTensor
