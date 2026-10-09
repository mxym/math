import CofactorGeometricTail

/-! The actual binomial-weighted subset sum is at most one plus a vanishing integer tail. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem ring_subset_sum_le_one_add_tail {K : Type*} [Fintype K] [LinearOrder K]
    (N : ℕ) (hN : 0 < N) (C b δ : ℝ) (hC : 0 < C) (hb : 1 < b) (hδ : δ < 1)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1)
    (d : K → ℕ) (hd : ∀ k, 0 < d k)
    (hsep : ∀ i j, i < j → b*(d i : ℝ) ≤ (d j : ℝ))
    (hD : 2*∑ k, d k ≤ N) (hfrac : (2*∑ k, d k : ℕ) ≤ δ*(N : ℝ))
    (m : ℕ) (hmin : ∀ k, m ≤ d k) (hinj : Function.Injective d) :
    (∑ s : Finset K, (ringAmplitude d (ringRadius N C d) s)^2 /
      (N.choose (2*∑ k ∈ s, d k) : ℝ)) ≤
      1+ringTailBound ((entropyConstant b/(C*Real.exp 1*(1-δ)))^2) m := by
  classical
  let θ := entropyConstant b/(C*Real.exp 1*(1-δ))
  let q := θ^2
  let W : Finset K → ℝ := fun s => (ringAmplitude d (ringRadius N C d) s)^2 /
    (N.choose (2*∑ k ∈ s, d k) : ℝ)
  let U : Finset K → ℝ := fun s => (∑ k ∈ s, d k : ℕ)*q^(∑ k ∈ s, d k)
  have hθ0 : 0 < θ := div_pos (entropyConstant_pos b hb)
    (mul_pos (mul_pos hC (Real.exp_pos _)) (sub_pos.mpr hδ))
  have hq0 : 0 ≤ q := sq_nonneg θ
  have hq1 : q < 1 := by dsimp [q]; nlinarith
  have hW0 : W ∅ = 1 := by simp [W,ringAmplitude]
  have hsplit : (∑ s, W s) = 1+∑ s ∈ Finset.univ.erase ∅, W s := by
    exact (Finset.add_sum_erase Finset.univ W (Finset.mem_univ ∅)).symm.trans
      (by rw [hW0])
  have hweights : (∑ s ∈ Finset.univ.erase ∅, W s) ≤ 2*Real.exp 1*∑ s, U s := by
    calc
      _ ≤ ∑ s ∈ Finset.univ.erase ∅, 2*Real.exp 1*U s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
        have h := ring_subset_weight_bound N hN C b δ hC hb hδ d hd hsep hD hfrac s hsne
        have he : θ^(2*∑ k ∈ s, d k) = q^(∑ k ∈ s, d k) := by rw [pow_mul]
        change W s ≤ 2*Real.exp 1*(∑ k ∈ s, d k : ℕ)*θ^(2*∑ k ∈ s, d k) at h
        rw [he] at h
        simpa only [U,mul_assoc] using h
      _ ≤ ∑ s, 2*Real.exp 1*U s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro s _ _
        dsimp [U]
        positivity
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htail := geometric_subset_integer_tail_bound q hq0 hq1 m d hinj hmin
  change 2*Real.exp 1*(∑ s, U s) ≤ ringTailBound q m at htail
  rw [hsplit]
  linarith

end
end CofactorSpectral
