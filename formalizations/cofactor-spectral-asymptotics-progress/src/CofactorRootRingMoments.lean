import CofactorRootRingProduct

/-! Exact first, second, squared-norm and imaginary moments of an actual root ring. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem ringSlope_sum (n : ℕ) (hn : 1 < n) (ζ a : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    (∑ j : Fin n, ringSlope ζ a j) = 0 := by
  unfold ringSlope
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => -(ζ^j*a)) n,
    Finset.sum_neg_distrib,← Finset.sum_mul,hζ.geom_sum_eq_zero hn]
  simp

theorem ringSlope_square_sum (n : ℕ) (hn : 2 < n) (ζ a : ℂ)
    (hζ : IsPrimitiveRoot ζ n) : (∑ j : Fin n, ringSlope ζ a j ^ 2) = 0 := by
  have hn0 : 0 < n := by omega
  have hne : ζ^2 ≠ 1 := (IsPrimitiveRoot.iff hn0).mp hζ |>.2 2 (by omega) hn
  have hpow : (ζ^2)^n = 1 := by
    rw [← pow_mul,mul_comm 2 n,pow_mul,hζ.pow_eq_one,one_pow]
  have hg : (∑ j ∈ Finset.range n, (ζ^2)^j) = 0 := by
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hne.symm)
    rw [mul_neg_geom_sum,hpow,sub_self]
  have ht : ∀ j : Fin n, ringSlope ζ a j ^ 2 = (ζ^2)^j.val*a^2 := by
    intro j
    simp only [ringSlope,neg_sq,mul_pow]
    rw [← pow_mul,mul_comm j.val 2,pow_mul]
  simp_rw [ht]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (ζ^2)^j*a^2) n,
    ← Finset.sum_mul,hg]
  simp

theorem ringSlope_normSq (n : ℕ) (hn : n ≠ 0) (ζ a : ℂ)
    (hζ : IsPrimitiveRoot ζ n) (j : Fin n) :
    Complex.normSq (ringSlope ζ a j) = Complex.normSq a := by
  simp [ringSlope,Complex.normSq_eq_norm_sq,norm_mul,norm_pow,hζ.norm'_eq_one hn]

theorem ringSlope_normSq_sum (n : ℕ) (hn : n ≠ 0) (ζ a : ℂ)
    (hζ : IsPrimitiveRoot ζ n) :
    (∑ j : Fin n, Complex.normSq (ringSlope ζ a j)) = n * Complex.normSq a := by
  simp_rw [ringSlope_normSq n hn ζ a hζ]
  simp

theorem ringSlope_imaginary_square_sum (n : ℕ) (hn : 2 < n) (ζ a : ℂ)
    (hζ : IsPrimitiveRoot ζ n) :
    (∑ j : Fin n, (ringSlope ζ a j).im^2) = (n : ℝ)*Complex.normSq a/2 := by
  have hnorm := ringSlope_normSq_sum n (by omega) ζ a hζ
  have hsq := congrArg Complex.re (ringSlope_square_sum n hn ζ a hζ)
  simp only [Complex.re_sum,Complex.normSq_apply,pow_two,Complex.mul_re,
    Complex.zero_re,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hnorm hsq
  simp only [Complex.normSq_apply,pow_two]
  nlinarith

theorem imaginary_test_sum_of_square_sum_zero {V : Type*} [Fintype V]
    (z : V → ℂ) (hz : ∑ i, z i ^ 2 = 0) :
    (∑ i, ((z i).im : ℂ)*z i) = Complex.I * (∑ i, (z i).im^2 : ℝ) := by
  have h := congrArg Complex.im hz
  simp only [Complex.im_sum,pow_two,Complex.mul_im,Complex.zero_im] at h
  have he : (∑ i, ((z i).re*(z i).im+(z i).im*(z i).re)) =
      2 * ∑ i, (z i).im*(z i).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  have hc : (∑ i, (z i).im*(z i).re) = 0 := by linarith
  apply Complex.ext
  · simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero] using hc
  · simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,zero_add,one_mul,pow_two]
    simp only [add_zero]

end
end CofactorSpectral
