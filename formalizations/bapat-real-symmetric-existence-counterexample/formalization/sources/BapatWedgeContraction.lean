import BapatRatioCoordinates
import BapatSelectedPeak

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions

namespace BapatRealExistence
noncomputable section

def exteriorCoefficient (u w : EuclideanSpace ℂ (Fin 4)) (a b : Fin 4) : ℂ :=
  u a*w b-u b*w a

theorem complex_wedge_contraction {n : ℕ} (v : Fin n → Fin 4 → ℝ) (i j : Fin n)
    (u w : EuclideanSpace ℂ (Fin 4)) :
    (∑ p ∈ originalPairs (ι := Fin 4), ((wedge v i j p.1 p.2 : ℝ) : ℂ)*exteriorCoefficient u w p.1 p.2) =
      realComplexLinear (WithLp.toLp 2 (v i)) u * realComplexLinear (WithLp.toLp 2 (v j)) w -
        realComplexLinear (WithLp.toLp 2 (v i)) w * realComplexLinear (WithLp.toLp 2 (v j)) u := by
  simpa only [wedge,Complex.ofReal_sub,Complex.ofReal_mul,exteriorCoefficient,realComplexLinear] using
    (dot_minor_eq_wedges (fun a => (v i a:ℂ)) (fun a => (v j a:ℂ)) (fun a => u a) (fun a => w a)).symm

theorem complexEval_product_split_two {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {i j : Fin n} (hij : i≠j) (u : EuclideanSpace ℂ (Fin 4)) :
    complexEval (formsProduct v) u =
      realComplexLinear (WithLp.toLp 2 (v i)) u * realComplexLinear (WithLp.toLp 2 (v j)) u *
        complexEval (remainingPolynomial v i j) u := by
  have h := product_split_two (fun k => linearForm (v k)) hij
  change formsProduct v = _ at h
  rw [← remainingPolynomial_eq_deleteTwoProduct] at h
  rw [h]
  simp only [complexEval,MvPolynomial.eval₂_mul]
  change complexEval (linearForm (v i)) u * complexEval (linearForm (v j)) u * _ = _
  rw [complexEval_linearForm,complexEval_linearForm]
  rfl

theorem product_linear_ne_zero {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    (u : EuclideanSpace ℂ (Fin 4)) (hp : complexEval (formsProduct v) u≠0) (i : Fin n) :
    realComplexLinear (WithLp.toLp 2 (v i)) u≠0 := by
  rw [complexEval_formsProduct] at hp
  exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)

theorem wedge_polynomial_contraction {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    (u w : EuclideanSpace ℂ (Fin 4)) (hp : complexEval (formsProduct v) u≠0) :
    (∑ c ∈ originalPairs (ι := Fin 4), complexEval (wedgePolynomial v c.1 c.2) u *
      exteriorCoefficient u w c.1 c.2) =
      complexEval (formsProduct v) u * ∑ p ∈ originalPairs (ι := Fin n),
        (realComplexLinear (WithLp.toLp 2 (v p.2)) w / realComplexLinear (WithLp.toLp 2 (v p.2)) u -
         realComplexLinear (WithLp.toLp 2 (v p.1)) w / realComplexLinear (WithLp.toLp 2 (v p.1)) u) := by
  have he (a b : Fin 4) : complexEval (wedgePolynomial v a b) u =
      ∑ p ∈ originalPairs (ι := Fin n), ((wedge v p.1 p.2 a b : ℝ) : ℂ)*complexEval (remainingPolynomial v p.1 p.2) u := by
    simp [wedgePolynomial,complexEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul]
  simp_rw [he,Finset.sum_mul]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp'
  have hij : p.1≠p.2 := (Finset.mem_filter.mp hp').2.ne
  have hc := complex_wedge_contraction v p.1 p.2 u w
  have hf := complexEval_product_split_two v hij u
  have hi := product_linear_ne_zero v u hp p.1
  have hj := product_linear_ne_zero v u hp p.2
  calc
    _ = (∑ c ∈ originalPairs (ι := Fin 4), ((wedge v p.1 p.2 c.1 c.2 : ℝ) : ℂ)*
          exteriorCoefficient u w c.1 c.2)*complexEval (remainingPolynomial v p.1 p.2) u := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = _ := by rw [hc,hf]; field_simp <;> ring

/-- Cauchy--Schwarz controls a unit exterior coefficient contraction. -/
theorem exterior_contraction_bound {n : ℕ} (v : Fin n → Fin 4 → ℝ) (z : ComplexUnitSphere4)
    (c : Fin 4 × Fin 4 → ℂ) (hc : ∑ p ∈ originalPairs (ι := Fin 4), ‖c p‖^2=1) :
    ‖∑ p ∈ originalPairs (ι := Fin 4), complexEval (wedgePolynomial v p.1 p.2) z * c p‖^2 ≤ rowWedgeEnergy v z := by
  have hnorm := norm_sum_le (originalPairs (ι := Fin 4))
    (fun p => complexEval (wedgePolynomial v p.1 p.2) z*c p)
  simp only [norm_mul] at hnorm
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (originalPairs (ι := Fin 4))
    (fun p => ‖complexEval (wedgePolynomial v p.1 p.2) z‖) (fun p => ‖c p‖)
  rw [hc,mul_one] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => by positivity))).mpr hnorm |>.trans hs

end
end BapatRealExistence
