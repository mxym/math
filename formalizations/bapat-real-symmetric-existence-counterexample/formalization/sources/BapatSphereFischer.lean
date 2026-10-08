import BapatSphereMoments
import BapatHomogeneous

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ComplexConjugate
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def complexEval (p : MvPolynomial ι ℝ) (z : EuclideanSpace ℂ ι) : ℂ :=
  p.eval₂ Complex.ofRealHom (fun i => z i)

theorem complexEval_expand (p : MvPolynomial ι ℝ) (z : EuclideanSpace ℂ ι) :
    complexEval p z = ∑ α ∈ p.support, (p.coeff α : ℂ) * complexMonomial α z :=
  MvPolynomial.eval₂_eq' _ _ _

@[fun_prop] theorem complexMonomial_continuous (α : ι → ℕ) : Continuous (complexMonomial α) := by
  unfold complexMonomial
  fun_prop

@[fun_prop] theorem complexEval_continuous (p : MvPolynomial ι ℝ) : Continuous (complexEval p) := by
  simp_rw [funext (complexEval_expand p)]
  fun_prop (disch := exact complexMonomial_continuous _)

theorem homogeneous_degree_of_mem_support (p : MvPolynomial ι ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (α : ι →₀ ℕ) (hα : α ∈ p.support) :
    ∑ i, α i = d := by
  have h := hp (MvPolynomial.mem_support_iff.mp hα)
  simpa [Finsupp.weight_eq_sum, Pi.one_apply] using h

theorem complexEval_pair_expand (p q : MvPolynomial ι ℝ) (z : EuclideanSpace ℂ ι) :
    complexEval p z * conj (complexEval q z) =
      ∑ α ∈ p.support, ∑ β ∈ q.support,
        (p.coeff α : ℂ) * (q.coeff β : ℂ) *
          (complexMonomial α z * conj (complexMonomial β z)) := by
  simp only [complexEval_expand, _root_.map_sum, map_mul, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

/-- Fischer pairing of real homogeneous polynomials is their complex-sphere pairing. -/
theorem sphere_fischer_pair (p q : MvPolynomial ι ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    (∫ z : sphere (0 : EuclideanSpace ℂ ι) 1,
      complexEval p z * conj (complexEval q z)
      ∂normalizedSphere (complexProductHaar ι)) =
      (((Fintype.card ι-1).factorial : ℂ) / ((Fintype.card ι+d-1).factorial : ℂ)) *
        ((fischerPair p q : ℝ) : ℂ) := by
  let μ := normalizedSphere (complexProductHaar ι)
  have hi (α β : ι →₀ ℕ) : Integrable (fun z : sphere (0 : EuclideanSpace ℂ ι) 1 =>
      (p.coeff α : ℂ) * (q.coeff β : ℂ) *
        (complexMonomial α z * conj (complexMonomial β z))) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop (disch := exact complexMonomial_continuous _)
  simp_rw [complexEval_pair_expand]
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hi α β))]
  simp only [fischerPair, MvPolynomial.sum_def, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [integral_finsetSum _ (fun β _ => hi α β)]
  simp_rw [integral_const_mul]
  have hαd := homogeneous_degree_of_mem_support p d hp α hα
  have hm (β : ι →₀ ℕ) (hβ : β ∈ q.support) := complex_sphere_moment α β d hαd
    (homogeneous_degree_of_mem_support q d hq β hβ)
  rw [Finset.sum_congr rfl (fun β hβ => congrArg
    (fun w : ℂ => (p.coeff α : ℂ) * (q.coeff β : ℂ) * w) (hm β hβ))]
  by_cases hαq : α ∈ q.support
  · simp [DFunLike.coe_fn_eq, hαq, multiFactorial, mul_ite]
    ring
  · have hz : q.coeff α = 0 := not_not.mp (fun hn => hαq (MvPolynomial.mem_support_iff.mpr hn))
    simp [DFunLike.coe_fn_eq, hαq, hz, mul_ite]

/-- The real Fischer norm is the squared-modulus integral with the exact factor. -/
theorem sphere_fischer_norm (p : MvPolynomial ι ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    (∫ z : sphere (0 : EuclideanSpace ℂ ι) 1, ‖complexEval p z‖^2
      ∂normalizedSphere (complexProductHaar ι)) =
      ((Fintype.card ι-1).factorial : ℝ) / ((Fintype.card ι+d-1).factorial : ℝ) *
        fischerNormSq p := by
  have h := sphere_fischer_pair p p d hp hp
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, fischerNormSq] using h

theorem fischer_norm_from_sphere (p : MvPolynomial ι ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    fischerNormSq p =
      ((Fintype.card ι+d-1).factorial : ℝ) / ((Fintype.card ι-1).factorial : ℝ) *
        (∫ z : sphere (0 : EuclideanSpace ℂ ι) 1, ‖complexEval p z‖^2
          ∂normalizedSphere (complexProductHaar ι)) := by
  rw [sphere_fischer_norm p d hp]
  have h0 : ((Fintype.card ι-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hd : ((Fintype.card ι+d-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem rank_four_fischer_norm (p : MvPolynomial (Fin 4) ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    fischerNormSq p = ((d+3).factorial : ℝ) / 6 *
      (∫ z : sphere (0 : EuclideanSpace ℂ (Fin 4)) 1, ‖complexEval p z‖^2
        ∂normalizedSphere (complexProductHaar (Fin 4))) := by
  simpa [Nat.add_comm, Nat.factorial] using fischer_norm_from_sphere p d hp

@[simp] theorem complexEval_mul (p q : MvPolynomial ι ℝ) (z : EuclideanSpace ℂ ι) :
    complexEval (p*q) z = complexEval p z * complexEval q z :=
  MvPolynomial.eval₂_mul _ _

@[simp] theorem complexEval_pow (p : MvPolynomial ι ℝ) (k : ℕ) (z : EuclideanSpace ℂ ι) :
    complexEval (p^k) z = (complexEval p z)^k :=
  MvPolynomial.eval₂_pow _ _

end
end BapatRealExistence
