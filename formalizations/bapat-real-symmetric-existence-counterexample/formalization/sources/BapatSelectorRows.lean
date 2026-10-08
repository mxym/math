import BapatSelectorPeaks

set_option autoImplicit false
open BapatFiniteRank
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section

@[simp] theorem complexEval_linearForm (v : Fin 4 → ℝ) (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval (linearForm v) z = ∑ i, (v i : ℂ)*z i := by
  simp [complexEval,linearForm,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial,
    Finsupp.prod_single_index]

@[simp] theorem complexEval_formsProduct {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval (formsProduct v) z = ∏ i, (∑ j, (v i j : ℂ)*z j) := by
  unfold formsProduct complexEval
  rw [MvPolynomial.eval₂_prod]
  exact Finset.prod_congr rfl (fun i _ => complexEval_linearForm (v i) z)

theorem complexEval_conjugate (p : MvPolynomial (Fin 4) ℝ)
    (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval p (conjugateComplex4 z) = conj (complexEval p z) := by
  simp [complexEval_expand,complexMonomial,conjugateComplex4]

theorem complexEval_smul_homogeneous (p : MvPolynomial (Fin 4) ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (a : ℂ) (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval p (a • z) = a^d * complexEval p z := by
  simp only [complexEval_expand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hm : complexMonomial α (a • z) = a^(∑ i,α i) * complexMonomial α z := by
    simp only [complexMonomial,PiLp.smul_apply,smul_eq_mul,mul_pow,
      Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [hm,homogeneous_degree_of_mem_support p d hp α hα]
  ring

theorem norm_complexEval_phase (p : MvPolynomial (Fin 4) ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (a : ℂ) (ha : ‖a‖=1) (z : EuclideanSpace ℂ (Fin 4)) :
    ‖complexEval p (a • z)‖ = ‖complexEval p z‖ := by
  rw [complexEval_smul_homogeneous p d hp,norm_mul,norm_pow,ha,one_pow,one_mul]

/-- The four actual real coefficient rows, in the stated order. -/
def selectorRows (c : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![1,0,0,0],![0,1,0,0],![Real.sqrt (1+c),1,0,0],![Real.sqrt (1+c),-1,0,0]]

theorem selectorRows_product {c : ℝ} (hc : 0 ≤ c) (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval (formsProduct (selectorRows c)) z = selectorQuartic c z := by
  have ha : (Real.sqrt (1+c) : ℂ)^2 = ((1+c:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1+c by linarith)
  calc
    _ = z 0 * z 1 * ((Real.sqrt (1+c) : ℂ)^2 * (z 0)^2 - (z 1)^2) := by
      simp [complexEval_formsProduct,selectorRows,Fin.prod_univ_succ,Fin.sum_univ_succ]
      <;> ring
    _ = _ := by rw [ha]; rfl

theorem selectorRows_nonzero {c : ℝ} (hc : 0 ≤ c) (i : Fin 4) : selectorRows c i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> simp [selectorRows] at h0 h1

def appendSelectorRows {n : ℕ} (v : Fin n → Fin 4 → ℝ) (c : ℝ) :
    Fin (n+4) → Fin 4 → ℝ := Fin.append v (selectorRows c)

theorem appendSelectorRows_product {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (z : EuclideanSpace ℂ (Fin 4)) :
    complexEval (formsProduct (appendSelectorRows v c)) z =
      complexEval (formsProduct v) z * selectorQuartic c z := by
  rw [← selectorRows_product hc]
  simp only [complexEval_formsProduct,appendSelectorRows,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]

end
end BapatRealExistence
