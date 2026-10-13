import APPTReview.CanonicalRankBounds

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Exact first moment for the unnormalized physical perturbation. -/
theorem lacunaryPerturbation_trace (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (v : Fin m × Fin n → ℂ) (hv : star v ⬝ᵥ v=1) :
    (lacunaryPerturbation m n ds e a P v).trace.re=
      a+(∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(P d).trace.re) := by
  have ht : (Matrix.vecMulVec v (star v)).trace=1 := by
    have he : (Matrix.vecMulVec v (star v)).trace=star v ⬝ᵥ v := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.vecMulVec_apply,dotProduct,mul_comm]
    exact he.trans hv
  simp only [lacunaryPerturbation,Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,ht,
    Complex.add_re,Complex.re_sum,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one]
  ring

/-- Exact floor ranks and positive cross moments give finite physical bounds. -/
theorem canonical_perturbation_moments {m n : ℕ} (hm : 1≤m) (hmn : m≤n)
    (ds : List ℝ) (hd : ∀ d∈ds,0≤d) (e : ℝ → ℝ) (he : ∀ d∈ds,0≤e d)
    (a : ℝ) (ha : 0≤a) (v : Fin m × Fin n → ℂ) (hv : star v ⬝ᵥ v=1) :
    let Y := lacunaryPerturbation m n ds e a (canonicalScaleProjection m n) v
    0≤Y.trace.re ∧ Y.trace.re≤(m:ℝ)*lacunaryTraceError ds e a m ∧
    0≤(Y*Y).trace.re ∧
    a^2+(∑ d∈ds.toFinset,e d)-lacunaryMomentError ds e m≤(Y*Y).trace.re := by
  dsimp only
  let P := canonicalScaleProjection m n
  let Y := lacunaryPerturbation m n ds e a P v
  have hP (d) (h : d∈ds) : (P d).PosSemidef := (canonicalScaleProjection_properties m n d).1
  have hY : Y.PosSemidef := lacunaryPerturbation_posSemidef m n ds e a ha P hP v
  have hmP : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  refine ⟨(RCLike.nonneg_iff.mp hY.trace_nonneg).1,?_,positive_product_trace_re Y Y hY hY,?_⟩
  · rw [lacunaryPerturbation_trace m n ds e a P v hv]
    have hp (d : ℝ) (h : d∈ds.toFinset) :
        (Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(P d).trace.re≤
        (m:ℝ)*(Real.sqrt (e d)*(m:ℝ)^(-d/2)) := by
      rw [← canonical_trace_identity (m:ℝ) d (e d) hmP]
      exact mul_le_mul_of_nonneg_left (canonicalScaleProjection_properties m n d).2.2.2
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hmP.le _))
    have hh := Finset.sum_le_sum hp
    rw [← Finset.mul_sum] at hh
    have hid : (m:ℝ)*(a*(m:ℝ)^(-1:ℝ))=a := by
      rw [Real.rpow_neg_one]
      field_simp
    dsimp only [lacunaryTraceError]
    rw [mul_add,hid]
    linarith
  · have hl := lacunaryPerturbation_square_lower m n ds e a ha P hP
      (fun d _ => (canonicalScaleProjection_properties m n d).2.2.1) v hv
    have hp := Finset.sum_le_sum (fun d (h : d∈ds.toFinset) =>
      canonical_projection_energy_lower hm hmn d (e d) (hd d (List.mem_toFinset.mp h)) (he d (List.mem_toFinset.mp h)))
    simp only [Finset.sum_sub_distrib] at hp
    change a^2+(∑ d∈ds.toFinset,e d)-(∑ d∈ds.toFinset,e d*(m:ℝ)^(d-2))≤_
    dsimp only [P] at hl
    linarith

end APPTReview
