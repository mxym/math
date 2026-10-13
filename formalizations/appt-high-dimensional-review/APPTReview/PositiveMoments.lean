import APPTReview.CompressionTrace
import APPTReview.CanonicalLacunaryState
import APPTReview.EffectiveLowerScalar

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Cross moments of PSD summands are nonnegative even without commutation.
Thus a second-moment lower bound does not require nested projections. -/
theorem positive_sum_square_trace_lower {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (X : κ → Matrix ι ι ℂ) (hX : ∀ k∈S,(X k).PosSemidef) :
    (∑ k∈S,(X k*X k).trace.re)≤((∑ k∈S,X k)*(∑ k∈S,X k)).trace.re := by
  have hr (k : κ) (hk : k∈S) : (X k*X k).trace.re≤∑ l∈S,(X k*X l).trace.re := by
    exact Finset.single_le_sum (fun l hl => positive_product_trace_re (X k) (X l) (hX k hk) (hX l hl)) hk
  have hh := Finset.sum_le_sum hr
  simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
  rw [Finset.sum_comm]
  exact hh

/-- Adding one more positive summand preserves the diagonal second-moment budget. -/
theorem positive_add_square_trace_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X*X).trace.re+(Y*Y).trace.re≤((X+Y)*(X+Y)).trace.re := by
  have hxy := positive_product_trace_re X Y hX hY
  have hyx := positive_product_trace_re Y X hY hX
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.trace_add,Complex.add_re]
  linarith

/-- Exact purity of a real-trace-normalized perturbation of the identity. -/
theorem normalized_identity_purity {m n : ℕ}
    (Y : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    APPT.Quantum.purity ((1/((m:ℝ)*n+Y.trace.re):ℝ) • (1+Y))=
      ((m:ℝ)*n+2*Y.trace.re+(Y*Y).trace.re)/((m:ℝ)*n+Y.trace.re)^2 := by
  have he : (1+Y)*(1+Y)=(1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+Y+Y+Y*Y := by
    noncomm_ring
  unfold APPT.Quantum.purity
  rw [Matrix.smul_mul,Matrix.mul_smul,he]
  simp only [Matrix.trace_smul,Matrix.trace_add,Matrix.trace_one,Complex.smul_re,
    Complex.add_re,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Complex.mul_re,
    Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero,smul_eq_mul]
  simp only [div_eq_mul_inv,← inv_pow]
  ring

noncomputable def lacunaryPerturbation (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (v : Fin m × Fin n → ℂ) :=
  (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d)+a • Matrix.vecMulVec v (star v)

theorem pure_unit_square_trace {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (hv : star v ⬝ᵥ v=1) :
    (Matrix.vecMulVec v (star v)*Matrix.vecMulVec v (star v)).trace.re=1 := by
  rw [Matrix.vecMulVec_mul_vecMulVec,hv,one_smul]
  have ht : (Matrix.vecMulVec v (star v)).trace=star v ⬝ᵥ v := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.vecMulVec_apply,dotProduct,mul_comm]
  rw [ht,hv]
  rfl

theorem lacunaryPerturbation_posSemidef (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (ha : 0≤a) (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (v : Fin m × Fin n → ℂ) :
    (lacunaryPerturbation m n ds e a P v).PosSemidef := by
  have hsum : (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d).PosSemidef := by
    apply Finset.sum_induction (s:=ds.toFinset)
      (fun d : ℝ => (Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d)
      (fun Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ => Q.PosSemidef)
      (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    intro d hd
    exact (hP d (List.mem_toFinset.mp hd)).smul
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  exact hsum.add ((Matrix.posSemidef_vecMulVec_self_star v).smul ha)

/-- The physical second moment contains all individual scale energies and the
spike energy. Positive cross traces are retained as a proved lower bound. -/
theorem lacunaryPerturbation_square_lower (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (ha : 0≤a) (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (hPsq : ∀ d∈ds,P d*P d=P d)
    (v : Fin m × Fin n → ℂ) (hv : star v ⬝ᵥ v=1) :
    a^2+(∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))^2*(P d).trace.re)≤
      ((lacunaryPerturbation m n ds e a P v)*(lacunaryPerturbation m n ds e a P v)).trace.re := by
  let X := fun d => (Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d
  let Y := ∑ d∈ds.toFinset,X d
  let V := a • Matrix.vecMulVec v (star v)
  have hX (d) (hd : d∈ds.toFinset) : (X d).PosSemidef :=
    (hP d (List.mem_toFinset.mp hd)).smul
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  have hY : Y.PosSemidef := Finset.sum_induction X
    (fun Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ => Q.PosSemidef)
    (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero hX
  have hV : V.PosSemidef := (Matrix.posSemidef_vecMulVec_self_star v).smul ha
  have hsum := positive_sum_square_trace_lower ds.toFinset X hX
  have hadd := positive_add_square_trace_lower Y V hY hV
  have hVsq : (V*V).trace.re=a^2 := by
    simp only [V,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul,
      pure_unit_square_trace v hv]
    ring
  have hXs (d) (hd : d∈ds.toFinset) : (X d*X d).trace.re=
      (Real.sqrt (e d)*(m:ℝ)^(d/2-1))^2*(P d).trace.re := by
    simp only [X,Matrix.smul_mul,Matrix.mul_smul,hPsq d (List.mem_toFinset.mp hd),
      Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hXs] at hsum
  rw [hVsq] at hadd
  change a^2+_≤((Y+V)*(Y+V)).trace.re
  linarith

end APPTReview
