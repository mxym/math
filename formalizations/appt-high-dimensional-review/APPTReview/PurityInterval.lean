import APPTReview.PurityMixing
import Mathlib.Topology.Order.IntermediateValue

open scoped BigOperators ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix
namespace APPTReview

noncomputable def maximallyMixed (m n : ℕ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1/((m:ℝ)*n)) • 1

theorem maximallyMixed_density {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    APPT.Quantum.IsDensity (maximallyMixed m n) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  constructor
  · exact Matrix.PosSemidef.one.smul (by positivity : (0:ℝ)≤1/((m:ℝ)*n))
  · simp [maximallyMixed, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]
    field_simp

theorem maximallyMixed_appt (m n : ℕ) : APPT.Quantum.AbsolutelyPPT (maximallyMixed m n) := by
  intro U
  have he : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)*maximallyMixed m n*
      (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ=maximallyMixed m n := by
    simp [maximallyMixed, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self]
  rw [he]
  simpa [maximallyMixed] using (Matrix.PosSemidef.one.smul
    (by positivity : (0:ℝ)≤1/((m:ℝ)*n)))

theorem maximallyMixed_purity {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    APPT.Quantum.purity (maximallyMixed m n)=1/((m:ℝ)*n) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [APPT.Quantum.purity, maximallyMixed, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]
  field_simp

/-- Exact Hilbert--Schmidt identity, including the original trace-one normalization. -/
theorem density_centered_purity {m n : ℕ} (hm : 0<m) (hn : 0<n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hρ : APPT.Quantum.IsDensity A) :
    APPT.Quantum.purity (A-maximallyMixed m n)=APPT.Quantum.purity A-1/((m:ℝ)*n) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let c : ℝ := 1/((m:ℝ)*n)
  have he : (A-c • 1)*(A-c • 1)=A*A-(2*c) • A+(c^2) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  change ((A-c • 1)*(A-c • 1)).trace.re=(A*A).trace.re-c
  rw [he]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hρ.2,
    Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.one_re, Complex.natCast_re,
    smul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  dsimp [c]
  field_simp
  <;> ring

/-- The maximally mixed state is the unique purity minimum among all density matrices. -/
theorem density_minimum_purity {m n : ℕ} (hm : 0<m) (hn : 0<n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hρ : APPT.Quantum.IsDensity A) :
    1/((m:ℝ)*n)≤APPT.Quantum.purity A ∧
    (APPT.Quantum.purity A=1/((m:ℝ)*n) ↔ A=maximallyMixed m n) := by
  have hH := hρ.1.isHermitian.sub (maximallyMixed_density hm hn).1.isHermitian
  have hnon := hermitian_purity_nonneg hH
  have he := density_centered_purity hm hn hρ
  refine ⟨by linarith,?_⟩
  rw [← sub_eq_zero, ← he, hermitian_purity_zero_iff hH, sub_eq_zero]

/-- The attainable purity values form the entire closed interval between their actual extrema. -/
theorem apptPurityValues_eq_Icc {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    apptPurityValues m n=Set.Icc (1/((m:ℝ)*n)) (apptPuritySup m n) := by
  have hmP : 0<m := by omega
  have hnP : 0<n := by omega
  obtain ⟨A,hA,hP,hopt⟩ := exists_appt_purity_eq_sup hm hmn
  ext x
  constructor
  · rintro ⟨B,hB,hQ,rfl⟩
    exact ⟨(density_minimum_purity hmP hnP hB).1,
      le_csSup (appt_purity_values_nonempty_bounded hm hmn).2 ⟨B,hB,hQ,rfl⟩⟩
  · intro hx
    let f : ℝ → ℝ := fun t => APPT.Quantum.purity (stateMix t (maximallyMixed m n) A)
    have hf : Continuous f := by
      apply continuous_quantum_purity.comp
      unfold stateMix
      fun_prop
    have h0 : f 0=1/((m:ℝ)*n) := by simpa [f,stateMix] using maximallyMixed_purity hmP hnP
    have h1 : f 1=apptPuritySup m n := by simpa [f,stateMix] using hopt
    have hx' : x ∈ Set.Icc (f 0) (f 1) := by rwa [h0,h1]
    obtain ⟨t,ht,hval⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hf.continuousOn hx'
    refine ⟨stateMix t (maximallyMixed m n) A,
      stateMix_density ht.1 ht.2 (maximallyMixed_density hmP hnP) hA,
      stateMix_appt ht.1 ht.2 (maximallyMixed_appt m n) hP,?_⟩
    exact hval.symm

end APPTReview
