import APPTReview.PositiveMap

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_idempotent_posSemidef (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hsq : P*P=P) : P.PosSemidef := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hsq] at hp

theorem hermitian_idempotent_complement_posSemidef (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hsq : P*P=P) : (1-P).PosSemidef := by
  apply hermitian_idempotent_posSemidef
  · exact Matrix.isHermitian_one.sub hP
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hsq]
    abel

noncomputable def plateauDenominator (m n k : ℕ) : ℝ :=
  (m : ℝ)*n*((m : ℝ)-1)+2*k

noncomputable def projectionPlateau {m n : ℕ} (k : ℕ)
    (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  (1/plateauDenominator m n k) • (((m : ℝ)-1) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+(2 : ℝ) • P)

theorem plateauDenominator_pos {m n : ℕ} (hm : 2 ≤ m) (hn : 0<n) (k : ℕ) :
    0<plateauDenominator m n k := by
  have hmR : (1 : ℝ)<m := by exact_mod_cast (by omega : 1<m)
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  unfold plateauDenominator
  positivity

/-- The physical state formed from any orthogonal projection of trace k. -/
theorem projectionPlateau_isDensity {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    (k : ℕ) (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : P.IsHermitian) (hsq : P*P=P) (htr : P.trace=(k : ℂ)) :
    APPT.Quantum.IsDensity (projectionPlateau k P) := by
  have hZ := plateauDenominator_pos hm hn k
  have hm1 : (1 : ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
  have hc : (0 : ℝ)≤(m : ℝ)-1 := by linarith
  constructor
  · exact ((Matrix.PosSemidef.one.smul hc).add
      ((hermitian_idempotent_posSemidef P hP hsq).smul (by norm_num : (0 : ℝ)≤2))).smul
      (by positivity : (0 : ℝ)≤1/plateauDenominator m n k)
  · have ht : ((((m : ℝ)-1) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
        (2 : ℝ) • P).trace) = (plateauDenominator m n k : ℂ) := by
      simp [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, htr,
        Complex.real_smul, plateauDenominator]
      <;> push_cast <;> ring
    simp only [projectionPlateau, Matrix.trace_smul, ht, Complex.real_smul]
    rw [← Complex.ofReal_mul]
    simp [ne_of_gt hZ]

theorem projectionPlateau_absolutelyPPT {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    (k : ℕ) (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : P.IsHermitian) (hsq : P*P=P) :
    APPT.Quantum.AbsolutelyPPT (projectionPlateau k P) := by
  apply APPT.Quantum.absolutelyPPT_smul
  · simpa using absolutelyPPT_dimension_contraction P
      (hermitian_idempotent_posSemidef P hP hsq)
      (hermitian_idempotent_complement_posSemidef P hP hsq)
  · have hZ := plateauDenominator_pos hm hn k
    positivity

/-- Exact second moment for all projection ranks, with the original quantum purity. -/
theorem projectionPlateau_purity {m n : ℕ} (k : ℕ)
    (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hsq : P*P=P) (htr : P.trace=(k : ℂ)) :
    APPT.Quantum.purity (projectionPlateau k P) =
      ((m : ℝ)*n*((m : ℝ)-1)^2+4*m*k)/(plateauDenominator m n k)^2 := by
  have he : (((m : ℝ)-1) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+(2 : ℝ) • P)*
      (((m : ℝ)-1) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+(2 : ℝ) • P) =
      (((m : ℝ)-1)^2) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+(4*(m : ℝ)) • P := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hsq]
    module
  unfold APPT.Quantum.purity projectionPlateau
  rw [Matrix.smul_mul, Matrix.mul_smul, he]
  simp only [Matrix.trace_smul, Matrix.trace_add, htr, Matrix.trace_one,
    Complex.smul_re, Complex.add_re, Complex.natCast_re,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul, Nat.cast_mul, Complex.mul_re, Complex.natCast_im, mul_zero, sub_zero]
  ring

/-- A genuine coordinate orthogonal projection of any finite chosen rank. -/
def setProjection (s : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if i∈s then 1 else 0)

theorem setProjection_hermitian (s : Finset ι) : (setProjection s).IsHermitian := by
  simp [setProjection, Matrix.IsHermitian, 
    complex_conj_ite, funext_iff]

theorem setProjection_sq (s : Finset ι) : setProjection s * setProjection s = setProjection s := by
  rw [setProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem setProjection_trace (s : Finset ι) : (setProjection s).trace = (s.card : ℂ) := by
  simp [setProjection, Matrix.trace_diagonal]

/-- Physical APPT attainment of the exact two-level purity at every allowed rank. -/
theorem exists_projectionPlateau {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    (k : ℕ) (hk : k≤m*n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A =
        ((m : ℝ)*n*((m : ℝ)-1)^2+4*m*k)/(plateauDenominator m n k)^2 := by
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset (Fin m × Fin n)).card by simpa using hk)
  let P := setProjection s
  have hP : P.IsHermitian := setProjection_hermitian s
  have hsq : P*P=P := setProjection_sq s
  have htr : P.trace = (k : ℂ) := by simp [P, setProjection_trace, hcard]
  exact ⟨projectionPlateau k P, projectionPlateau_isDensity hm hn k P hP hsq htr,
    projectionPlateau_absolutelyPPT hm hn k P hP hsq, projectionPlateau_purity k P hsq htr⟩

/-- The broad-plateau candidate in the research formula is physically attained
in every rectangular dimension; no optimality of that candidate is asserted. -/
theorem exists_broad_plateau {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    let k := ((m-1)*n+1)/2
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A =
        ((m : ℝ)*n*((m : ℝ)-1)^2+4*m*k)/(plateauDenominator m n k)^2 := by
  dsimp only
  apply exists_projectionPlateau hm (by omega)
  have hsub : m-1+1=m := by omega
  have ht : (m-1)*n+1 ≤ m*n := by nlinarith
  exact (Nat.div_le_self _ _).trans ht

end APPTReview
