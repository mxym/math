import APPTReview.CompactMaximum

open scoped BigOperators ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

noncomputable def stateMix (t : ℝ) (A B : Matrix (a × b) (a × b) ℂ) := (1-t) • A+t • B

theorem stateMix_density {t : ℝ} (ht : 0≤t) (ht1 : t≤1)
    {A B : Matrix (a × b) (a × b) ℂ}
    (hA : APPT.Quantum.IsDensity A) (hB : APPT.Quantum.IsDensity B) :
    APPT.Quantum.IsDensity (stateMix t A B) := by
  refine ⟨(hA.1.smul (sub_nonneg.mpr ht1)).add (hB.1.smul ht),?_⟩
  simp [stateMix, Matrix.trace_add, Matrix.trace_smul, hA.2, hB.2, Complex.real_smul]

theorem stateMix_appt {t : ℝ} (ht : 0≤t) (ht1 : t≤1)
    {A B : Matrix (a × b) (a × b) ℂ}
    (hA : APPT.Quantum.AbsolutelyPPT A) (hB : APPT.Quantum.AbsolutelyPPT B) :
    APPT.Quantum.AbsolutelyPPT (stateMix t A B) := by
  intro U
  have h := ((hA U).smul (sub_nonneg.mpr ht1)).add ((hB U).smul ht)
  simpa [stateMix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] using h

theorem stateMix_purity (t : ℝ) (A B : Matrix (a × b) (a × b) ℂ) :
    APPT.Quantum.purity (stateMix t A B) =
      (1-t)*APPT.Quantum.purity A+t*APPT.Quantum.purity B-
        t*(1-t)*APPT.Quantum.purity (A-B) := by
  have he : stateMix t A B * stateMix t A B =
      (1-t) • (A*A)+t • (B*B)-(t*(1-t)) • ((A-B)*(A-B)) := by
    simp only [stateMix, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
    module
  unfold APPT.Quantum.purity
  rw [he]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul]

theorem hermitian_purity_nonneg {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) : 0≤APPT.Quantum.purity A := by
  rw [purity_eq_entry_norm_sum hA]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- The Hermitian premise is essential: trace-square is not a norm on arbitrary matrices. -/
theorem hermitian_purity_zero_iff {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) : APPT.Quantum.purity A=0 ↔ A=0 := by
  constructor
  · intro hz
    rw [purity_eq_entry_norm_sum hA] at hz
    ext i j
    have hrow : ‖A i j‖^2 ≤ ∑ k, ‖A i k‖^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (‖A i k‖)) (Finset.mem_univ j)
    have hall : (∑ k, ‖A i k‖^2) ≤ ∑ l, ∑ k, ‖A l k‖^2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (‖A l k‖))) (Finset.mem_univ i)
    have hn : ‖A i j‖=0 := by nlinarith [hrow.trans hall, norm_nonneg (A i j)]
    exact norm_eq_zero.mp hn
  · rintro rfl
    simp [APPT.Quantum.purity]

/-- Any nontrivial convex mixture attaining the physical maximum has identical endpoints. -/
theorem appt_maximizing_mixture_rigid {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {A B : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : APPT.Quantum.IsDensity A) (ha : APPT.Quantum.AbsolutelyPPT A)
    (hB : APPT.Quantum.IsDensity B) (hb : APPT.Quantum.AbsolutelyPPT B)
    (hmax : APPT.Quantum.purity (stateMix t A B)=apptPuritySup m n) : A=B := by
  have hbd := (appt_purity_values_nonempty_bounded hm hmn).2
  have hpA : APPT.Quantum.purity A≤apptPuritySup m n := le_csSup hbd ⟨A,hA,ha,rfl⟩
  have hpB : APPT.Quantum.purity B≤apptPuritySup m n := le_csSup hbd ⟨B,hB,hb,rfl⟩
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hpA (by linarith : 0≤1-t))
    (mul_le_mul_of_nonneg_left hpB ht.le)
  have hw : (1-t)*apptPuritySup m n+t*apptPuritySup m n=apptPuritySup m n := by ring
  rw [hw] at hsum
  have hH := hA.1.isHermitian.sub hB.1.isHermitian
  have hn := hermitian_purity_nonneg hH
  have hc : 0<t*(1-t) := mul_pos ht (by linarith)
  rw [stateMix_purity] at hmax
  have hz : APPT.Quantum.purity (A-B)=0 := by nlinarith
  exact sub_eq_zero.mp ((hermitian_purity_zero_iff hH).mp hz)

end APPTReview
