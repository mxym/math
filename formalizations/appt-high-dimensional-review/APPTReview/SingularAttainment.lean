import APPTReview.SingularClassification

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def uniformHole {m n : ℕ} (e : Fin m × Fin n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1/((m:ℝ)*n-1)) • (1-setProjection {e})

theorem singletonProjection_density {m n : ℕ} (e : Fin m × Fin n) :
    APPT.Quantum.IsDensity (setProjection {e}) := by
  exact ⟨hermitian_idempotent_posSemidef _ (setProjection_hermitian _) (setProjection_sq _),
    by simp [setProjection_trace]⟩

theorem uniformHole_isDensity {m n : ℕ} (hD : 1<m*n) (e : Fin m × Fin n) :
    APPT.Quantum.IsDensity (uniformHole e) := by
  have hDR : (1:ℝ)<(m:ℝ)*n := by exact_mod_cast hD
  have hc : (m:ℝ)*n-1≠0 := by linarith
  constructor
  · exact (hermitian_idempotent_complement_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)).smul
      (by positivity : (0:ℝ)≤1/((m:ℝ)*n-1))
  · have ht : (1-setProjection {e} : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).trace=
        (((m:ℝ)*(n:ℝ)-1:ℝ):ℂ) := by
      simp [Matrix.trace_sub, Matrix.trace_one, setProjection_trace]
    simp only [uniformHole, Matrix.trace_smul, ht, Complex.real_smul]
    rw [← Complex.ofReal_mul]
    simp [hc]

theorem uniformHole_absolutelyPPT {m n : ℕ} (hD : 1<m*n) (e : Fin m × Fin n) :
    APPT.Quantum.AbsolutelyPPT (uniformHole e) := by
  have hDR : (1:ℝ)<(m:ℝ)*n := by exact_mod_cast hD
  exact APPT.Quantum.absolutelyPPT_smul
    (density_complement_absolutelyPPT (singletonProjection_density e)) (by positivity)

theorem uniformHole_singular {m n : ℕ} (e : Fin m × Fin n) : (uniformHole e).det=0 := by
  have he : uniformHole e=Matrix.diagonal
      (fun i : Fin m × Fin n => if i=e then (0:ℂ) else ((1/((m:ℝ)*n-1):ℝ):ℂ)) := by
    ext i j
    by_cases hij : i=j <;> by_cases hie : i=e <;>
      simp_all [uniformHole, setProjection, Matrix.diagonal_apply, Matrix.one_apply, Complex.real_smul]
  rw [he, Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp)

/-- Actual trace-one singular APPT attainment in every nontrivial rectangular system. -/
theorem exists_singular_appt_density {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧ A.det=0 ∧
      APPT.Quantum.purity A=1/((m:ℝ)*n-1) := by
  let e : Fin m × Fin n := (⟨0,by omega⟩,⟨0,by omega⟩)
  have hD : 1<m*n := by nlinarith
  have hd := uniformHole_isDensity hD e
  have ha := uniformHole_absolutelyPPT hD e
  have hz := uniformHole_singular e
  exact ⟨uniformHole e,hd,ha,hz,singular_appt_purity hm hmn hd ha hz⟩

/-- The purity ball is not a necessary APPT condition for nonsingular states. -/
theorem purity_ball_not_necessary :
    ∃ A : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A=11/50 ∧ 1/5<APPT.Quantum.purity A := by
  obtain ⟨A,hA,hP,he⟩ := exists_projectionPlateau (by norm_num : 2≤2)
    (by norm_num : 0<3) 2 (by norm_num : 2≤2*3)
  norm_num [plateauDenominator] at he
  exact ⟨A,hA,hP,he,by rw [he]; norm_num⟩

end APPTReview
