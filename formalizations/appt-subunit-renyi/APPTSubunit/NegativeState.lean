import APPTSubunit.NegativeJoint
import APPTReview.Counterexample1038

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTSubunit
open APPTReview

noncomputable def negativeTrace (D m h k : ℝ) : ℝ :=
  (D-1)*negativeBackground m h+h^2+2*h*k

noncomputable def negativePurity (D m h k : ℝ) : ℝ :=
  ((D-1)*(negativeBackground m h)^2+h^4+
    4*h*(negativeBackground m h+h)*k)/(negativeTrace D m h k)^2

noncomputable def negativeStateBase {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  negativeSpike h (setProjection s) (Pi.single e (1:ℂ))

noncomputable def negativeState {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1/negativeTrace ((m:ℝ)*n) m h s.card) • negativeStateBase h s e

theorem negativeStateBase_eq {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    negativeStateBase h s e=negativeBackground m h • (1 : Matrix _ _ ℂ)+
      (2*h) • setProjection s-negativeSpikeSize m h • setProjection {e} := by
  simp only [negativeStateBase,negativeSpike,Fintype.card_fin,pure_single_eq_setProjection]

theorem negativeStateBase_trace {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    (negativeStateBase h s e).trace=(negativeTrace ((m:ℝ)*n) m h s.card:ℂ) := by
  rw [negativeStateBase_eq]
  simp [Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,setProjection_trace,
    Complex.real_smul,negativeTrace,negativeSpikeSize]
  ring

theorem negativeTrace_pos (D m h k : ℝ) (hD : 1≤D) (hm : 0≤m)
    (hh : 0<h) (hk : 0≤k) : 0<negativeTrace D m h k := by
  unfold negativeTrace negativeBackground
  have hx : 0≤(D-1)*((h+1)*m) := by positivity
  have hy : 0≤2*h*k := by positivity
  have hs := sq_pos_of_pos hh
  linarith

theorem negativeSpikeSize_nonneg (m h : ℝ) (hh : 0≤h) (hm : h≤m) :
    0≤negativeSpikeSize m h := by
  unfold negativeSpikeSize negativeBackground
  nlinarith [mul_nonneg (show 0≤h+1 by linarith) (sub_nonneg.mpr hm)]

theorem negativeState_density {m n : ℕ} (hm : 0<m) (hn : 0<n) (h : ℝ) (hh : 0<h)
    (hsize : h≤m) (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    APPT.Quantum.IsDensity (negativeState h s e) := by
  have hD : (1:ℝ)≤(m:ℝ)*n := by exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
  have hZ := negativeTrace_pos ((m:ℝ)*n) m h s.card hD (Nat.cast_nonneg _) hh (Nat.cast_nonneg _)
  have hd := negativeSpikeSize_nonneg (m:ℝ) h hh.le hsize
  have hP := hermitian_idempotent_posSemidef (setProjection s) (setProjection_hermitian _) (setProjection_sq _)
  have hR := hermitian_idempotent_posSemidef (setProjection ({e}:Finset (Fin m × Fin n)))
    (setProjection_hermitian _) (setProjection_sq _)
  have hI := hermitian_idempotent_complement_posSemidef (setProjection ({e}:Finset (Fin m × Fin n)))
    (setProjection_hermitian _) (setProjection_sq _)
  have he : negativeStateBase h s e=h^2 • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
      negativeSpikeSize m h • (1-setProjection {e})+(2*h) • setProjection s := by
    rw [negativeStateBase_eq]
    simp only [smul_sub,negativeSpikeSize]
    module
  constructor
  · unfold negativeState
    rw [he]
    exact (((Matrix.PosSemidef.one.smul (sq_nonneg h)).add (hI.smul hd)).add
      (hP.smul (by positivity))).smul (by positivity)
  · simp only [negativeState,Matrix.trace_smul,negativeStateBase_trace,Complex.real_smul]
    rw [← Complex.ofReal_mul]
    simp [ne_of_gt hZ]

theorem negativeState_appt {m n : ℕ} (hm : 0<m) (hn : 0<n) (h : ℝ) (hh : 0<h)
    (hsize : h≤m) (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    APPT.Quantum.AbsolutelyPPT (negativeState h s e) := by
  have hD : (1:ℝ)≤(m:ℝ)*n := by exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos hm hn))
  have hZ := negativeTrace_pos ((m:ℝ)*n) m h s.card hD (Nat.cast_nonneg _) hh (Nat.cast_nonneg _)
  apply APPT.Quantum.absolutelyPPT_smul
  · apply negativeSpike_absolutelyPPT h hh.le
    · simpa only [Fintype.card_fin] using negativeSpikeSize_nonneg (m:ℝ) h hh.le hsize
    · exact hermitian_idempotent_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · exact hermitian_idempotent_complement_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · simp [dotProduct,Pi.single_apply]
  · positivity

theorem negativeStateBase_square {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) (he : e∉s) :
    negativeStateBase h s e*negativeStateBase h s e=
      (negativeBackground m h)^2 • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
      (4*h*(negativeBackground m h+h)) • setProjection s+
      (h^4-(negativeBackground m h)^2) • setProjection {e} := by
  have hPR : setProjection s*setProjection ({e}:Finset (Fin m × Fin n))=0 := by
    simp only [setProjection,Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hi : i=e <;> by_cases hij : i=j <;> simp_all
  have hRP : setProjection ({e}:Finset (Fin m × Fin n))*setProjection s=0 := by
    have ht := congrArg Matrix.conjTranspose hPR
    simpa only [Matrix.conjTranspose_mul,(setProjection_hermitian _).eq,Matrix.conjTranspose_zero] using ht
  rw [negativeStateBase_eq]
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,setProjection_sq,hPR,hRP,smul_zero,negativeSpikeSize]
  module

theorem negativeState_purity {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) (he : e∉s) :
    APPT.Quantum.purity (negativeState h s e)=negativePurity ((m:ℝ)*n) m h s.card := by
  unfold APPT.Quantum.purity negativeState
  rw [Matrix.smul_mul,Matrix.mul_smul,negativeStateBase_square h s e he]
  simp only [Matrix.trace_smul,Matrix.trace_add,Matrix.trace_one,setProjection_trace,
    Finset.card_singleton,Complex.smul_re,Complex.add_re,Complex.natCast_re,
    Fintype.card_prod,Fintype.card_fin,smul_eq_mul,Nat.cast_mul,Complex.mul_re,Complex.natCast_im,mul_zero,sub_zero]
  unfold negativePurity
  ring

/-- Every admissible finite rank below D admits a true density/APPT witness
with a downward eigenvalue and the exact trace-square objective. -/
theorem exists_negative_rank_state {m n k : ℕ} (hm : 0<m) (hn : 0<n)
    (hk : k<m*n) (h : ℝ) (hh : 0<h) (hsize : h≤m) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A=negativePurity ((m:ℝ)*n) m h k := by
  let e : Fin m × Fin n := (⟨0,hm⟩,⟨0,hn⟩)
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq
    (show k≤((Finset.univ : Finset (Fin m × Fin n)).erase e).card by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ e),Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
      omega)
  have he : e∉s := fun hes => (Finset.mem_erase.mp (hs hes)).1 rfl
  refine ⟨negativeState h s e,negativeState_density hm hn h hh hsize s e,
    negativeState_appt hm hn h hh hsize s e,?_⟩
  rw [negativeState_purity h s e he,hcard]

end APPTSubunit
