import APPTReview.EffectiveJoint
import APPTReview.EffectiveLowerScalar
import APPTReview.Counterexample1038

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def effectiveStateBase {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  effectiveSpike h (setProjection s) (Pi.single e (1:ℂ))

noncomputable def effectiveState {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1/effectiveTrace ((m:ℝ)*n) m h s.card) • effectiveStateBase h s e

theorem effectiveStateBase_eq {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    effectiveStateBase h s e=(effectiveBackground m h) • (1 : Matrix _ _ ℂ)+
      (2*h) • setProjection s+(2*(m:ℝ)*h) • setProjection {e} := by
  simp only [effectiveStateBase,effectiveSpike,Fintype.card_fin,pure_single_eq_setProjection]

theorem effectiveStateBase_trace {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    (effectiveStateBase h s e).trace=(effectiveTrace ((m:ℝ)*n) m h s.card:ℂ) := by
  rw [effectiveStateBase_eq]
  simp [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,setProjection_trace,
    Complex.real_smul,effectiveTrace]
  <;> push_cast <;> ring

theorem effectiveState_density {m n : ℕ} (hm : 2≤m) (hn : 0<n) (h : ℝ) (hh : 0≤h)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    APPT.Quantum.IsDensity (effectiveState h s e) := by
  have hmP : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hnP : (0:ℝ)<n := by exact_mod_cast hn
  have hZ := effectiveTrace_pos ((m:ℝ)*n) m h s.card (mul_pos hmP hnP) hmP hh (Nat.cast_nonneg _)
  have hbg : 0≤effectiveBackground m h := by unfold effectiveBackground; positivity
  constructor
  · have hP := hermitian_idempotent_posSemidef (setProjection s) (setProjection_hermitian _) (setProjection_sq _)
    have hR := hermitian_idempotent_posSemidef (setProjection ({e}:Finset (Fin m × Fin n))) (setProjection_hermitian _) (setProjection_sq _)
    unfold effectiveState
    rw [effectiveStateBase_eq]
    exact (((Matrix.PosSemidef.one.smul hbg).add (hP.smul (by positivity))).add
      (hR.smul (by positivity))).smul (by positivity)
  · simp only [effectiveState,Matrix.trace_smul,effectiveStateBase_trace,Complex.real_smul]
    rw [← Complex.ofReal_mul]
    simp [ne_of_gt hZ]

theorem effectiveState_appt {m n : ℕ} (hm : 2≤m) (hn : 0<n) (h : ℝ) (hh : 0≤h)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) :
    APPT.Quantum.AbsolutelyPPT (effectiveState h s e) := by
  have hmP : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hnP : (0:ℝ)<n := by exact_mod_cast hn
  have hZ := effectiveTrace_pos ((m:ℝ)*n) m h s.card (mul_pos hmP hnP) hmP hh (Nat.cast_nonneg _)
  apply APPT.Quantum.absolutelyPPT_smul
  · apply effectiveSpike_absolutelyPPT h hh
    · exact hermitian_idempotent_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · exact hermitian_idempotent_complement_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · simp [dotProduct,Pi.single_apply]
  · positivity

theorem effectiveStateBase_square {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) (he : e∈s) :
    effectiveStateBase h s e*effectiveStateBase h s e=
      (effectiveBackground m h)^2 • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
      (4*h*(effectiveBackground m h+h)) • setProjection s+
      (4*(m:ℝ)*h*(effectiveBackground m h+((m:ℝ)+2)*h)) • setProjection {e} := by
  have hPR := setProjection_mul_subset s {e} (Finset.singleton_subset_iff.mpr he)
  have hRP : setProjection ({e}:Finset (Fin m × Fin n))*setProjection s=setProjection {e} := by
    have ht := congrArg Matrix.conjTranspose hPR
    simpa only [Matrix.conjTranspose_mul,(setProjection_hermitian _).eq] using ht
  rw [effectiveStateBase_eq]
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,setProjection_sq,hPR,hRP]
  module

theorem effectiveState_purity {m n : ℕ} (h : ℝ)
    (s : Finset (Fin m × Fin n)) (e : Fin m × Fin n) (he : e∈s) :
    APPT.Quantum.purity (effectiveState h s e)=effectivePurity ((m:ℝ)*n) m h s.card := by
  unfold APPT.Quantum.purity effectiveState
  rw [Matrix.smul_mul,Matrix.mul_smul,effectiveStateBase_square h s e he]
  simp only [Matrix.trace_smul,Matrix.trace_add,Matrix.trace_one,setProjection_trace,
    Finset.card_singleton,Complex.smul_re,Complex.add_re,Complex.natCast_re,
    Fintype.card_prod,Fintype.card_fin,smul_eq_mul,Nat.cast_mul,Complex.mul_re,Complex.natCast_im,mul_zero,sub_zero]
  unfold effectivePurity
  ring

/-- Actual rational-coefficient half-rank states realize the scalar lower bound. -/
theorem exists_effective_lower {m n h : ℕ} (hm : 2≤m) (hmn : m≤n) (hh : 1≤h)
    (hsize : 2*h^2+4*h≤m) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      ((h:ℝ)/(h+2))^2*(4+(n:ℝ)/m) ≤
        ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  let k := (m*n+1)/2
  have hD : 4≤m*n := by nlinarith
  have hk : 1≤k ∧ k≤m*n := by dsimp [k]; omega
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq
    (show k≤(Finset.univ : Finset (Fin m × Fin n)).card by simpa using hk.2)
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<s.card by omega)
  refine ⟨effectiveState (h:ℝ) s e,effectiveState_density hm (by omega) _ (Nat.cast_nonneg _) _ _,
    effectiveState_appt hm (by omega) _ (Nat.cast_nonneg _) _ _,?_⟩
  rw [effectiveState_purity _ _ _ he,hcard]
  have hkN : m*n≤2*k ∧ 2*k≤m*n+1 := by dsimp [k]; omega
  have hbound := effectivePurity_lower ((m:ℝ)*n) m h k (by exact_mod_cast hm)
    (by have ht := Nat.mul_le_mul_left m hmn; exact_mod_cast (show m^2≤m*n by nlinarith))
    (by exact_mod_cast hh) (by exact_mod_cast hkN.1) (by exact_mod_cast hkN.2)
    (by exact_mod_cast hsize)
  have hmP : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have heq : ((m:ℝ)*n)/(m:ℝ)^2=(n:ℝ)/m := by field_simp
  rw [heq] at hbound
  exact hbound

end APPTReview
