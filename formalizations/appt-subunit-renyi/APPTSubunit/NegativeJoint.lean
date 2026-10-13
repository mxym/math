import APPTSubunit.NegativeJointScalar
import APPTReview.JointSufficiency

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTSubunit
open APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

noncomputable def negativeSpike (h : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (v : a × b → ℂ) : Matrix (a × b) (a × b) ℂ :=
  negativeBackground (Fintype.card a) h • 1+(2*h) • P-
    negativeSpikeSize (Fintype.card a) h • Matrix.vecMulVec v (star v)

theorem pure_negative_witness (h : ℝ) (hh : 0≤h)
    (hd : 0≤negativeSpikeSize (Fintype.card a) h)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (x : a × b → ℂ) :
    ∃ N : ℝ, 0≤N ∧
      -N≤(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re ∧
      (((negativeBackground (Fintype.card a) h*(star x ⬝ᵥ x).re-2*h*N) •
        (1 : Matrix (a × b) (a × b) ℂ))-
        negativeSpikeSize (Fintype.card a) h •
        APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).PosSemidef := by
  obtain ⟨s,L,hs,hss,hL,hW⟩ := exists_pure_signed_model x
  refine ⟨schmidtMass s,schmidtMass_nonneg s hs,?_,?_⟩
  · rw [hW]
    exact trace_contraction_diagonal_lower P L (schmidtSigned s) (schmidtNegative s)
      hP hI hL (schmidtNegative_nonneg s hs) (schmidtSigned_add_negative_nonneg s hs)
  · rw [hW,← hss,sub_eq_add_neg,← neg_smul]
    exact diagonal_floor_lift L (schmidtSigned s) _ _
      (negative_joint_background s h hh) hL
      (fun p => by simpa only [neg_mul,sub_eq_add_neg] using negative_joint_signed s h hh hd hs p)

theorem negativeSpike_hermitian (h : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (hP : P.IsHermitian) (v : a × b → ℂ) : (negativeSpike h P v).IsHermitian := by
  exact ((Matrix.isHermitian_one.smul (show IsSelfAdjoint (negativeBackground (Fintype.card a) h) by rfl)).add
    (hP.smul (show IsSelfAdjoint (2*h) by rfl))).sub
    ((Matrix.posSemidef_vecMulVec_self_star v).isHermitian.smul
      (show IsSelfAdjoint (negativeSpikeSize (Fintype.card a) h) by rfl))

theorem negativeSpike_quadratic (h : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (v x : a × b → ℂ) :
    (star x ⬝ᵥ (APPT.Quantum.partialTranspose (negativeSpike h P v)*ᵥx)).re =
    negativeBackground (Fintype.card a) h*(star x ⬝ᵥ x).re+
      2*h*(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re-
      negativeSpikeSize (Fintype.card a) h*(star v ⬝ᵥ
        (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv)).re := by
  rw [← trace_mul_pure,← trace_partialTranspose_pairing]
  have htrace : (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=star x ⬝ᵥ x := by
    rw [APPT.Quantum.partialTranspose_trace]
    change (∑ i,x i*star (x i))=∑ i,star (x i)*x i
    simp only [mul_comm]
  have hpure : (Matrix.vecMulVec v (star v)*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=
      star v ⬝ᵥ (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv) := by
    rw [Matrix.trace_mul_comm,trace_mul_pure]
  simp only [negativeSpike,Matrix.add_mul,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,
    Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,htrace,hpure,
    Complex.add_re,Complex.sub_re,Complex.smul_re,smul_eq_mul]

theorem negativeSpike_partialTranspose_posSemidef (h : ℝ) (hh : 0≤h)
    (hd : 0≤negativeSpikeSize (Fintype.card a) h)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) :
    (APPT.Quantum.partialTranspose (negativeSpike h P v)).PosSemidef := by
  have hH := APPT.Quantum.partialTranspose_isHermitian (negativeSpike_hermitian h P hP.isHermitian v)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  obtain ⟨N,hN,htrace,hfloor⟩ := pure_negative_witness h hh hd P hP hI x
  have hq := (RCLike.nonneg_iff.mp (hfloor.dotProduct_mulVec_nonneg v)).1
  change 0≤(star v ⬝ᵥ (_ *ᵥv)).re at hq
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
    dotProduct_smul,Complex.sub_re,Complex.smul_re,smul_eq_mul,hv,Complex.one_re,mul_one] at hq
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0≤(star x ⬝ᵥ (APPT.Quantum.partialTranspose (negativeSpike h P v)*ᵥx)).re
    rw [negativeSpike_quadratic]
    have he := mul_nonneg (show 0≤2*h by positivity)
      (show 0≤N+(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re by linarith)
    linarith
  · change (star x ⬝ᵥ (APPT.Quantum.partialTranspose (negativeSpike h P v)*ᵥx)).im=0
    have him := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith

/-- True all-unitary PPT sufficiency for a contraction plus a downward pure spike.
There is no supplied Schmidt decomposition or asymptotic positivity assumption. -/
theorem negativeSpike_absolutelyPPT (h : ℝ) (hh : 0≤h)
    (hd : 0≤negativeSpikeSize (Fintype.card a) h)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) : APPT.Quantum.AbsolutelyPPT (negativeSpike h P v) := by
  intro U
  let Q := (U:Matrix (a × b) (a × b) ℂ)*P*(U:Matrix (a × b) (a × b) ℂ)ᴴ
  have hQ : Q.PosSemidef := hP.mul_mul_conjTranspose_same _
  have hQI : (1-Q).PosSemidef := by
    have hh := hI.mul_mul_conjTranspose_same (U:Matrix (a × b) (a × b) ℂ)
    simpa [Q,Matrix.mul_sub,Matrix.sub_mul,← Matrix.star_eq_conjTranspose,Unitary.coe_mul_star_self] using hh
  have hn := (unitary_normSq_general U v).trans hv
  have hp := negativeSpike_partialTranspose_posSemidef h hh hd Q hQ hQI _ hn
  have hu : (U:Matrix (a × b) (a × b) ℂ)*(U:Matrix (a × b) (a × b) ℂ)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  simpa only [negativeSpike,Q,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,hu,pure_conjugate_general] using hp

end APPTSubunit
