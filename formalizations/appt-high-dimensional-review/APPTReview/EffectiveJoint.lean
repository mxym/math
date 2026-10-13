import APPTReview.EffectiveJointScalar
import APPTReview.JointSufficiency

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

noncomputable def effectiveSpike (t : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (v : a × b → ℂ) : Matrix (a × b) (a × b) ℂ :=
  (effectiveBackground (Fintype.card a) t) • 1+(2*t) • P+
    (2*(Fintype.card a:ℝ)*t) • Matrix.vecMulVec v (star v)

theorem pure_effective_witness (t : ℝ) (ht : 0≤t)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (x : a × b → ℂ) :
    ∃ N : ℝ, 0≤N ∧
      -N≤(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re ∧
      (((effectiveBackground (Fintype.card a) t*(star x ⬝ᵥ x).re-2*t*N) •
        (1 : Matrix (a × b) (a × b) ℂ))+
        (2*(Fintype.card a:ℝ)*t) • APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).PosSemidef := by
  obtain ⟨s,L,hs,hss,hL,hW⟩ := exists_pure_signed_model x
  refine ⟨schmidtMass s,schmidtMass_nonneg s hs,?_,?_⟩
  · rw [hW]
    exact trace_contraction_diagonal_lower P L (schmidtSigned s) (schmidtNegative s)
      hP hI hL (schmidtNegative_nonneg s hs) (schmidtSigned_add_negative_nonneg s hs)
  · rw [hW,← hss]
    exact diagonal_floor_lift L (schmidtSigned s) _ _
      (effective_joint_background s t ht) hL (effective_joint_signed s t ht hs)

theorem effectiveSpike_hermitian (t : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (hP : P.IsHermitian) (v : a × b → ℂ) : (effectiveSpike t P v).IsHermitian := by
  exact ((Matrix.isHermitian_one.smul (show IsSelfAdjoint (effectiveBackground (Fintype.card a) t) by rfl)).add
    (hP.smul (show IsSelfAdjoint (2*t) by rfl))).add
    ((Matrix.posSemidef_vecMulVec_self_star v).isHermitian.smul
      (show IsSelfAdjoint (2*(Fintype.card a:ℝ)*t) by rfl))

theorem effectiveSpike_quadratic (t : ℝ) (P : Matrix (a × b) (a × b) ℂ)
    (v x : a × b → ℂ) :
    (star x ⬝ᵥ (APPT.Quantum.partialTranspose (effectiveSpike t P v)*ᵥx)).re =
    effectiveBackground (Fintype.card a) t*(star x ⬝ᵥ x).re+
      2*t*(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re+
      (2*(Fintype.card a:ℝ)*t)*(star v ⬝ᵥ
        (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv)).re := by
  rw [← trace_mul_pure,← trace_partialTranspose_pairing]
  have htrace : (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=star x ⬝ᵥ x := by
    rw [APPT.Quantum.partialTranspose_trace]
    change (∑ i,x i*star (x i))=∑ i,star (x i)*x i
    simp only [mul_comm]
  have hpure : (Matrix.vecMulVec v (star v)*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=
      star v ⬝ᵥ (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv) := by
    rw [Matrix.trace_mul_comm,trace_mul_pure]
  simp only [effectiveSpike,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_add,
    Matrix.trace_smul,htrace,hpure,Complex.add_re,Complex.smul_re,smul_eq_mul]

theorem effectiveSpike_partialTranspose_posSemidef (t : ℝ) (ht : 0≤t)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) :
    (APPT.Quantum.partialTranspose (effectiveSpike t P v)).PosSemidef := by
  have hH := APPT.Quantum.partialTranspose_isHermitian (effectiveSpike_hermitian t P hP.isHermitian v)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  obtain ⟨N,hN,htrace,hfloor⟩ := pure_effective_witness t ht P hP hI x
  have hq := (RCLike.nonneg_iff.mp (hfloor.dotProduct_mulVec_nonneg v)).1
  change 0≤(star v ⬝ᵥ (_ *ᵥv)).re at hq
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,
    dotProduct_smul,Complex.add_re,Complex.smul_re,smul_eq_mul,hv,Complex.one_re,mul_one] at hq
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0≤(star x ⬝ᵥ (APPT.Quantum.partialTranspose (effectiveSpike t P v)*ᵥx)).re
    rw [effectiveSpike_quadratic]
    have he := mul_nonneg (show 0≤2*t by positivity) (show 0≤N+(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re by linarith)
    linarith
  · change (star x ⬝ᵥ (APPT.Quantum.partialTranspose (effectiveSpike t P v)*ᵥx)).im=0
    have him := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith

/-- A dimension-uniform physical construction; the test-vector and unitary quantifiers are closed. -/
theorem effectiveSpike_absolutelyPPT (t : ℝ) (ht : 0≤t)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) : APPT.Quantum.AbsolutelyPPT (effectiveSpike t P v) := by
  intro U
  let Q := (U:Matrix (a × b) (a × b) ℂ)*P*(U:Matrix (a × b) (a × b) ℂ)ᴴ
  have hQ : Q.PosSemidef := hP.mul_mul_conjTranspose_same _
  have hQI : (1-Q).PosSemidef := by
    have hh := hI.mul_mul_conjTranspose_same (U:Matrix (a × b) (a × b) ℂ)
    simpa [Q,Matrix.mul_sub,Matrix.sub_mul,← Matrix.star_eq_conjTranspose,Unitary.coe_mul_star_self] using hh
  have hn := (unitary_normSq_general U v).trans hv
  have hp := effectiveSpike_partialTranspose_posSemidef t ht Q hQ hQI _ hn
  have hu : (U:Matrix (a × b) (a × b) ℂ)*(U:Matrix (a × b) (a × b) ℂ)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  simpa only [effectiveSpike,Q,Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.mul_one,hu,pure_conjugate_general] using hp

end APPTReview
