import APPTReview.SchmidtJointWitness

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

/-- The original projection-plus-spike matrix, before trace normalization. -/
noncomputable def jointSpike (P : Matrix (a × b) (a × b) ℂ) (v : a × b → ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  (2*(Fintype.card a:ℝ)-5) • 1+(2:ℝ) • P+
    (4*((Fintype.card a:ℝ)-4)) • Matrix.vecMulVec v (star v)

theorem jointSpike_hermitian (P : Matrix (a × b) (a × b) ℂ)
    (hP : P.IsHermitian) (v : a × b → ℂ) : (jointSpike P v).IsHermitian := by
  exact ((Matrix.isHermitian_one.smul (show IsSelfAdjoint (2*(Fintype.card a:ℝ)-5) by rfl)).add
    (hP.smul (show IsSelfAdjoint (2:ℝ) by rfl))).add
    ((Matrix.posSemidef_vecMulVec_self_star v).isHermitian.smul (show IsSelfAdjoint (4*((Fintype.card a:ℝ)-4)) by rfl))

/-- Exact trace-duality identity for the actual physical quadratic form. -/
theorem jointSpike_quadratic (P : Matrix (a × b) (a × b) ℂ) (v x : a × b → ℂ) :
    (star x ⬝ᵥ (APPT.Quantum.partialTranspose (jointSpike P v)*ᵥx)).re =
    (2*(Fintype.card a:ℝ)-5)*(star x ⬝ᵥ x).re+
      2*(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re+
      (4*((Fintype.card a:ℝ)-4))*(star v ⬝ᵥ
        (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv)).re := by
  rw [← trace_mul_pure,← trace_partialTranspose_pairing]
  have htrace : (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=star x ⬝ᵥ x := by
    rw [APPT.Quantum.partialTranspose_trace]
    change (∑ i,x i*star (x i))=∑ i,star (x i)*x i
    simp only [mul_comm]
  have hpure : (Matrix.vecMulVec v (star v)*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=
      star v ⬝ᵥ (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv) := by
    rw [Matrix.trace_mul_comm,trace_mul_pure]
  simp only [jointSpike,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_add,
    Matrix.trace_smul,htrace,hpure,Complex.add_re,Complex.smul_re,smul_eq_mul]

/-- Joint positivity for all complex test vectors, with no supplied Schmidt data. -/
theorem jointSpike_partialTranspose_posSemidef (hc : 4≤Fintype.card a)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) :
    (APPT.Quantum.partialTranspose (jointSpike P v)).PosSemidef := by
  have hH := APPT.Quantum.partialTranspose_isHermitian (jointSpike_hermitian P hP.isHermitian v)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  obtain ⟨N,hN,htrace,hfloor⟩ := pure_joint_witness hc P hP hI x
  have hq := (RCLike.nonneg_iff.mp (hfloor.dotProduct_mulVec_nonneg v)).1
  change 0≤(star v ⬝ᵥ (_ *ᵥv)).re at hq
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,
    dotProduct_smul,Complex.add_re,Complex.smul_re,smul_eq_mul,hv,Complex.one_re,mul_one] at hq
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0≤(star x ⬝ᵥ (APPT.Quantum.partialTranspose (jointSpike P v)*ᵥx)).re
    rw [jointSpike_quadratic]
    linarith
  · change (star x ⬝ᵥ (APPT.Quantum.partialTranspose (jointSpike P v)*ᵥx)).im=0
    have him := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith

/-- Unitary transport of a pure outer product and its exact squared norm. -/
theorem pure_conjugate_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (U:Matrix ι ι ℂ)*Matrix.vecMulVec v (star v)*(U:Matrix ι ι ℂ)ᴴ=
      Matrix.vecMulVec ((U:Matrix ι ι ℂ)*ᵥv) (star ((U:Matrix ι ι ℂ)*ᵥv)) := by
  simp [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_conjTranspose]

theorem unitary_normSq_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    star ((U:Matrix ι ι ℂ)*ᵥv) ⬝ᵥ ((U:Matrix ι ι ℂ)*ᵥv)=star v ⬝ᵥ v := by
  have hu : (U:Matrix ι ι ℂ)ᴴ*(U:Matrix ι ι ℂ)=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,hu,Matrix.vecMul_one]

/-- Dimension-uniform joint sufficiency on the entire global-unitary orbit. -/
theorem jointSpike_absolutelyPPT (hc : 4≤Fintype.card a)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (v : a × b → ℂ) (hv : star v ⬝ᵥ v=1) : APPT.Quantum.AbsolutelyPPT (jointSpike P v) := by
  intro U
  let Q := (U:Matrix (a × b) (a × b) ℂ)*P*(U:Matrix (a × b) (a × b) ℂ)ᴴ
  have hQ : Q.PosSemidef := hP.mul_mul_conjTranspose_same _
  have hQI : (1-Q).PosSemidef := by
    have hh := hI.mul_mul_conjTranspose_same (U:Matrix (a × b) (a × b) ℂ)
    simpa [Q,Matrix.mul_sub,Matrix.sub_mul,← Matrix.star_eq_conjTranspose,Unitary.coe_mul_star_self] using hh
  have hn := (unitary_normSq_general U v).trans hv
  have h := jointSpike_partialTranspose_posSemidef hc Q hQ hQI _ hn
  have hu : (U:Matrix (a × b) (a × b) ℂ)*(U:Matrix (a × b) (a × b) ℂ)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  simpa only [jointSpike,Q,Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.mul_one,hu,pure_conjugate_general] using h

end APPTReview
