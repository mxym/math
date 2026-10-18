import EffectiveEncoding.AngleEvaluation
import CircuitRecursion.QuaternionOracles

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

noncomputable def hadRepresentative : SU2 :=
  quaternionSU2 (-Complex.I*(invSqrtTwo:ℂ)) (-Complex.I*(invSqrtTwo:ℂ)) (by
    simpa [Complex.normSq_apply,Complex.mul_re,Complex.mul_im] using invSqrtTwo_square)

noncomputable def yRepresentative : SU2 :=
  quaternionSU2 ((1+Complex.I)/2) ((1+Complex.I)/2) (by norm_num [Complex.normSq_apply])

noncomputable def phaseRepresentative (θ : ℝ) : SU2 :=
  quaternionSU2 (complexPhase θ) 0 (by simp [complexPhase_normSq])

theorem star_complexPhase (θ : ℝ) : star (complexPhase θ)=complexPhase (-θ) := by
  apply Complex.ext <;> simp [complexPhase_trig]

theorem phaseRepresentative_bool (θ : ℝ) :
    (su2ToBool (phaseRepresentative θ) : Matrix Bool Bool ℂ)=
      Matrix.diagonal (fun b => complexPhase (if b then -θ else θ)) := by
  ext b c
  cases b <;> cases c <;>
    simp [phaseRepresentative,su2ToBool,su2AsUnitary,reindexUnitary,
      Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,quaternionSU2,quaternionMatrix,
      finTwoEquiv,Matrix.diagonal_apply,star_complexPhase]

theorem su2ToBool_star (U : SU2) : su2ToBool (star U)=star (su2ToBool U) := by
  apply Subtype.ext
  ext b c
  rfl

/-- Explicit representatives for the exact finite one-qubit syntax.
No determinant-root selection is used. -/
noncomputable def SingleCode.representative : SingleCode → SU2
  | .hadamard => hadRepresentative
  | .yBasis => yRepresentative
  | .phase a b => phaseRepresentative ((a.value-b.value)/2)
  | .inverse u => star u.representative

noncomputable def SingleCode.globalPhase : SingleCode → ℂ
  | .hadamard => Complex.I
  | .yBasis => (invSqrtTwo:ℂ)-(invSqrtTwo:ℂ)*Complex.I
  | .phase a b => complexPhase ((a.value+b.value)/2)
  | .inverse u => star u.globalPhase

theorem SingleCode.globalPhase_norm (u : SingleCode) : Complex.normSq u.globalPhase=1 := by
  induction u with
  | hadamard => simp [SingleCode.globalPhase]
  | yBasis =>
    simpa [SingleCode.globalPhase,Complex.normSq_apply,pow_two] using invSqrtTwo_square
  | phase a b => exact complexPhase_normSq _
  | inverse u ih => simpa [SingleCode.globalPhase] using ih

/-- This phase and this SU2 matrix belong to each particular descriptor,
rather than to an arbitrary existence certificate for an unknown U2 gate. -/
theorem SingleCode.representative_spec (u : SingleCode) :
    (u.value : Matrix Bool Bool ℂ)=u.globalPhase •
      (su2ToBool u.representative : Matrix Bool Bool ℂ) := by
  induction u with
  | hadamard =>
    ext b c
    cases b <;> cases c <;>
      simp [SingleCode.value,SingleCode.globalPhase,SingleCode.representative,
        hadRepresentative,su2ToBool,su2AsUnitary,reindexUnitary,
        Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,quaternionSU2,quaternionMatrix,
        finTwoEquiv,hadamard_entry,Matrix.smul_apply,smul_eq_mul] <;>
        ring_nf <;> simp [Complex.I_sq]
  | yBasis =>
    ext b c
    cases b <;> cases c <;>
      simp [SingleCode.value,SingleCode.globalPhase,SingleCode.representative,
        yRepresentative,su2ToBool,su2AsUnitary,reindexUnitary,
        Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,quaternionSU2,quaternionMatrix,
        finTwoEquiv,yBasis_entry,Matrix.smul_apply,smul_eq_mul] <;>
        ring_nf <;> simp [Complex.I_sq] <;> ring
  | phase a b =>
    change (Matrix.diagonal (fun z => complexPhase (if z then b.value else a.value)))=
      complexPhase ((a.value+b.value)/2) •
        (su2ToBool (phaseRepresentative ((a.value-b.value)/2)) : Matrix Bool Bool ℂ)
    rw [phaseRepresentative_bool]
    ext x y
    cases x <;> cases y <;> simp [Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul]
    all_goals rw [← complexPhase_add]
    all_goals congr 1 <;> ring
  | inverse u ih =>
    change (star u.value : Matrix Bool Bool ℂ)=star u.globalPhase •
      (su2ToBool (star u.representative) : Matrix Bool Bool ℂ)
    rw [su2ToBool_star]
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_smul] using
      congrArg Matrix.conjTranspose ih

theorem quaternionCoordinates_star (U : SU2) :
    quaternionCoordinates (star U)=
      ![quaternionCoordinates U 0,-quaternionCoordinates U 1,
        -quaternionCoordinates U 2,-quaternionCoordinates U 3] := by
  funext i
  fin_cases i <;>
    simp [quaternionCoordinates,Matrix.conjTranspose_apply,su2_lower_left]

def invSqrtTwoOracle : RationalOracle := oracleSqrt (oracleConst (1/2))

theorem sqrt_half_eq_invSqrtTwo : Real.sqrt (1/2)=invSqrtTwo := by
  have hn : 0 ≤ invSqrtTwo := by unfold invSqrtTwo;positivity
  have hs : invSqrtTwo^2=(1/2:ℝ) := by nlinarith [invSqrtTwo_square]
  rw [← hs,Real.sqrt_sq hn]

theorem invSqrtTwoOracle_correct : Approximates invSqrtTwoOracle invSqrtTwo := by
  have h := oracleSqrt_correct (oracleConst (1/2)) (1/2)
    (by simpa using oracleConst_correct (1/2)) (by norm_num)
  simpa only [invSqrtTwoOracle,sqrt_half_eq_invSqrtTwo] using h

def phaseCosOracle (a b : AngleCode) : RationalOracle :=
  oracleAdd
    (oracleMul 0 (a.half 1).cosOracle (b.half 1).cosOracle)
    (oracleMul 0 (a.half 1).sinOracle (b.half 1).sinOracle)

def phaseSinOracle (a b : AngleCode) : RationalOracle :=
  oracleAdd
    (oracleMul 0 (a.half 1).sinOracle (b.half 1).cosOracle)
    (oracleNeg (oracleMul 0 (a.half 1).cosOracle (b.half 1).sinOracle))

theorem phaseCosOracle_correct (a b : AngleCode) :
    Approximates (phaseCosOracle a b) (Real.cos ((a.value-b.value)/2)) := by
  rw [sub_div,Real.cos_sub]
  have hca := (a.half 1).cosOracle_correct
  have hcb := (b.half 1).cosOracle_correct
  have hsa := (a.half 1).sinOracle_correct
  have hsb := (b.half 1).sinOracle_correct
  simp only [AngleCode.half_value,pow_one] at hca hcb hsa hsb
  exact oracleAdd_correct _ _ _ _
    (oracleMul_correct 0 _ _ _ _ hca hcb (by simpa using Real.abs_cos_le_one _)
      (by simpa using Real.abs_cos_le_one _))
    (oracleMul_correct 0 _ _ _ _ hsa hsb (by simpa using Real.abs_sin_le_one _)
      (by simpa using Real.abs_sin_le_one _))

theorem phaseSinOracle_correct (a b : AngleCode) :
    Approximates (phaseSinOracle a b) (Real.sin ((a.value-b.value)/2)) := by
  rw [sub_div,Real.sin_sub]
  have hca := (a.half 1).cosOracle_correct
  have hcb := (b.half 1).cosOracle_correct
  have hsa := (a.half 1).sinOracle_correct
  have hsb := (b.half 1).sinOracle_correct
  simp only [AngleCode.half_value,pow_one] at hca hcb hsa hsb
  simpa only [phaseSinOracle,sub_eq_add_neg] using
    oracleAdd_correct _ _ _ _
      (oracleMul_correct 0 _ _ _ _ hsa hcb (by simpa using Real.abs_sin_le_one _)
        (by simpa using Real.abs_cos_le_one _))
      (oracleNeg_correct _ _ (oracleMul_correct 0 _ _ _ _ hca hsb
        (by simpa using Real.abs_cos_le_one _) (by simpa using Real.abs_sin_le_one _)))

def quaternionStarOracle (f : QuaternionOracle) (p : ℕ) : List.Vector ℚ 4 :=
  let a := f p
  List.Vector.ofFn ![a.get 0,-a.get 1,-a.get 2,-a.get 3]

theorem quaternionStarOracle_correct (f : QuaternionOracle) (U : SU2)
    (hf : QApproximates f U) : QApproximates (quaternionStarOracle f) (star U) := by
  intro p i
  rw [quaternionCoordinates_star]
  fin_cases i
  · simpa [quaternionStarOracle] using hf p 0
  · change |((-(f p).get 1:ℚ):ℝ)- -quaternionCoordinates U 1|≤_
    rw [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact hf p 1
  · change |((-(f p).get 2:ℚ):ℝ)- -quaternionCoordinates U 2|≤_
    rw [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact hf p 2
  · change |((-(f p).get 3:ℚ):ℝ)- -quaternionCoordinates U 3|≤_
    rw [Rat.cast_neg,neg_sub_neg,abs_sub_comm]
    exact hf p 3

def coordinatePacket (f : Fin 4 → RationalOracle) : QuaternionOracle :=
  fun p => List.Vector.ofFn (fun i => f i p)

theorem coordinatePacket_correct (f : Fin 4 → RationalOracle) (U : SU2)
    (hf : ∀ i,Approximates (f i) (quaternionCoordinates U i)) :
    QApproximates (coordinatePacket f) U := by
  intro p i
  simpa only [coordinatePacket,List.Vector.get_ofFn] using hf i p

/-- The actual SU2 packet is computed from the descriptor. Its only square
root routine is the previously implemented finite rational Nat.sqrt code. -/
def SingleCode.quaternionOracle : SingleCode → QuaternionOracle
  | .hadamard => coordinatePacket ![oracleConst 0,oracleNeg invSqrtTwoOracle,
      oracleConst 0,oracleNeg invSqrtTwoOracle]
  | .yBasis => coordinatePacket ![oracleConst (1/2),oracleConst (1/2),
      oracleConst (1/2),oracleConst (1/2)]
  | .phase a b => coordinatePacket ![phaseCosOracle a b,phaseSinOracle a b,oracleConst 0,oracleConst 0]
  | .inverse u => quaternionStarOracle u.quaternionOracle

theorem hadRepresentative_coordinates :
    quaternionCoordinates hadRepresentative=![0,-invSqrtTwo,0,-invSqrtTwo] := by
  funext i
  fin_cases i <;> simp [quaternionCoordinates,hadRepresentative,quaternionSU2,
    quaternionMatrix,Complex.mul_re,Complex.mul_im]

theorem phaseRepresentative_coordinates (θ : ℝ) :
    quaternionCoordinates (phaseRepresentative θ)=![Real.cos θ,Real.sin θ,0,0] := by
  funext i
  fin_cases i <;> simp [quaternionCoordinates,phaseRepresentative,quaternionSU2,
    quaternionMatrix,complexPhase_trig,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

theorem SingleCode.quaternionOracle_correct (u : SingleCode) :
    QApproximates u.quaternionOracle u.representative := by
  induction u with
  | hadamard =>
    apply coordinatePacket_correct
    intro i
    rw [SingleCode.representative,hadRepresentative_coordinates]
    fin_cases i
    · simpa using oracleConst_correct 0
    · exact oracleNeg_correct _ _ invSqrtTwoOracle_correct
    · simpa using oracleConst_correct 0
    · exact oracleNeg_correct _ _ invSqrtTwoOracle_correct
  | yBasis =>
    apply coordinatePacket_correct
    intro i
    fin_cases i <;> simpa [SingleCode.representative,yRepresentative,quaternionSU2,
      quaternionMatrix,quaternionCoordinates] using oracleConst_correct (1/2)
  | phase a b =>
    apply coordinatePacket_correct
    intro i
    rw [SingleCode.representative,phaseRepresentative_coordinates]
    fin_cases i
    · exact phaseCosOracle_correct a b
    · exact phaseSinOracle_correct a b
    · simpa using oracleConst_correct 0
    · simpa using oracleConst_correct 0
  | inverse u ih => exact quaternionStarOracle_correct _ _ ih

end EffectiveEncoding
