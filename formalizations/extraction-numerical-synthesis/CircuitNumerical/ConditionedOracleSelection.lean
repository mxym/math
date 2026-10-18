import CircuitRecursion.PrecomputedNet

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

def quaternionOracleInverse (f : QuaternionOracle) (p : ℕ) : List.Vector ℚ 4 :=
  let a := f p
  List.Vector.ofFn (fun i => if i=0 then a.get i else -a.get i)

theorem quaternionCoordinates_inverse (U : SU2) (i : Fin 4) :
    quaternionCoordinates U⁻¹ i=
      if i=0 then quaternionCoordinates U i else -quaternionCoordinates U i := by
  have h : (U⁻¹).val=U.valᴴ := rfl
  fin_cases i <;> simp [quaternionCoordinates,h,Matrix.conjTranspose_apply,
    su2_lower_left,su2_lower_right]

theorem quaternionOracleInverse_correct (f : QuaternionOracle) (U : SU2)
    (hf : QApproximates f U) : QApproximates (quaternionOracleInverse f) U⁻¹ := by
  intro p i
  simp only [quaternionOracleInverse,List.Vector.get_ofFn,quaternionCoordinates_inverse]
  by_cases hi : i=0
  · simpa only [if_pos hi] using hf p i
  · simpa only [if_neg hi,Rat.cast_neg,neg_sub_neg,abs_sub_comm] using hf p i

def frameOracle (j : Fin 4) : QuaternionOracle := fun _ =>
  List.Vector.ofFn (fun i => if i=j then 1 else 0)

theorem frameOracle_correct (j : Fin 4) : QApproximates (frameOracle j) (conjugacyFrame j) := by
  intro p i
  fin_cases j <;> fin_cases i <;>
    simp [frameOracle,quaternionCoordinates,conjugacyFrame,quaternionSU2,quaternionMatrix] <;> positivity

def chartTargetOracle (f : QuaternionOracle) (j : Fin 4) : QuaternionOracle :=
  quaternionOracleMul (quaternionOracleMul (frameOracle j) f)
    (quaternionOracleInverse (frameOracle j))

theorem chartTargetOracle_correct (f : QuaternionOracle) (V : SU2)
    (hf : QApproximates f V) (j : Fin 4) :
    QApproximates (chartTargetOracle f j) (conjugacyTarget V j) := by
  have h : conjugacyFrame j*V*(conjugacyFrame j)⁻¹=conjugacyTarget V j := Subtype.ext rfl
  rw [← h]
  exact quaternionOracleMul_correct _ _ _ _
    (quaternionOracleMul_correct _ _ _ _ (frameOracle_correct j) hf)
    (quaternionOracleInverse_correct _ _ (frameOracle_correct j))

theorem intertwinerMass_distance (U V : SU2) (j : Fin 4) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary (conjugacyTarget V j)⁻¹)^2=
      intertwinerMass U V j := by
  change ‖U.val-(conjugacyTarget V j).valᴴ‖^2=_
  rw [quaternion_difference,quaternionMatrix_norm_square]
  rfl

def chartMassScore (f g : QuaternionOracle) (p : ℕ) (j : Fin 4) : ℚ :=
  distanceScore f (quaternionOracleInverse (chartTargetOracle g j)) p

theorem chartMassScore_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) (p : ℕ) (j : Fin 4) :
    |(chartMassScore f g p j:ℝ)-intertwinerMass U V j|≤(1/2:ℝ)^p := by
  rw [← intertwinerMass_distance]
  exact distanceScore_correct _ _ _ _ hf
    (quaternionOracleInverse_correct _ _ (chartTargetOracle_correct g V hg j)) p

theorem dyadic_square_precision (t : ℕ) :
    (1/2:ℝ)^(2*t+2)=((1/2:ℝ)^t)^2/4 := by
  rw [pow_add,show 2*t=t*2 by omega,pow_mul]
  norm_num
  ring

def chooseChart (f g : QuaternionOracle) (t : ℕ) : Fin 4 :=
  let scores := List.Vector.ofFn (chartMassScore f g (2*t+2))
  rationalMaxIndex 3 scores.get

theorem chooseChart_denominator (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V)
    (hr : (U.val 0 0).re=(V.val 0 0).re) (t : ℕ)
    (hσd : (1/2:ℝ)^t≤unitaryDistance (su2AsUnitary U) 1)
    (hd : unitaryDistance (su2AsUnitary U) 1≤1) :
    (1/2:ℝ)^(t+1)≤Real.sqrt (intertwinerMass U V (chooseChart f g t)) := by
  let score := chartMassScore f g (2*t+2)
  have hget : (List.Vector.ofFn score).get=score := by funext j; exact List.Vector.get_ofFn score j
  simp only [chooseChart]
  change (1/2:ℝ)^(t+1)≤Real.sqrt (intertwinerMass U V (rationalMaxIndex 3 (List.Vector.ofFn score).get))
  rw [hget]
  have h := conditionedChart_denominator U V hr ((1/2:ℝ)^t) ((1/2:ℝ)^(2*t+2))
    (by positivity) hσd hd (dyadic_square_precision t).le score
    (chartMassScore_correct f g U V hf hg (2*t+2))
  simpa only [pow_succ,div_eq_mul_inv,one_mul] using h

def residualSmall (f : QuaternionOracle) (t : ℕ) : Bool :=
  decide (distanceScore f quaternionOracleOne (2*t+2)≤2*((1/2:ℚ)^t)^2)

/-- Rational thresholding gives overlapping safe branches: a small residual
may be skipped, and a continuing residual has the chart lower bound. -/
theorem residualSmall_correct (f : QuaternionOracle) (U : SU2)
    (hf : QApproximates f U) (t : ℕ) :
    (residualSmall f t=true → unitaryDistance (su2AsUnitary U) 1≤2*(1/2:ℝ)^t) ∧
    (residualSmall f t=false → (1/2:ℝ)^t≤unitaryDistance (su2AsUnitary U) 1) := by
  let q := distanceScore f quaternionOracleOne (2*t+2)
  have he := distanceScore_correct f quaternionOracleOne U 1 hf quaternionOracleOne_correct (2*t+2)
  rw [dyadic_square_precision] at he
  change |(q:ℝ)-unitaryDistance (su2AsUnitary U) 1^2|≤_ at he
  have he' := abs_le.mp he
  have hd0 := unitaryDistance_nonneg (su2AsUnitary U) 1
  have hσ : (0:ℝ)<(1/2:ℝ)^t := by positivity
  constructor
  · intro h
    have hq : q≤2*((1/2:ℚ)^t)^2 := of_decide_eq_true h
    have hq' : (q:ℝ)≤((2*((1/2:ℚ)^t)^2:ℚ):ℝ) := by exact_mod_cast hq
    push_cast at hq'
    nlinarith [he'.1]
  · intro h
    have hq : ¬q≤2*((1/2:ℚ)^t)^2 := of_decide_eq_false h
    have hq' : ((2*((1/2:ℚ)^t)^2:ℚ):ℝ)<(q:ℝ) := by exact_mod_cast (lt_of_not_ge hq)
    push_cast at hq'
    nlinarith [he'.2]

end CircuitRecursion
