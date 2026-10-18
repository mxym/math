import CircuitNumerical.ConditionedOracleSelection

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

noncomputable def balancedS (U : SU2) : ℝ := Real.sqrt (Real.sqrt ((1-(U.val 0 0).re)/2))

noncomputable def balancedC (U : SU2) : ℝ := Real.sqrt (1-balancedS U^2)

theorem balancedParameterFacts (U : SU2) :
    0≤balancedS U ∧ balancedS U≤1 ∧ 0≤balancedC U ∧ balancedC U≤1 ∧
    balancedC U^2+balancedS U^2=1 ∧
    balancedS U^4=(1-(U.val 0 0).re)/2 ∧
    2*balancedS U^2=unitaryDistance (su2AsUnitary U) 1 := by
  have hr := su2_scalarPart_bounds U
  have ht0 := Real.sqrt_nonneg ((1-(U.val 0 0).re)/2)
  have ht2 := Real.sq_sqrt (show 0≤(1-(U.val 0 0).re)/2 by linarith)
  have hs0 : 0≤balancedS U := Real.sqrt_nonneg _
  have hs2 : balancedS U^2=Real.sqrt ((1-(U.val 0 0).re)/2) := Real.sq_sqrt ht0
  have hs4 : balancedS U^4=(1-(U.val 0 0).re)/2 := by nlinarith
  have ht1 : Real.sqrt ((1-(U.val 0 0).re)/2)≤1 := by nlinarith
  have hs1 : balancedS U≤1 := by nlinarith
  have hc0 : 0≤balancedC U := Real.sqrt_nonneg _
  have hc2 : balancedC U^2=1-balancedS U^2 := Real.sq_sqrt (by linarith)
  have hc1 : balancedC U≤1 := by nlinarith [sq_nonneg (balancedS U)]
  have hd := su2_distance_square U
  have hd0 := unitaryDistance_nonneg (su2AsUnitary U) 1
  refine ⟨hs0,hs1,hc0,hc1,by linarith,hs4,?_⟩
  nlinarith

theorem balancedCircle (U : SU2) : balancedC U^2+balancedS U^2=1 :=
  (balancedParameterFacts U).2.2.2.2.1

noncomputable def referenceX (U : SU2) : SU2 := axisX (balancedC U) (balancedS U) (balancedCircle U)
noncomputable def referenceY (U : SU2) : SU2 := axisY (balancedC U) (balancedS U) (balancedCircle U)
noncomputable def balancedReference (U : SU2) : SU2 := su2Commutator (referenceX U) (referenceY U)

theorem balancedReference_scalar (U : SU2) :
    ((balancedReference U).val 0 0).re=(U.val 0 0).re := by
  rw [balancedReference,referenceX,referenceY,axisCommutator_scalar]
  have h := (balancedParameterFacts U).2.2.2.2.2.1
  linarith

theorem referenceX_distance (U : SU2) :
    unitaryDistance (su2AsUnitary (referenceX U)) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) := by
  rcases balancedParameterFacts U with ⟨hs0,hs1,hc0,hc1,hcs,hs4,hsd⟩
  have hn := axisX_distance (balancedC U) (balancedS U) (balancedCircle U)
  change unitaryDistance (su2AsUnitary (referenceX U)) 1^2=2-2*balancedC U at hn
  have hd0 := unitaryDistance_nonneg (su2AsUnitary U) 1
  have hn0 := unitaryDistance_nonneg (su2AsUnitary (referenceX U)) 1
  have hroot := Real.sq_sqrt hd0
  have hroot0 := Real.sqrt_nonneg (unitaryDistance (su2AsUnitary U) 1)
  have hcc : balancedC U*balancedC U≤balancedC U := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  nlinarith

theorem referenceY_distance (U : SU2) :
    unitaryDistance (su2AsUnitary (referenceY U)) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) := by
  rcases balancedParameterFacts U with ⟨hs0,hs1,hc0,hc1,hcs,hs4,hsd⟩
  have hn := axisY_distance (balancedC U) (balancedS U) (balancedCircle U)
  change unitaryDistance (su2AsUnitary (referenceY U)) 1^2=2-2*balancedC U at hn
  have hd0 := unitaryDistance_nonneg (su2AsUnitary U) 1
  have hn0 := unitaryDistance_nonneg (su2AsUnitary (referenceY U)) 1
  have hroot := Real.sq_sqrt hd0
  have hroot0 := Real.sqrt_nonneg (unitaryDistance (su2AsUnitary U) 1)
  have hcc : balancedC U*balancedC U≤balancedC U := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  nlinarith

def coordinateOracle (f : QuaternionOracle) (i : Fin 4) : RationalOracle := fun p => (f p).get i

theorem coordinateOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) (i : Fin 4) :
    Approximates (coordinateOracle f i) (quaternionCoordinates U i) := fun p => hf p i

def balancedSOracle (f : QuaternionOracle) : RationalOracle :=
  oracleSqrt (oracleSqrt (oracleMeanMinus (coordinateOracle f 0)))

def balancedCOracle (f : QuaternionOracle) : RationalOracle :=
  oracleSqrt (oracleAdd (oracleConst 1)
    (oracleNeg (oracleMul 0 (balancedSOracle f) (balancedSOracle f))))

theorem balancedSOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) :
    Approximates (balancedSOracle f) (balancedS U) := by
  have hr : Approximates (coordinateOracle f 0) (U.val 0 0).re := coordinateOracle_correct f U hf 0
  have hm := oracleMeanMinus_correct _ _ hr
  have hs := oracleSqrt_correct _ _ hm (by linarith [(su2_scalarPart_bounds U).2])
  exact oracleSqrt_correct _ _ hs (Real.sqrt_nonneg _)

theorem balancedCOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) :
    Approximates (balancedCOracle f) (balancedC U) := by
  rcases balancedParameterFacts U with ⟨hs0,hs1,hc0,hc1,hcs,hs4,hsd⟩
  have hs := balancedSOracle_correct f U hf
  have hb : |balancedS U|≤(2:ℝ)^0 := by simpa only [abs_of_nonneg hs0,pow_zero] using hs1
  have hmul := oracleMul_correct 0 _ _ _ _ hs hs hb hb
  have hneg := oracleNeg_correct _ _ hmul
  have hadd := oracleAdd_correct _ _ _ _ (oracleConst_correct 1) hneg
  simp only [Rat.cast_one] at hadd
  have he := oracleSqrt_correct _ _ hadd (by nlinarith)
  simpa only [balancedCOracle,balancedC,sub_eq_add_neg,pow_two,Rat.cast_one] using he

def referenceXOracle (f : QuaternionOracle) (p : ℕ) : List.Vector ℚ 4 :=
  let c := balancedCOracle f p
  let s := balancedSOracle f p
  List.Vector.ofFn ![c,0,0,s]

def referenceYOracle (f : QuaternionOracle) (p : ℕ) : List.Vector ℚ 4 :=
  let c := balancedCOracle f p
  let s := balancedSOracle f p
  List.Vector.ofFn ![c,0,s,0]

theorem referenceXOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) :
    QApproximates (referenceXOracle f) (referenceX U) := by
  intro p i
  have hc := balancedCOracle_correct f U hf p
  have hs := balancedSOracle_correct f U hf p
  fin_cases i <;> simp [referenceXOracle,referenceX,axisX,quaternionSU2,quaternionMatrix,
    quaternionCoordinates] <;> first
    | simpa only [one_div,inv_pow] using hc
    | simpa only [one_div,inv_pow] using hs

theorem referenceYOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) :
    QApproximates (referenceYOracle f) (referenceY U) := by
  intro p i
  have hc := balancedCOracle_correct f U hf p
  have hs := balancedSOracle_correct f U hf p
  fin_cases i <;> simp [referenceYOracle,referenceY,axisY,quaternionSU2,quaternionMatrix,
    quaternionCoordinates] <;> first
    | simpa only [one_div,inv_pow] using hc
    | simpa only [one_div,inv_pow] using hs

def balancedReferenceOracle (f : QuaternionOracle) : QuaternionOracle :=
  quaternionOracleMul
    (quaternionOracleMul (quaternionOracleMul (referenceXOracle f) (referenceYOracle f))
      (quaternionOracleInverse (referenceXOracle f)))
    (quaternionOracleInverse (referenceYOracle f))

theorem balancedReferenceOracle_correct (f : QuaternionOracle) (U : SU2) (hf : QApproximates f U) :
    QApproximates (balancedReferenceOracle f) (balancedReference U) := by
  have hX := referenceXOracle_correct f U hf
  have hY := referenceYOracle_correct f U hf
  exact quaternionOracleMul_correct _ _ _ _
    (quaternionOracleMul_correct _ _ _ _ (quaternionOracleMul_correct _ _ _ _ hX hY)
      (quaternionOracleInverse_correct _ _ hX))
    (quaternionOracleInverse_correct _ _ hY)

end CircuitRecursion
