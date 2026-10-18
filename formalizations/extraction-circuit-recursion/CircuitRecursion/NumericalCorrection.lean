import CircuitRecursion.ConditionedFactors

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

/-- One finite numerical SK correction. The target is an entry oracle,
never an exact-real matrix. All branches are finite rational comparisons. -/
def numericalCorrection {m : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (approx : QuaternionOracle → List (Fin m))
    (t : ℕ) (target : QuaternionOracle) : List (Fin m) :=
  let u := approx target
  let residual := quaternionOracleMul target (quaternionOracleInverse (quaternionWordOracle entry u))
  if residualSmall residual t=true then u else
    let a := approx (conditionedFactorXOracle residual t)
    let b := approx (conditionedFactorYOracle residual t)
    u++instructionInverse inverseLabel b++instructionInverse inverseLabel a++b++a

theorem numericalCorrection_length {m : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (approx : QuaternionOracle → List (Fin m))
    (L t : ℕ) (hL : ∀ f,(approx f).length≤L) (target : QuaternionOracle) :
    (numericalCorrection entry inverseLabel approx t target).length≤5*L := by
  let u := approx target
  let r := quaternionOracleMul target (quaternionOracleInverse (quaternionWordOracle entry u))
  change (if residualSmall r t=true then u else
    u++instructionInverse inverseLabel (approx (conditionedFactorYOracle r t))++
      instructionInverse inverseLabel (approx (conditionedFactorXOracle r t))++
      approx (conditionedFactorYOracle r t)++approx (conditionedFactorXOracle r t)).length≤_
  split_ifs
  · have h := hL target; change u.length≤L at h; omega
  · simp only [List.length_append,instructionInverse,List.length_map,List.length_reverse]
    have hu := hL target
    have ha := hL (conditionedFactorXOracle r t)
    have hb := hL (conditionedFactorYOracle r t)
    change u.length≤L at hu
    omega

theorem numericalCorrection_error {m : ℕ} (entry : Fin m → QuaternionOracle)
    (G : Fin m → SU2) (hentry : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (approx : QuaternionOracle → List (Fin m)) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (heach : ∀ (U : SU2) (f : QuaternionOracle),QApproximates f U →
      unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G (approx f)))≤ε)
    (t : ℕ) (hstop : 2*(1/2:ℝ)^t≤6*ε*Real.sqrt ε)
    (U : SU2) (f : QuaternionOracle) (hf : QApproximates f U) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (numericalCorrection entry inverseLabel approx t f)))≤
        6*ε*Real.sqrt ε := by
  let uw := approx f
  let u := instructionWordValue G uw
  let R := U*u⁻¹
  let r := quaternionOracleMul f (quaternionOracleInverse (quaternionWordOracle entry uw))
  have hr : QApproximates r R := quaternionOracleMul_correct _ _ _ _ hf
    (quaternionOracleInverse_correct _ _ (quaternionWordOracle_correct entry G hentry uw))
  have hRu : unitaryDistance (su2AsUnitary R) 1=
      unitaryDistance (su2AsUnitary U) (su2AsUnitary u) := by
    have hu : su2AsUnitary u*(su2AsUnitary u)⁻¹=1 := mul_inv_cancel _
    rw [← hu,su2AsUnitary_mul,su2AsUnitary_inv,unitaryDistance_mul_right]
  have hR : unitaryDistance (su2AsUnitary R) 1≤ε := by rw [hRu]; exact heach U f hf
  by_cases hs : residualSmall r t=true
  · have hword : numericalCorrection entry inverseLabel approx t f=uw := by
      change (if residualSmall r t=true then uw else _)=uw
      rw [if_pos hs]
    rw [hword,← hRu]
    exact ((residualSmall_correct r R hr t).1 hs).trans hstop
  · have hsfalse : residualSmall r t=false := Bool.eq_false_iff.mpr hs
    have hσ := (residualSmall_correct r R hr t).2 hsfalse
    obtain ⟨A,B,hAo,hBo,hAB,hA,hB⟩ := conditionedFactors_correct r R hr t hσ (hR.trans hε1)
    let aw := approx (conditionedFactorXOracle r t)
    let bw := approx (conditionedFactorYOracle r t)
    let A' := instructionWordValue G aw
    let B' := instructionWordValue G bw
    have hAε : unitaryDistance (su2AsUnitary A) 1≤Real.sqrt ε := hA.trans (Real.sqrt_le_sqrt hR)
    have hBε : unitaryDistance (su2AsUnitary B) 1≤Real.sqrt ε := hB.trans (Real.sqrt_le_sqrt hR)
    have hcomm := unitaryCommutator_error (su2AsUnitary A) (su2AsUnitary B)
      (su2AsUnitary A') (su2AsUnitary B') (Real.sqrt ε) ε (Real.sqrt_nonneg _) hε hAε hBε
      (heach A _ hAo) (heach B _ hBo)
    have hshape : numericalCorrection entry inverseLabel approx t f=
        uw++instructionInverse inverseLabel bw++instructionInverse inverseLabel aw++bw++aw := by
      change (if residualSmall r t=true then uw else _)=_
      rw [if_neg hs]
    have hval : instructionWordValue G (numericalCorrection entry inverseLabel approx t f)=
        su2Commutator A' B'*u := by
      rw [hshape]
      simp only [instructionWordValue_append,instructionInverse,instructionWordValue_inverse G inverseLabel hi,
        su2Commutator,mul_assoc]
      rfl
    rw [hval,su2AsUnitary_mul]
    have hU : U=R*u := by dsimp [R]; simp
    rw [hU,su2AsUnitary_mul,unitaryDistance_mul_right,hAB,su2Commutator_unitary,su2Commutator_unitary]
    apply hcomm.trans
    have hroot : ε≤Real.sqrt ε := by
      have ht := Real.sq_sqrt hε
      have hp := Real.sqrt_nonneg ε
      nlinarith
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hroot)]

end CircuitRecursion
