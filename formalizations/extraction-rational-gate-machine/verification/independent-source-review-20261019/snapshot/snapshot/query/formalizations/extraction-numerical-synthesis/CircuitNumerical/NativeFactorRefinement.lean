import CircuitNumerical.NativeExpressionRefinement

namespace CircuitRecursion

theorem NativeScalarOracleRefines.eval_eq {f : NativeScalarExpressionOracle} {F : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) : evaluateNativeScalarOracle f=evaluateScalarOracle F :=
  funext (fun p => (hf p).eval_eq)

theorem NativePacketOracleRefines.eval_eq {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : evaluateNativePacketOracle f=evaluatePacketOracle F :=
  funext (fun p => (hf p).eval_eq)

theorem nativeExpressionAdd_refines {f g : NativeScalarExpressionOracle} {F G : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) (hg : NativeScalarOracleRefines g G) :
    NativeScalarOracleRefines (nativeExpressionAdd f g) (expressionAdd F G) :=
  fun p => (hf (p+1)).add (hg (p+1))
theorem nativeExpressionNeg_refines {f : NativeScalarExpressionOracle} {F : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) : NativeScalarOracleRefines (nativeExpressionNeg f) (expressionNeg F) :=
  fun p => (hf p).neg
theorem nativeExpressionMul_refines {f g : NativeScalarExpressionOracle} {F G : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) (hg : NativeScalarOracleRefines g G) (b : ℕ) :
    NativeScalarOracleRefines (nativeExpressionMul b f g) (expressionMul b F G) :=
  fun p => (hf (p+b+2)).mul (hg (p+b+2))
theorem nativeExpressionInv_refines {f : NativeScalarExpressionOracle} {F : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) (b : ℕ) :
    NativeScalarOracleRefines (nativeExpressionInv b f) (expressionInv b F) := fun p => (hf (p+2*b+2)).inv
theorem nativeExpressionSqrt_refines {f : NativeScalarExpressionOracle} {F : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) : NativeScalarOracleRefines (nativeExpressionSqrt f) (expressionSqrt F) :=
  fun p => (hf (2*p+2)).sqrt (p+1)
theorem nativeExpressionMeanMinus_refines {f : NativeScalarExpressionOracle} {F : ScalarExpressionOracle}
    (hf : NativeScalarOracleRefines f F) : NativeScalarOracleRefines (nativeExpressionMeanMinus f) (expressionMeanMinus F) :=
  fun p => (hf p).meanMinus
theorem nativeExpressionCoordinate_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (i : Fin 4) :
    NativeScalarOracleRefines (nativeExpressionCoordinate f i) (expressionCoordinate F i) := fun p => NativeScalarRefines.coordinate (hf p) i
theorem nativeExpressionPacketMul_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) :
    NativePacketOracleRefines (nativeExpressionPacketMul f g) (expressionPacketMul F G) :=
  fun p => (hf (p+4)).mul (hg (p+4))
theorem nativeExpressionPacketInverse_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativePacketOracleRefines (nativeExpressionPacketInverse f) (expressionPacketInverse F) :=
  fun p => (hf p).inverse
theorem nativeExpressionDistance_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) (p : ℕ) :
    NativeScalarRefines (nativeExpressionDistance f g p) (expressionDistance F G p) :=
  NativeScalarRefines.distance (hf (p+6)) (hg (p+6))

theorem nativeExpressionBalancedS_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativeScalarOracleRefines (nativeExpressionBalancedS f) (expressionBalancedS F) :=
  nativeExpressionSqrt_refines (nativeExpressionSqrt_refines
    (nativeExpressionMeanMinus_refines (nativeExpressionCoordinate_refines hf 0)))

theorem nativeExpressionBalancedC_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativeScalarOracleRefines (nativeExpressionBalancedC f) (expressionBalancedC F) :=
  nativeExpressionSqrt_refines (nativeExpressionAdd_refines (fun _ => nativeScalarOne_refines)
    (nativeExpressionNeg_refines (nativeExpressionMul_refines (nativeExpressionBalancedS_refines hf)
      (nativeExpressionBalancedS_refines hf) 0)))

theorem nativeExpressionReferenceX_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativePacketOracleRefines (nativeExpressionReferenceX f) (expressionReferenceX F) := by
  intro p
  apply NativePacketRefines.tuple
  intro i
  fin_cases i
  · exact nativeExpressionBalancedC_refines hf p
  · exact nativeScalarZero_refines
  · exact nativeScalarZero_refines
  · exact nativeExpressionBalancedS_refines hf p

theorem nativeExpressionReferenceY_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativePacketOracleRefines (nativeExpressionReferenceY f) (expressionReferenceY F) := by
  intro p
  apply NativePacketRefines.tuple
  intro i
  fin_cases i
  · exact nativeExpressionBalancedC_refines hf p
  · exact nativeScalarZero_refines
  · exact nativeExpressionBalancedS_refines hf p
  · exact nativeScalarZero_refines

theorem nativeExpressionBalancedReference_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) :
    NativePacketOracleRefines (nativeExpressionBalancedReference f) (expressionBalancedReference F) :=
  nativeExpressionPacketMul_refines
    (nativeExpressionPacketMul_refines
      (nativeExpressionPacketMul_refines (nativeExpressionReferenceX_refines hf) (nativeExpressionReferenceY_refines hf))
      (nativeExpressionPacketInverse_refines (nativeExpressionReferenceX_refines hf)))
    (nativeExpressionPacketInverse_refines (nativeExpressionReferenceY_refines hf))

theorem nativeExpressionChartTarget_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (j : Fin 4) :
    NativePacketOracleRefines (nativeExpressionChartTarget f j) (expressionChartTarget F j) :=
  nativeExpressionPacketMul_refines (nativeExpressionPacketMul_refines (nativeFrame_refines j) hf)
    (nativeExpressionPacketInverse_refines (nativeFrame_refines j))

theorem nativeExpressionChartMass_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) (p : ℕ) (j : Fin 4) :
    NativeScalarRefines (nativeExpressionChartMass f g p j) (expressionChartMass F G p j) :=
  nativeExpressionDistance_refines hf (nativeExpressionPacketInverse_refines (nativeExpressionChartTarget_refines hg j)) p

theorem nativeExpressionRadius_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) (j : Fin 4) :
    NativeScalarOracleRefines (nativeExpressionRadius f g j) (expressionRadius F G j) :=
  nativeExpressionSqrt_refines (fun p => nativeExpressionChartMass_refines hf hg p j)

theorem nativeExpressionNormalized_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) (t : ℕ) (j : Fin 4) :
    NativePacketOracleRefines (nativeExpressionNormalized f g t j) (expressionNormalized F G t j) := by
  intro p
  apply NativePacketRefines.tuple
  intro i
  exact nativeExpressionMul_refines
    (nativeExpressionAdd_refines (nativeExpressionCoordinate_refines hf i)
      (nativeExpressionNeg_refines (nativeExpressionCoordinate_refines
        (nativeExpressionPacketInverse_refines (nativeExpressionChartTarget_refines hg j)) i)))
    (nativeExpressionInv_refines (nativeExpressionRadius_refines hf hg j) (t+1)) (t+2) p

theorem nativeExpressionConjugator_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (t : ℕ) :
    NativePacketOracleRefines (nativeExpressionConjugator f t) (expressionConjugator F t) := by
  intro p
  apply NativePacketRefines.selectMax
  · intro j
    exact nativeExpressionChartMass_refines hf (nativeExpressionBalancedReference_refines hf) (2*t+2) j
  · intro j
    exact nativeExpressionPacketMul_refines
      (nativeExpressionNormalized_refines hf (nativeExpressionBalancedReference_refines hf) t j) (nativeFrame_refines j) p

theorem nativeExpressionConjugate_refines {f g : NativePacketExpressionOracle} {F G : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (hg : NativePacketOracleRefines g G) :
    NativePacketOracleRefines (nativeExpressionConjugate f g) (expressionConjugate F G) :=
  nativeExpressionPacketMul_refines (nativeExpressionPacketMul_refines hf hg) (nativeExpressionPacketInverse_refines hf)

theorem nativeExpressionFactorX_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (t : ℕ) :
    NativePacketOracleRefines (nativeExpressionFactorX f t) (expressionFactorX F t) :=
  nativeExpressionConjugate_refines (nativeExpressionConjugator_refines hf t) (nativeExpressionReferenceX_refines hf)

theorem nativeExpressionFactorY_refines {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) (t : ℕ) :
    NativePacketOracleRefines (nativeExpressionFactorY f t) (expressionFactorY F t) :=
  nativeExpressionConjugate_refines (nativeExpressionConjugator_refines hf t) (nativeExpressionReferenceY_refines hf)

theorem nativeExpressionWord_refines {m : ℕ} {entry : Fin m → NativePacketExpressionOracle}
    {E : Fin m → PacketExpressionOracle} (he : ∀ i,NativePacketOracleRefines (entry i) (E i))
    (w : List (Fin m)) : NativePacketOracleRefines (nativeExpressionWord entry w) (expressionWord E w) := by
  induction w with
  | nil => exact nativePacketOne_refines
  | cons i w ih => exact nativeExpressionPacketMul_refines ih (he i)

end CircuitRecursion
