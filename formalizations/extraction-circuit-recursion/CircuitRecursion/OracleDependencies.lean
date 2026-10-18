import CircuitRecursion.NumericalSK

namespace CircuitRecursion

/-- A finite dependency statement, independent of semantic correctness of
the input packets. It will justify a concrete eager input cache. -/
def AgreesThrough {α : Type*} (f g : ℕ → α) (P : ℕ) : Prop := ∀ p,p≤P → f p=g p

theorem AgreesThrough.mono {α : Type*} {f g : ℕ → α} {P Q : ℕ}
    (h : AgreesThrough f g P) (hQ : Q≤P) : AgreesThrough f g Q :=
  fun p hp => h p (hp.trans hQ)

theorem AgreesThrough.refl {α : Type*} (f : ℕ → α) (P : ℕ) : AgreesThrough f f P := fun _ _ => rfl

theorem oracleAdd_agrees (f f' g g' : RationalOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+1)) (hg : AgreesThrough g g' (P+1)) :
    AgreesThrough (oracleAdd f g) (oracleAdd f' g') P := by
  intro p hp
  simp only [oracleAdd,hf (p+1) (by omega),hg (p+1) (by omega)]

theorem oracleNeg_agrees (f f' : RationalOracle) (P : ℕ) (hf : AgreesThrough f f' P) :
    AgreesThrough (oracleNeg f) (oracleNeg f') P := by
  intro p hp
  simp only [oracleNeg,hf p hp]

theorem oracleMul_agrees (b : ℕ) (f f' g g' : RationalOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+b+2)) (hg : AgreesThrough g g' (P+b+2)) :
    AgreesThrough (oracleMul b f g) (oracleMul b f' g') P := by
  intro p hp
  simp only [oracleMul,hf (p+b+2) (by omega),hg (p+b+2) (by omega)]

theorem oracleInv_agrees (b : ℕ) (f f' : RationalOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+2*b+2)) :
    AgreesThrough (oracleInv b f) (oracleInv b f') P := by
  intro p hp
  simp only [oracleInv,hf (p+2*b+2) (by omega)]

theorem oracleSqrt_agrees (f f' : RationalOracle) (P : ℕ)
    (hf : AgreesThrough f f' (2*P+2)) :
    AgreesThrough (oracleSqrt f) (oracleSqrt f') P := by
  intro p hp
  simp only [oracleSqrt,hf (2*p+2) (by omega)]

theorem oracleMeanMinus_agrees (f f' : RationalOracle) (P : ℕ)
    (hf : AgreesThrough f f' P) :
    AgreesThrough (oracleMeanMinus f) (oracleMeanMinus f') P := by
  intro p hp
  simp only [oracleMeanMinus,hf p hp]

theorem coordinateOracle_agrees (f f' : QuaternionOracle) (i : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' P) :
    AgreesThrough (coordinateOracle f i) (coordinateOracle f' i) P := by
  intro p hp
  simp only [coordinateOracle,hf p hp]

theorem quaternionOracleMul_agrees (f f' g g' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+4)) (hg : AgreesThrough g g' (P+4)) :
    AgreesThrough (quaternionOracleMul f g) (quaternionOracleMul f' g') P := by
  intro p hp
  simp only [quaternionOracleMul,hf (p+4) (by omega),hg (p+4) (by omega)]

theorem quaternionOracleInverse_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' P) :
    AgreesThrough (quaternionOracleInverse f) (quaternionOracleInverse f') P := by
  intro p hp
  simp only [quaternionOracleInverse,hf p hp]

theorem quaternionConjugateOracle_agrees (f f' g g' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+8)) (hg : AgreesThrough g g' (P+8)) :
    AgreesThrough (quaternionConjugateOracle f g) (quaternionConjugateOracle f' g') P := by
  apply quaternionOracleMul_agrees
  · exact quaternionOracleMul_agrees _ _ _ _ (P+4) (hf.mono (by omega)) (hg.mono (by omega))
  · exact quaternionOracleInverse_agrees _ _ _ (hf.mono (by omega))

theorem balancedSOracle_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (4*P+6)) :
    AgreesThrough (balancedSOracle f) (balancedSOracle f') P := by
  apply oracleSqrt_agrees
  apply oracleSqrt_agrees
  apply oracleMeanMinus_agrees
  exact coordinateOracle_agrees _ _ 0 _ (hf.mono (by omega))

theorem balancedCOracle_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (8*P+26)) :
    AgreesThrough (balancedCOracle f) (balancedCOracle f') P := by
  apply oracleSqrt_agrees
  apply oracleAdd_agrees
  · exact AgreesThrough.refl _ _
  · apply oracleNeg_agrees
    apply oracleMul_agrees
    · exact balancedSOracle_agrees _ _ _ (hf.mono (by omega))
    · exact balancedSOracle_agrees _ _ _ (hf.mono (by omega))

theorem referenceXOracle_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (8*P+26)) :
    AgreesThrough (referenceXOracle f) (referenceXOracle f') P := by
  have hc := balancedCOracle_agrees f f' P hf
  have hs := balancedSOracle_agrees f f' P (hf.mono (by omega))
  intro p hp
  simp only [referenceXOracle,hc p hp,hs p hp]

theorem referenceYOracle_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (8*P+26)) :
    AgreesThrough (referenceYOracle f) (referenceYOracle f') P := by
  have hc := balancedCOracle_agrees f f' P hf
  have hs := balancedSOracle_agrees f f' P (hf.mono (by omega))
  intro p hp
  simp only [referenceYOracle,hc p hp,hs p hp]

theorem balancedReferenceOracle_agrees (f f' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (8*P+122)) :
    AgreesThrough (balancedReferenceOracle f) (balancedReferenceOracle f') P := by
  have hX := referenceXOracle_agrees f f' (P+12) (hf.mono (by omega))
  have hY := referenceYOracle_agrees f f' (P+12) (hf.mono (by omega))
  apply quaternionOracleMul_agrees
  · apply quaternionOracleMul_agrees
    · exact quaternionOracleMul_agrees _ _ _ _ (P+8) (hX.mono (by omega)) (hY.mono (by omega))
    · exact quaternionOracleInverse_agrees _ _ _ (hX.mono (by omega))
  · exact quaternionOracleInverse_agrees _ _ _ (hY.mono (by omega))

theorem chartTargetOracle_agrees (f f' : QuaternionOracle) (j : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' (P+8)) :
    AgreesThrough (chartTargetOracle f j) (chartTargetOracle f' j) P := by
  apply quaternionOracleMul_agrees
  · exact quaternionOracleMul_agrees _ _ _ _ (P+4) (AgreesThrough.refl _ _) (hf.mono (by omega))
  · exact AgreesThrough.refl _ _

theorem distanceScore_agrees (f f' g g' : QuaternionOracle) (P : ℕ)
    (hf : AgreesThrough f f' (P+6)) (hg : AgreesThrough g g' (P+6)) :
    AgreesThrough (distanceScore f g) (distanceScore f' g') P := by
  intro p hp
  simp only [distanceScore,hf (p+6) (by omega),hg (p+6) (by omega)]

theorem chartMassScore_agrees (f f' g g' : QuaternionOracle) (j : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' (P+6)) (hg : AgreesThrough g g' (P+14)) :
    AgreesThrough (fun p => chartMassScore f g p j) (fun p => chartMassScore f' g' p j) P := by
  exact distanceScore_agrees _ _ _ _ P hf
    (quaternionOracleInverse_agrees _ _ _ (chartTargetOracle_agrees _ _ j (P+6) (hg.mono (by omega))))

end CircuitRecursion
