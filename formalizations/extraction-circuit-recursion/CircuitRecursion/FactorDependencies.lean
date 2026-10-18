import CircuitRecursion.OracleDependencies

namespace CircuitRecursion

theorem chooseChart_agrees (f f' g g' : QuaternionOracle) (t : ℕ)
    (hf : AgreesThrough f f' (2*t+8)) (hg : AgreesThrough g g' (2*t+16)) :
    chooseChart f g t=chooseChart f' g' t := by
  have hs : chartMassScore f g (2*t+2)=chartMassScore f' g' (2*t+2) := by
    funext j
    exact chartMassScore_agrees f f' g g' j (2*t+2)
      (hf.mono (by omega)) (hg.mono (by omega)) _ (le_refl _)
  simp only [chooseChart,hs]

theorem coordinateSubOracle_agrees (f f' g g' : QuaternionOracle) (i : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' (P+1)) (hg : AgreesThrough g g' (P+1)) :
    AgreesThrough (coordinateSubOracle f g i) (coordinateSubOracle f' g' i) P := by
  exact oracleAdd_agrees _ _ _ _ P (coordinateOracle_agrees _ _ i _ hf)
    (oracleNeg_agrees _ _ _ (coordinateOracle_agrees _ _ i _ hg))

theorem intertwinerRadiusOracle_agrees (f f' g g' : QuaternionOracle) (j : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' (2*P+8)) (hg : AgreesThrough g g' (2*P+16)) :
    AgreesThrough (intertwinerRadiusOracle f g j) (intertwinerRadiusOracle f' g' j) P := by
  exact oracleSqrt_agrees _ _ P (chartMassScore_agrees _ _ _ _ j (2*P+2)
    (hf.mono (by omega)) (hg.mono (by omega)))

theorem normalizedIntertwinerOracle_agrees (f f' g g' : QuaternionOracle) (t : ℕ) (j : Fin 4) (P : ℕ)
    (hf : AgreesThrough f f' (2*P+6*t+24)) (hg : AgreesThrough g g' (2*P+6*t+32)) :
    AgreesThrough (normalizedIntertwinerOracle f g t j) (normalizedIntertwinerOracle f' g' t j) P := by
  have hrad := intertwinerRadiusOracle_agrees f f' g g' j (P+3*t+8)
    (hf.mono (by omega)) (hg.mono (by omega))
  have hinv := oracleInv_agrees (t+1) (intertwinerRadiusOracle f g j)
    (intertwinerRadiusOracle f' g' j) (P+t+4) (hrad.mono (by omega))
  have hchart := quaternionOracleInverse_agrees _ _ (P+t+5)
    (chartTargetOracle_agrees g g' j (P+t+5) (hg.mono (by omega)))
  intro p hp
  apply List.Vector.ext
  intro i
  simp only [normalizedIntertwinerOracle,List.Vector.get_ofFn]
  exact oracleMul_agrees (t+2) _ _ _ _ P
    (coordinateSubOracle_agrees _ _ _ _ i (P+t+4) (hf.mono (by omega)) hchart)
    (hinv.mono (by omega)) p hp

theorem conditionedConjugatorOracle_agrees (f f' : QuaternionOracle) (t P : ℕ)
    (hf : AgreesThrough f f' (16*P+48*t+442)) :
    AgreesThrough (conditionedConjugatorOracle f t) (conditionedConjugatorOracle f' t) P := by
  have hc := chooseChart_agrees f f' (balancedReferenceOracle f) (balancedReferenceOracle f') t
    (hf.mono (by omega))
    (balancedReferenceOracle_agrees f f' (2*t+16) (hf.mono (by omega)))
  simp only [conditionedConjugatorOracle,hc]
  apply quaternionOracleMul_agrees
  · exact normalizedIntertwinerOracle_agrees f f' (balancedReferenceOracle f) (balancedReferenceOracle f')
      t _ (P+4) (hf.mono (by omega))
      (balancedReferenceOracle_agrees f f' (2*(P+4)+6*t+32) (hf.mono (by omega)))
  · exact AgreesThrough.refl _ _

theorem conditionedFactorXOracle_agrees (f f' : QuaternionOracle) (t P : ℕ)
    (hf : AgreesThrough f f' (16*P+48*t+570)) :
    AgreesThrough (conditionedFactorXOracle f t) (conditionedFactorXOracle f' t) P := by
  exact quaternionConjugateOracle_agrees _ _ _ _ P
    (conditionedConjugatorOracle_agrees f f' t (P+8) (hf.mono (by omega)))
    (referenceXOracle_agrees f f' (P+8) (hf.mono (by omega)))

theorem conditionedFactorYOracle_agrees (f f' : QuaternionOracle) (t P : ℕ)
    (hf : AgreesThrough f f' (16*P+48*t+570)) :
    AgreesThrough (conditionedFactorYOracle f t) (conditionedFactorYOracle f' t) P := by
  exact quaternionConjugateOracle_agrees _ _ _ _ P
    (conditionedConjugatorOracle_agrees f f' t (P+8) (hf.mono (by omega)))
    (referenceYOracle_agrees f f' (P+8) (hf.mono (by omega)))

end CircuitRecursion
