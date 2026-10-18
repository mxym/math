import EffectiveEncoding.BooleanRawDescriptor

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Coefficient for the actual cached raw descriptor's online Boolean/list
numeric actions. Provider, literal adapter and structural costs are separate. -/
def actualBooleanDescriptorCoefficient (n L k : ℕ) : ℕ :=
  40000*(2*(2*(actualTraceConstant n L*(k+3)^7))+4)^2*
    (1020*(n+1)*(2*L+1)*offsetGrowth)


theorem booleanRawDescriptorRun_actions {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (booleanRawDescriptorRun entry inverseLabel table L q u).booleanActions≤
      actualBooleanDescriptorCoefficient n L k*(q+1)^338 := by
  let C:=2*(actualTraceConstant n L*(k+3)^7)
  let O:=1020*(n+1)*(2*L+1)*offsetGrowth
  have hb : (booleanRawDescriptorRun entry inverseLabel table L q u).result.integerBitBudget≤C*(q+1)^137 := by
    rw [booleanRawDescriptorRun_result]
    simpa only [C,Nat.mul_assoc] using costedRawDescriptorRun_integerBitBudget entry G he inverseLabel table L q hL hu
  have ho : (booleanRawDescriptorRun entry inverseLabel table L q u).result.operations≤O*(q+1)^64 := by
    rw [booleanRawDescriptorRun_result]
    exact costedRawCachedRun_operations _ _ _ L q hL _
  exact booleanRawCachedRun_actions_power _ _ _ L q _ 137 64 C O hb ho


theorem booleanTargetDescriptorRun_actions {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (booleanTargetDescriptorRun entry inverseLabel table L q u).online.booleanActions≤
      actualBooleanDescriptorCoefficient n L k*(q+1)^338 := by
  rw [booleanTargetDescriptorRun_online]
  exact booleanRawDescriptorRun_actions entry G he inverseLabel table L q hL hu


theorem booleanTargetDescriptorRun_providerRootCharge_bound {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (booleanTargetDescriptorRun entry inverseLabel table L q u).providerRootCharge≤
      rawProviderCachePolynomialConstant L*(k+3)^8*(q+1)^18 := by
  rw [booleanTargetDescriptorRun_providerRootCharge]
  exact rawTargetProgramCacheCharge_polynomial_kq hu L q


theorem nativeDescriptorRun_actualWord (k : ℕ) : (nativeDescriptorRun k).word=extractionCode k := by
  rw [nativeDescriptorRun_eq,rankedDescriptorRun_word,literalExtractionCode_eq,
    constructedExtractionCode_eq,packedExtractionCode_eq,tripleStoredExtractionCode_eq,storedExtractionCode_eq]

end EffectiveEncoding
