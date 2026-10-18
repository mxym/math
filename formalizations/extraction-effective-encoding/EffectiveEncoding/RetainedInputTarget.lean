import EffectiveEncoding.RetainedNativeProvider
import CircuitNumerical.InputNumericalSynthesis

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure RetainedInputTargetResult (m L q : ℕ) where
  prepared : NativeSingleInput
  providerPrograms : List.Vector PacketWordEvaluation (numericalDemand L (Nat.clog 2 (q+1))+1)
  cached : InputCachedWordResult m (numericalDemand L (Nat.clog 2 (q+1)))

/-- Actual eager target-provider runs are retained once. The online input AST
performs and retains every visited cache read in the same numerical execution.
Resolution/interpretation and decoded data are used only in proofs. -/
def retainedInputTargetRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : RetainedInputTargetResult m L q :=
  let prepared:=prepareNativeSingleInput u
  let depth:=Nat.clog 2 (q+1)
  let P:=numericalDemand L depth
  let gates:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let providerPrograms:=buildNativeTargetPrograms prepared P
  let targetCache:=providerPrograms.map PacketWordEvaluation.value
  let cache:=NativeCacheEnvironment.mk gates targetCache
  let program:=inputTracedPairWord cache inputGateOracle inverseLabel table depth (inputTargetOracle m)
  ⟨prepared,providerPrograms,⟨cache,program⟩⟩

/-- Exact full cached program, not only equality of its emitted word. -/
theorem retainedInputTargetRun_cached {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedInputTargetRun entry inverseLabel table L q u).cached=
      inputCachedRun entry inverseLabel table L q (prepareNativeSingleInput u).packetDataOracle := by
  simp only [retainedInputTargetRun,buildNativeTargetPrograms_values,inputCachedRun]


theorem retainedInputTargetRun_cache {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedInputTargetRun entry inverseLabel table L q u).cached.cache.target=
      (retainedInputTargetRun entry inverseLabel table L q u).providerPrograms.map PacketWordEvaluation.value := rfl


theorem retainedInputTargetRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    (retainedInputTargetRun entry inverseLabel table L q u).cached.program.word=
      descriptorSynthesis (fun i => nativePacketDataOracle (entry i)) inverseLabel table L q u := by
  rw [retainedInputTargetRun_cached,inputCachedRun_word entry inverseLabel table L q hL,
    nativePreparedTargetOracle_eq]
  exact ((cachedArithmeticRun_word _ inverseLabel table L q u.quaternionOracle).trans
    (cachedNumericalRun_word _ inverseLabel table L q hL u.quaternionOracle)).symm


def RetainedInputTargetResult.providerActions {m L q : ℕ} (r : RetainedInputTargetResult m L q) : ℕ :=
  (r.providerPrograms.toList.map (fun run => run.trace.booleanActions)).sum

/-- The same retained provider programs as the previously bounded eager cache. -/
theorem retainedInputTargetRun_providerActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedInputTargetRun entry inverseLabel table L q u).providerActions=
      (retainedNativeTargetRun entry inverseLabel table L q u).providerActions := rfl


theorem retainedInputTargetRun_providerActions_polynomial {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) :
    (retainedInputTargetRun entry inverseLabel table L q u).providerActions≤
      nativeProviderCachePolynomialConstant L*(k+3)^15*(q+1)^27 := by
  rw [retainedInputTargetRun_providerActions]
  exact (retainedNativeTargetRun_providerActions_polynomial entry inverseLabel table L q hu).trans
    (Nat.mul_le_mul_right _ (nativeProviderCacheCoefficient_polynomial k L))


def actualInputOnlineCoefficient (m n L k gateB : ℕ) : ℕ :=
  actualNativeBooleanCoefficient n L k gateB+
    80*(m+51200000*(L+1)+5)*(1020*(n+1)*(2*L+1)*offsetGrowth)

/-- Numeric and actual cache-read primitives belong to this same input AST
execution. Actual target height is internal; only queried library height is supplied. -/
theorem retainedInputTargetRun_onlineActions {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (q+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(q+1)^9)) :
    (retainedInputTargetRun entry inverseLabel table L q u).cached.program.onlineActions≤
      actualInputOnlineCoefficient m n L k gateB*(q+1)^338 := by
  rw [retainedInputTargetRun_cached]
  apply inputCachedRun_onlineActions_degree338 entry inverseLabel table L q
    (nativeTargetInputCoefficient k L gateB) hL (prepareNativeSingleInput u).packetDataOracle
  · intro i r hr
    exact IntegerPacketHeight.mono _ _ _ (he i r hr)
      (Nat.mul_le_mul_right _ (nativeTargetInputCoefficient_gate k L gateB))
  · intro r hr
    exact IntegerPacketHeight.mono _ _ _ (nativePreparedTarget_cache_height hu L q r hr)
      (Nat.mul_le_mul_right _ (nativeTargetInputCoefficient_target k L gateB))

end EffectiveEncoding
