import CircuitNumerical.InputTraceRefinement

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

def inputTargetOracle (m : ℕ) : InputPacketExpressionOracle m := fun q => .input .target q
def inputGateOracle {m : ℕ} (i : Fin m) : InputPacketExpressionOracle m := fun q => .input (.gate i) q

@[simp] theorem inputTargetOracle_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) :
    resolveInputPacketOracle cache (inputTargetOracle m)=nativeLinearCachedPacketOracle cache.target := rfl
@[simp] theorem inputGateOracle_resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) (i : Fin m) :
    resolveInputPacketOracle cache (inputGateOracle i)=nativeLinearGatePacketOracle cache.gates cache.target i := rfl

structure InputCachedWordResult (m P : ℕ) where
  cache : NativeCacheEnvironment m P
  program : InputArithmeticWordResult m

/-- The cache-index references are retained in the factor AST. The actual
value evaluator performs and records every visited leaf lookup, so the
returned whole-word read trace belongs to this very execution. -/
def inputCachedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (target : NativePacketDataOracle) : InputCachedWordResult m (numericalDemand L (Nat.clog 2 (p+1))) :=
  let depth:=Nat.clog 2 (p+1)
  let P:=numericalDemand L depth
  let gates:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let targetCache:=buildNativePacketCache target P
  let cache:=NativeCacheEnvironment.mk gates targetCache
  let program:=inputTracedPairWord cache inputGateOracle inverseLabel table depth (inputTargetOracle m)
  ⟨cache,program⟩

theorem inputCachedRun_word_eq_native {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : NativePacketDataOracle) :
    (inputCachedRun entry inverseLabel table L p f).program.word=
      (nativeLinearCachedRun entry inverseLabel table L p f).program.word := by
  simp only [inputCachedRun,inputTracedPairWord_word,inputTargetOracle_resolve,inputGateOracle_resolve,
    nativeLinearCachedRun,nativeTracedPairWord_word]

theorem inputCachedRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (inputCachedRun entry inverseLabel table L p f).program.word=
      numericalPairWord (fun i => nativePacketDataOracle (entry i)) inverseLabel table
        (Nat.clog 2 (p+1)) (nativePacketDataOracle f) := by
  rw [inputCachedRun_word_eq_native]
  exact nativeLinearCachedRun_word entry inverseLabel table L p hL f

theorem inputCachedRun_length {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (inputCachedRun entry inverseLabel table L p f).program.word.length≤32*L*(p+1)^5 := by
  rw [inputCachedRun_word_eq_native]
  exact nativeLinearCachedRun_length entry inverseLabel table L p hL f

theorem inputCachedRun_error {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (G : Fin m → SU2) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (f : NativePacketDataOracle) (U : SU2) (hf : QApproximates (nativePacketDataOracle f) U) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
      (inputCachedRun entry inverseLabel table L p f).program.word))≤(1/2:ℝ)^p := by
  rw [inputCachedRun_word_eq_native]
  exact nativeLinearCachedRun_error entry G he inverseLabel hi table L p hL hcover f U hf

end CircuitRecursion
