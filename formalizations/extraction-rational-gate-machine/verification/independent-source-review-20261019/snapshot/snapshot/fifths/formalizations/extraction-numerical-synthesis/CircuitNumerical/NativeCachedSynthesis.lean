import CircuitNumerical.NativeNumericalExecution

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

def nativePacketDataOracle (f : NativePacketDataOracle) : QuaternionOracle :=
  fun p => (f p).decode.value

theorem nativeCachedPacketOracle_agrees (f : NativePacketDataOracle) (P : ℕ) :
    AgreesThrough (evaluateNativePacketOracle (nativeCachedPacketOracle (buildNativePacketCache f P)))
      (nativePacketDataOracle f) P := by
  intro p hp
  change (rawPacketExpression (readNativePacketCache (buildNativePacketCache f P) p).decode).eval=_
  rw [rawPacketExpression_eval,readNativePacketCache_build f P p hp]
  rfl

structure NativeCachedWordResult (m P : ℕ) where
  gateCaches : List.Vector (List.Vector WordIntegerPacket (P+1)) m
  targetCache : List.Vector WordIntegerPacket (P+1)
  program : NativeArithmeticWordResult m

/-- Every provider supplies actual canonical binary data. The eager gate and
target vectors are retained before the native numerical recursion starts.
The value path calls neither Nat.bits nor rational interpretation. -/
def nativeCachedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : NativePacketDataOracle) :
    NativeCachedWordResult m (numericalDemand L (Nat.clog 2 (p+1))) :=
  let depth:=Nat.clog 2 (p+1)
  let P:=numericalDemand L depth
  let gateCaches:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let targetCache:=buildNativePacketCache target P
  let program:=nativeTracedPairWord (fun i => nativeCachedPacketOracle (gateCaches.get i))
    inverseLabel table depth (nativeCachedPacketOracle targetCache)
  ⟨gateCaches,targetCache,program⟩

theorem nativeCachedRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (nativeCachedRun entry inverseLabel table L p f).program.word=
      numericalPairWord (fun i => nativePacketDataOracle (entry i)) inverseLabel table
        (Nat.clog 2 (p+1)) (nativePacketDataOracle f) := by
  simp only [nativeCachedRun,nativeTracedPairWord_word,List.Vector.get_ofFn]
  exact numericalPairWord_agrees _ _ inverseLabel table L hL _
    (fun i => nativeCachedPacketOracle_agrees (entry i) _) _ _ (nativeCachedPacketOracle_agrees f _)

theorem nativeCachedRun_targetLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (f : NativePacketDataOracle) :
    (nativeCachedRun entry inverseLabel table L p f).targetCache.toList.length=
      numericalDemand L (Nat.clog 2 (p+1))+1 :=
  (nativeCachedRun entry inverseLabel table L p f).targetCache.2

theorem nativeCachedRun_gateLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (f : NativePacketDataOracle) (i : Fin m) :
    ((nativeCachedRun entry inverseLabel table L p f).gateCaches.get i).toList.length=
      numericalDemand L (Nat.clog 2 (p+1))+1 :=
  ((nativeCachedRun entry inverseLabel table L p f).gateCaches.get i).2

theorem nativeCachedRun_length {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (nativeCachedRun entry inverseLabel table L p f).program.word.length≤32*L*(p+1)^5 := by
  rw [nativeCachedRun_word entry inverseLabel table L p hL f]
  have ht:=numericalPairWord_length (fun i => nativePacketDataOracle (entry i)) inverseLabel table L hL
    (Nat.clog 2 (p+1)) (nativePacketDataOracle f)
  have hp:=Nat.mul_le_mul_left L (precisionDepth_length p)
  exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)

theorem nativeCachedRun_error {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (G : Fin m → SU2) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (f : NativePacketDataOracle) (U : SU2) (hf : QApproximates (nativePacketDataOracle f) U) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
      (nativeCachedRun entry inverseLabel table L p f).program.word))≤(1/2:ℝ)^p := by
  rw [nativeCachedRun_word entry inverseLabel table L p hL f]
  have ht:=numericalPairWord_error (fun i => nativePacketDataOracle (entry i)) G he inverseLabel hi
    table hcover (Nat.clog 2 (p+1)) U (nativePacketDataOracle f) hf
  have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
  exact ht.trans (skPairError_precision _ p hp)

end CircuitRecursion
