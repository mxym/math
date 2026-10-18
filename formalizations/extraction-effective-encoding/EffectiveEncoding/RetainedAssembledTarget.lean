import EffectiveEncoding.FullyScannedInputExtraction
import CircuitNumerical.InputAssemblyPolynomial

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure RetainedAssembledTargetResult (m L q : ℕ) where
  prepared : NativeSingleInput
  providerPrograms : List.Vector PacketWordEvaluation (numericalDemand L (Nat.clog 2 (q+1))+1)
  cached : AssembledInputCachedWordResult m (numericalDemand L (Nat.clog 2 (q+1)))

/-- Provider records/cache values are built once; the cache-level actual
assembly recursion consumes those stored values without replaying providers. -/
def retainedAssembledTargetRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : RetainedAssembledTargetResult m L q :=
  let prepared:=prepareNativeSingleInput u
  let depth:=Nat.clog 2 (q+1)
  let P:=numericalDemand L depth
  let gates:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let providerPrograms:=buildNativeTargetPrograms prepared P
  let targetCache:=providerPrograms.map PacketWordEvaluation.value
  let cache:=NativeCacheEnvironment.mk gates targetCache
  let program:=assembledInputPairWord cache inputGateOracle inverseLabel table depth (inputTargetOracle m)
  ⟨prepared,providerPrograms,⟨cache,program⟩⟩


def RetainedAssembledTargetResult.erase {m L q : ℕ} (r : RetainedAssembledTargetResult m L q) : RetainedInputTargetResult m L q :=
  ⟨r.prepared,r.providerPrograms,r.cached.erase⟩

/-- Whole previous provider/numeric/read record, not only the emitted word. -/
theorem retainedAssembledTargetRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).erase=
      retainedInputTargetRun entry inverseLabel table L q u := by
  simp only [retainedAssembledTargetRun,RetainedAssembledTargetResult.erase,AssembledInputCachedWordResult.erase,
    assembledInputPairWord_program,retainedInputTargetRun]


theorem retainedAssembledTargetRun_cached {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).cached=
      assembledInputCachedRun entry inverseLabel table L q (prepareNativeSingleInput u).packetDataOracle := by
  simp only [retainedAssembledTargetRun,buildNativeTargetPrograms_values,assembledInputCachedRun]


def RetainedAssembledTargetResult.assemblyActions {m L q : ℕ} (r : RetainedAssembledTargetResult m L q) : ℕ :=
  r.cached.program.trace.actions

def RetainedAssembledTargetResult.inverseCalls {m L q : ℕ} (r : RetainedAssembledTargetResult m L q) : ℕ :=
  r.cached.program.trace.inverseCalls


theorem retainedAssembledTargetRun_assemblyActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).assemblyActions≤
      (8192*(L+2*(n+1)+2))*(q+1)^13 :=
  assembledInputPairWord_actions_degree13 _ inputGateOracle inverseLabel table L q hL (inputTargetOracle m)

/-- Invocation count only; this does not assign a cost to the inverse-label provider. -/
theorem retainedAssembledTargetRun_inverseCalls {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).inverseCalls≤
      (8192*(L+2*(n+1)+2))*(q+1)^13 :=
  assembledInputPairWord_inverseCalls_degree13 _ inputGateOracle inverseLabel table L q hL (inputTargetOracle m)

end EffectiveEncoding
