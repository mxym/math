import CircuitNumerical.InputAssemblyBounds

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem listAssemblyGrowth_precision_bound (p : ℕ) :
    8192^(Nat.clog 2 (p+1))≤8192*(p+1)^13 := by
  have h:=pow_clog_two_le (p+1) (by omega)
  calc
    _=(2^Nat.clog 2 (p+1))^13 := by
      change (2^13)^Nat.clog 2 (p+1)=(2^Nat.clog 2 (p+1))^13
      rw [←Nat.pow_mul,←Nat.pow_mul,Nat.mul_comm]
    _≤(2*(p+1))^13 := Nat.pow_le_pow_left h _
    _=_ := by rw [mul_pow];rfl

theorem assembledInputPairWord_actions_degree13 {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : InputPacketExpressionOracle m) :
    (assembledInputPairWord cache entry inverseLabel table (Nat.clog 2 (p+1)) f).trace.actions≤
      (8192*(L+2*(n+1)+2))*(p+1)^13 := by
  have h:=(assembledInputPairWord_bounds cache entry inverseLabel table L hL (Nat.clog 2 (p+1)) f).2
  exact h.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    Nat.mul_le_mul_right (L+2*(n+1)+2) (listAssemblyGrowth_precision_bound p))

theorem assembledInputPairWord_inverseCalls_degree13 {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : InputPacketExpressionOracle m) :
    (assembledInputPairWord cache entry inverseLabel table (Nat.clog 2 (p+1)) f).trace.inverseCalls≤
      (8192*(L+2*(n+1)+2))*(p+1)^13 :=
  (InputListAssemblyTrace.inverseCalls_le_actions _).trans
    (assembledInputPairWord_actions_degree13 cache entry inverseLabel table L p hL f)

structure AssembledInputCachedWordResult (m P : ℕ) where
  cache : NativeCacheEnvironment m P
  program : AssembledInputWordResult m

/-- Actual cache construction followed by actual assembled word recursion.
It does not call inputCachedRun and then reconstruct the returned word. -/
def assembledInputCachedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (target : NativePacketDataOracle) : AssembledInputCachedWordResult m (numericalDemand L (Nat.clog 2 (p+1))) :=
  let depth:=Nat.clog 2 (p+1)
  let P:=numericalDemand L depth
  let gates:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let targetCache:=buildNativePacketCache target P
  let cache:=NativeCacheEnvironment.mk gates targetCache
  let program:=assembledInputPairWord cache inputGateOracle inverseLabel table depth (inputTargetOracle m)
  ⟨cache,program⟩

def AssembledInputCachedWordResult.erase {m P : ℕ} (r : AssembledInputCachedWordResult m P) : InputCachedWordResult m P :=
  ⟨r.cache,r.program.program⟩

theorem assembledInputCachedRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : NativePacketDataOracle) :
    (assembledInputCachedRun entry inverseLabel table L p f).erase=inputCachedRun entry inverseLabel table L p f := by
  simp only [assembledInputCachedRun,AssembledInputCachedWordResult.erase,assembledInputPairWord_program,inputCachedRun]

theorem assembledInputCachedRun_program {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : NativePacketDataOracle) :
    (assembledInputCachedRun entry inverseLabel table L p f).program.program=(inputCachedRun entry inverseLabel table L p f).program :=
  congrArg InputCachedWordResult.program (assembledInputCachedRun_erase entry inverseLabel table L p f)

theorem assembledInputCachedRun_actions_degree13 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (assembledInputCachedRun entry inverseLabel table L p f).program.trace.actions≤
      (8192*(L+2*(n+1)+2))*(p+1)^13 :=
  assembledInputPairWord_actions_degree13 _ inputGateOracle inverseLabel table L p hL (inputTargetOracle m)

/-- Executed numerical primitives, concrete online cache list traversals and
concrete retained-list copies/reverse-maps. Inverse-label provider calls are
counted separately; this remains a partial source-cost semantics. -/
def AssembledInputWordResult.onlineActions {m : ℕ} (r : AssembledInputWordResult m) : ℕ :=
  r.program.onlineActions+r.trace.actions

theorem assembledInputCachedRun_onlineActions_degree338 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p A : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (entry i r).decode (A*(p+1)^9))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (f r).decode (A*(p+1)^9)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (assembledInputCachedRun entry inverseLabel table L p f).program.onlineActions≤
      (40000*(40*C+4)^2*(20*O)+80*(m+51200000*(L+1)+5)*O+8192*(L+2*(n+1)+2))*(p+1)^338 := by
  have hn:=inputCachedRun_onlineActions_degree338 entry inverseLabel table L p A hL f he hf
  have hs:=assembledInputCachedRun_actions_degree13 entry inverseLabel table L p hL f
  have hp : (p+1)^13≤(p+1)^338 := Nat.pow_le_pow_right (by omega) (by decide)
  have hss:=hs.trans (Nat.mul_le_mul_left _ hp)
  unfold AssembledInputWordResult.onlineActions
  rw [assembledInputCachedRun_program]
  exact (Nat.add_le_add hn hss).trans_eq (Nat.add_mul _ _ _).symm

/-- Semantic correctness and fidelity statements for inputCachedRun can be
transported using the whole-record theorem; the numerical/cache traces are
part of that equality, not inferred from the output word alone. -/
theorem assembledInputCachedRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (assembledInputCachedRun entry inverseLabel table L p f).program.program.word=
      numericalPairWord (fun i => nativePacketDataOracle (entry i)) inverseLabel table
        (Nat.clog 2 (p+1)) (nativePacketDataOracle f) := by
  rw [assembledInputCachedRun_program]
  exact inputCachedRun_word entry inverseLabel table L p hL f

end CircuitRecursion
