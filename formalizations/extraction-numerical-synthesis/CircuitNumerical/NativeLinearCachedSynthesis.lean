import CircuitNumerical.NativeLinearPacketCache

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

/-- Native synthesis whose gate-label and precision cache reads use the
explicit list-spine lookup programs. Source provider calls still belong to
the eager cache construction. Numeric expression evaluation retains the
previous canonical Boolean programs. -/
def nativeLinearCachedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : NativePacketDataOracle) :
    NativeCachedWordResult m (numericalDemand L (Nat.clog 2 (p+1))) :=
  let depth:=Nat.clog 2 (p+1)
  let P:=numericalDemand L depth
  let gateCaches:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let targetCache:=buildNativePacketCache target P
  let program:=nativeTracedPairWord (fun i => nativeLinearGatePacketOracle gateCaches targetCache i)
    inverseLabel table depth (nativeLinearCachedPacketOracle targetCache)
  ⟨gateCaches,targetCache,program⟩

theorem nativeLinearCachedRun_eq {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (f : NativePacketDataOracle) :
    nativeLinearCachedRun entry inverseLabel table L p f=nativeCachedRun entry inverseLabel table L p f := by
  unfold nativeLinearCachedRun nativeCachedRun
  simp only [nativeLinearGatePacketOracle_eq,nativeLinearCachedPacketOracle_eq]

theorem nativeLinearCachedRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (nativeLinearCachedRun entry inverseLabel table L p f).program.word=
      numericalPairWord (fun i => nativePacketDataOracle (entry i)) inverseLabel table
        (Nat.clog 2 (p+1)) (nativePacketDataOracle f) := by
  rw [nativeLinearCachedRun_eq]
  exact nativeCachedRun_word entry inverseLabel table L p hL f

theorem nativeLinearCachedRun_length {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (nativeLinearCachedRun entry inverseLabel table L p f).program.word.length≤32*L*(p+1)^5 := by
  rw [nativeLinearCachedRun_eq]
  exact nativeCachedRun_length entry inverseLabel table L p hL f

theorem nativeLinearCachedRun_error {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (G : Fin m → SU2) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (f : NativePacketDataOracle) (U : SU2) (hf : QApproximates (nativePacketDataOracle f) U) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
      (nativeLinearCachedRun entry inverseLabel table L p f).program.word))≤(1/2:ℝ)^p := by
  rw [nativeLinearCachedRun_eq]
  exact nativeCachedRun_error entry G he inverseLabel hi table L p hL hcover f U hf

/-- This transfers only the numerical evaluation/decision charge. The
explicit cache-list access charge is a separate per-query trace; total AST
construction/request accumulation is not silently absorbed into this bound. -/
theorem nativeLinearCachedRun_numericalBooleanActions_degree338 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (entry i r).decode (A*(p+1)^9))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (f r).decode (A*(p+1)^9)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (nativeLinearCachedRun entry inverseLabel table L p f).program.booleanActions≤
      40000*(40*C+4)^2*(20*O)*(p+1)^338 := by
  rw [nativeLinearCachedRun_eq]
  exact nativeCachedRun_booleanActions_degree338 entry inverseLabel table L p A hL f he hf

end CircuitRecursion
