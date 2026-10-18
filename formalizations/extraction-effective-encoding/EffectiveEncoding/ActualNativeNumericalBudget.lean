import EffectiveEncoding.FullyNativeExtraction
import CircuitNumerical.NativeSynthesisPolynomial

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- One explicit common height coefficient for native gate input data and the
internally computed actual target. Polynomial degree seven in k. -/
def nativeTargetInputCoefficient (k L gateB : ℕ) : ℕ :=
  (gateB+1000000*(51200000*(L+1)+5))*(k+3)^7


theorem nativeTargetInputCoefficient_gate (k L gateB : ℕ) : gateB≤nativeTargetInputCoefficient k L gateB := by
  have hp : 1≤(k+3)^7 := Nat.one_le_pow _ _ (by omega)
  calc
    _≤gateB+1000000*(51200000*(L+1)+5) := Nat.le_add_right _ _
    _≤(gateB+1000000*(51200000*(L+1)+5))*(k+3)^7 := by nlinarith


theorem nativeTargetInputCoefficient_target (k L gateB : ℕ) :
    actualNativeTargetHeightCoefficient k L≤nativeTargetInputCoefficient k L gateB := by
  unfold actualNativeTargetHeightCoefficient nativeTargetInputCoefficient
  nlinarith [Nat.zero_le (gateB*(k+3)^7)]


def actualNativeBooleanCoefficient (n L k gateB : ℕ) : ℕ :=
  let C:=1000000000002*(n+1)*(8*nativeTargetInputCoefficient k L gateB+10)*(L+1)*traceRGrowth
  let O:=1020*(n+1)*(2*L+1)*offsetGrowth
  40000*(40*C+4)^2*(20*O)

/-- The actual native target is closed internally. The only supplied data bound
is on finitely queried library Word packets, not a runtime/final budget premise. -/
theorem nativeTargetDescriptorRun_booleanActions_actual {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (q+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(q+1)^9)) :
    (nativeTargetDescriptorRun entry inverseLabel table L q u).cached.program.booleanActions≤
      actualNativeBooleanCoefficient n L k gateB*(q+1)^338 := by
  apply nativeCachedRun_booleanActions_degree338 entry inverseLabel table L q
    (nativeTargetInputCoefficient k L gateB) hL (prepareNativeSingleInput u).packetDataOracle
  · intro i r hr
    exact IntegerPacketHeight.mono _ _ _ (he i r hr)
      (Nat.mul_le_mul_right _ (nativeTargetInputCoefficient_gate k L gateB))
  · intro r hr
    exact IntegerPacketHeight.mono _ _ _ (nativePreparedTarget_cache_height hu L q r hr)
      (Nat.mul_le_mul_right _ (nativeTargetInputCoefficient_target k L gateB))

/-- Projection only of the actual stored native numerical executions. It
charges no provider/adapter/cache/list/control/counter work by implication. -/
def NativeCompiledLabelRun.nativeActions {m wires L q : ℕ}
    (run : NativeCompiledLabelRun m wires L q) : ℕ :=
  (run.programs.map (fun r => r.cached.program.booleanActions)).sum


theorem compileNativeWord_nativeActions {m wires L q : ℕ}
    (synth : SingleCode → NativeTargetResult m L q) (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → (synth u).cached.program.booleanActions≤B) :
    (compileNativeWord synth xs).nativeActions≤xs.length*B := by
  induction xs with
  | nil => simp [compileNativeWord,NativeCompiledLabelRun.nativeActions]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    cases g with
    | single wire u =>
      have hg:=h wire u (by simp)
      simp only [compileNativeWord,compileNativeGate,NativeCompiledLabelRun.nativeActions,
        List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
        Nat.add_zero,List.length_cons] at *
      nlinarith
    | cnot c t hct =>
      simp only [compileNativeWord,compileNativeGate,NativeCompiledLabelRun.nativeActions,
        List.nil_append,List.length_cons] at *
      nlinarith


theorem fullyNativeExtractionRun_numericalActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).compilation.nativeActions≤
      actualGatePolynomial k*(actualNativeBooleanCoefficient n L k gateB*(logarithmicPrecision k p+1)^338) := by
  have hw : (preparedNativeDescriptorRun k).word=extractionCode k := by
    rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  let q:=dyadicCircuitPrecision (preparedNativeDescriptorRun k).word.length (p+1)
  have hq : q=extractionPrecision k p := by
    dsimp [q]
    rw [hw]
    rfl
  change (compileNativeWord (nativeTargetDescriptorRun entry inverseLabel table L q)
    (preparedNativeDescriptorRun k).word).nativeActions≤_
  have h:=compileNativeWord_nativeActions _ (preparedNativeDescriptorRun k).word
    (actualNativeBooleanCoefficient n L k gateB*(q+1)^338) (by
      intro wire u hu
      apply nativeTargetDescriptorRun_booleanActions_actual entry inverseLabel table L q gateB hL hu
      simpa only [hq] using he)
  apply h.trans
  apply Nat.mul_le_mul (by rw [hw]; exact extractionCode_length_polynomial k)
  rw [hq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 338)

end EffectiveEncoding
