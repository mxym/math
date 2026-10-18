import CircuitNumerical.ExpressionCosts

namespace CircuitRecursion

/-- The same eager cache as `cachedNumericalRun`, followed by the finite
expression word program. Original provider calls occur only in cache creation. -/
def cachedArithmeticRun {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : QuaternionOracle) : ArithmeticWordResult m :=
  let P := numericalDemand L (Nat.clog 2 (p+1))
  let gates := List.Vector.ofFn (fun i : Fin m => buildPacketCache (entry i) P)
  let targetCache := buildPacketCache target P
  tracedPairWord (fun i q => .literal (readPacketCache (gates.get i).1 q)) inverseLabel table
    (Nat.clog 2 (p+1)) (fun q => .literal (readPacketCache targetCache.1 q))

theorem cachedArithmeticRun_word {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    (cachedArithmeticRun entry inverseLabel table L p f).word=
      (cachedNumericalRun entry inverseLabel table L p f).word := by
  exact tracedPairWord_word _ inverseLabel table _ _

theorem cachedArithmeticRun_operations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : QuaternionOracle) :
    (cachedArithmeticRun entry inverseLabel table L p f).operations≤
      (1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64 := by
  have h := tracedPairWord_literal_operations
    (fun i => readPacketCache (buildPacketCache (entry i) (numericalDemand L (Nat.clog 2 (p+1)))).1)
    inverseLabel table L (Nat.clog 2 (p+1)) hL
    (readPacketCache (buildPacketCache f (numericalDemand L (Nat.clog 2 (p+1)))).1)
  have he : (cachedArithmeticRun entry inverseLabel table L p f).operations≤
      1001*(n+1)*(L+1)*offsetGrowth^Nat.clog 2 (p+1) := by
    simpa only [cachedArithmeticRun,List.Vector.get_ofFn] using h
  have hp := Nat.mul_le_mul_left (1001*(n+1)*(L+1)) (offsetGrowth_precision_bound p)
  exact he.trans (by simpa only [Nat.mul_assoc] using hp)

theorem cachedArithmeticRun_executedOperations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : QuaternionOracle) :
    (cachedArithmeticRun entry inverseLabel table L p f).executedOperations≤
      (1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64 :=
  (ArithmeticWordResult.executedOperations_le _).trans
    (cachedArithmeticRun_operations entry inverseLabel table L p hL f)

/-- A finite numerical oracle algorithm with an internal arithmetic-expression
count. No bit-cost conclusion is made: its listed arithmetic primitives and
input providers still require machine implementations and operand-size bounds. -/
theorem cachedArithmeticSU2Synthesis {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → QuaternionOracle), (∀ i,QApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ (p : ℕ) (U : SU2) (f : QuaternionOracle),QApproximates f U →
        (cachedArithmeticRun entry inverseLabel table L p f).word.length≤32*L*(p+1)^5 ∧
        unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
          (cachedArithmeticRun entry inverseLabel table L p f).word))≤(1/2:ℝ)^p ∧
        (cachedArithmeticRun entry inverseLabel table L p f).operations≤
          (1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64 := by
  obtain ⟨L,n,table,hL,hcover⟩ := precomputedNet_exists G hinv huniversal
  refine ⟨L,n,table,fun entry he inverseLabel hi p U f hf => ?_⟩
  have hw : (cachedArithmeticRun entry inverseLabel table L p f).word=
      numericalPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f :=
    (cachedArithmeticRun_word entry inverseLabel table L p f).trans
      (cachedNumericalRun_word entry inverseLabel table L p hL f)
  refine ⟨?_,?_,cachedArithmeticRun_operations entry inverseLabel table L p hL f⟩
  · rw [hw]
    have ht := numericalPairWord_length entry inverseLabel table L hL (Nat.clog 2 (p+1)) f
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · rw [hw]
    have ht := numericalPairWord_error entry G he inverseLabel hi table hcover (Nat.clog 2 (p+1)) U f hf
    have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision _ p hp)

end CircuitRecursion
