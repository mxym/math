import CircuitRecursion.NumericalCorrection

open scoped Matrix.Norms.L2Operator
namespace CircuitRecursion

theorem numerical_stop_budget (ε σ : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (hσ : σ≤ε^2) :
    2*σ≤6*ε*Real.sqrt ε := by
  have hs : ε≤Real.sqrt ε := by nlinarith [Real.sq_sqrt hε,Real.sqrt_nonneg ε]
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hs)]

theorem numericalDoubleCorrection_error {m : ℕ} (entry : Fin m → QuaternionOracle)
    (G : Fin m → SU2) (hentry : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (approx : QuaternionOracle → List (Fin m)) (ε : ℝ) (hε : 0≤ε) (hεsmall : ε≤1/288)
    (heach : ∀ (U : SU2) (f : QuaternionOracle),QApproximates f U →
      unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G (approx f)))≤ε)
    (t : ℕ) (hσ : (1/2:ℝ)^t≤ε^4)
    (U : SU2) (f : QuaternionOracle) (hf : QApproximates f U) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
      (numericalCorrection entry inverseLabel (numericalCorrection entry inverseLabel approx t) t f)))≤144*ε^2 := by
  have hε1 : ε≤1 := by linarith
  have hs : Real.sqrt ε≤1 := by nlinarith [Real.sq_sqrt hε,Real.sqrt_nonneg ε]
  have he2 : ε^2≤1 := by nlinarith
  have he4 : ε^4≤ε^2 := by nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr he2)]
  have hstop := numerical_stop_budget ε ((1/2:ℝ)^t) hε hε1 (hσ.trans he4)
  let η := 6*ε*Real.sqrt ε
  have hη0 : 0≤η := by dsimp [η]; positivity
  have hη : η≤6*ε := by dsimp [η]; nlinarith [Real.sqrt_nonneg ε]
  have hη1 : η≤1 := by linarith
  have hη2 : η^2=36*ε^3 := by
    dsimp [η]
    rw [mul_pow,mul_pow,Real.sq_sqrt hε]
    ring
  have he43 : ε^4≤ε^3 := by nlinarith [mul_nonneg (by positivity : 0≤ε^3) (sub_nonneg.mpr hε1)]
  have hση : (1/2:ℝ)^t≤η^2 := by
    rw [hη2]
    nlinarith [show 0≤ε^3 by positivity]
  have hstopη := numerical_stop_budget η ((1/2:ℝ)^t) hη0 hη1 hση
  have hfirst := numericalCorrection_error entry G hentry inverseLabel hi approx ε hε hε1 heach t hstop
  have hsecond := numericalCorrection_error entry G hentry inverseLabel hi
    (numericalCorrection entry inverseLabel approx t) η hη0 hη1 hfirst t hstopη U f hf
  apply hsecond.trans
  have hroot : Real.sqrt η≤4*Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε,Real.sq_sqrt hη0,Real.sqrt_nonneg ε,Real.sqrt_nonneg η]
  calc
    6*η*Real.sqrt η≤6*(6*ε*Real.sqrt ε)*(4*Real.sqrt ε) := by gcongr
    _=144*ε*(Real.sqrt ε)^2 := by ring
    _=144*ε^2 := by rw [Real.sq_sqrt hε]; ring

def numericalThreshold (n : ℕ) : ℕ := 4*2^n+40

theorem numericalThreshold_error (n : ℕ) :
    (1/2:ℝ)^numericalThreshold n≤(skPairError n)^4 := by
  have hp : ((1/2:ℝ)^(2^n))^4=(1/2:ℝ)^(4*2^n) := by
    rw [← pow_mul,Nat.mul_comm]
  have hc : (1/2:ℝ)^40≤(1/144:ℝ)^4 := by norm_num
  simp only [numericalThreshold,skPairError,pow_add,mul_pow,hp]
  have h := mul_le_mul_of_nonneg_left hc
    (pow_nonneg (by norm_num : (0:ℝ)≤1/2) (4*2^n))
  simpa only [mul_comm] using h

theorem numericalThreshold_depth_bound (p : ℕ) :
    numericalThreshold (Nat.clog 2 (p+1))≤8*(p+1)+40 := by
  have h := pow_clog_two_le (p+1) (by omega)
  unfold numericalThreshold
  omega

/-- The full finite word recursion has no exact-real target input, no
classical choice and no unimplemented commutator primitive. -/
def numericalPairWord {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → QuaternionOracle → List (Fin m)
  | 0 => fixedNetWord entry table
  | k+1 => numericalCorrection entry inverseLabel
      (numericalCorrection entry inverseLabel (numericalPairWord entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem numericalPairWord_error {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (G : Fin m → SU2) (hentry : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m))
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k : ℕ) (U : SU2) (f : QuaternionOracle) (hf : QApproximates f U) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (numericalPairWord entry inverseLabel table k f)))≤skPairError k := by
  induction k generalizing U f with
  | zero =>
    simpa only [numericalPairWord,skPairError_zero] using fixedNetWord_correct entry G hentry table hcover f U hf
  | succ k ih =>
    rw [numericalPairWord,skPairError_succ]
    exact numericalDoubleCorrection_error entry G hentry inverseLabel hi _ (skPairError k)
      (skPairError_nonneg k) (skPairError_small k) ih (numericalThreshold k)
      (numericalThreshold_error k) U f hf

theorem numericalPairWord_length {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L : ℕ) (hL : ∀ j,(table j).length≤L) (k : ℕ) (f : QuaternionOracle) :
    (numericalPairWord entry inverseLabel table k f).length≤L*25^k := by
  induction k generalizing f with
  | zero => simpa only [numericalPairWord,pow_zero,mul_one] using fixedNetWord_length entry table L hL f
  | succ k ih =>
    have hfirst := numericalCorrection_length entry inverseLabel (numericalPairWord entry inverseLabel table k)
      (L*25^k) (numericalThreshold k) ih
    have hsecond := numericalCorrection_length entry inverseLabel
      (numericalCorrection entry inverseLabel (numericalPairWord entry inverseLabel table k) (numericalThreshold k))
      (5*(L*25^k)) (numericalThreshold k) hfirst f
    change _≤L*25^(k+1)
    exact hsecond.trans_eq (by rw [pow_succ]; ring)

/-- Oracle-model numerical synthesis. The fixed finite table is derived
internally. Every online input is a finite packet oracle and inverse-label
table; the word is the explicit program above. This theorem proves actual
error and length, not Turing bit complexity. -/
theorem numericalSU2Synthesis {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (C n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → QuaternionOracle), (∀ i,QApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ (p : ℕ) (U : SU2) (f : QuaternionOracle),QApproximates f U →
        (numericalPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).length≤C*(p+1)^5 ∧
        unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
          (numericalPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f)))≤(1/2:ℝ)^p := by
  obtain ⟨L,n,table,hL,hcover⟩ := precomputedNet_exists G hinv huniversal
  refine ⟨32*L,n,table,fun entry he inverseLabel hi p U f hf => ⟨?_,?_⟩⟩
  · have ht := numericalPairWord_length entry inverseLabel table L hL (Nat.clog 2 (p+1)) f
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · have ht := numericalPairWord_error entry G he inverseLabel hi table hcover (Nat.clog 2 (p+1)) U f hf
    have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision _ p hp)

theorem numericalSU2Synthesis_dyadic {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (C n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → DyadicQuaternionOracle), (∀ i,DyadicQApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ (p : ℕ) (U : SU2) (f : DyadicQuaternionOracle),DyadicQApproximates f U →
        (numericalPairWord (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table
          (Nat.clog 2 (p+1)) (dyadicQuaternionOracle f)).length≤C*(p+1)^5 ∧
        unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
          (numericalPairWord (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table
            (Nat.clog 2 (p+1)) (dyadicQuaternionOracle f))))≤(1/2:ℝ)^p := by
  obtain ⟨C,n,table,h⟩ := numericalSU2Synthesis G hinv huniversal
  exact ⟨C,n,table,fun entry he inverseLabel hi p U f hf =>
    h (fun i => dyadicQuaternionOracle (entry i)) he inverseLabel hi p U (dyadicQuaternionOracle f) hf⟩

end CircuitRecursion
