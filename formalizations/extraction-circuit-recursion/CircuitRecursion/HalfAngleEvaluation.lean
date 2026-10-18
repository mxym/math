import CircuitRecursion.OracleSqrt

open CircuitCompletion
namespace CircuitRecursion

def oracleConst (q : ℚ) : RationalOracle := fun _ => q

theorem oracleConst_correct (q : ℚ) : Approximates (oracleConst q) (q:ℝ) := by
  intro p
  simp only [oracleConst,sub_self,abs_zero]
  positivity

def oracleMeanPlus (f : RationalOracle) (p : ℕ) : ℚ := (1+f p)/2

def oracleMeanMinus (f : RationalOracle) (p : ℕ) : ℚ := (1-f p)/2

theorem oracleMeanPlus_correct (f : RationalOracle) (x : ℝ) (hf : Approximates f x) :
    Approximates (oracleMeanPlus f) ((1+x)/2) := by
  intro p
  have he := hf p
  have hid : ((oracleMeanPlus f p:ℚ):ℝ)-(1+x)/2=((f p:ℝ)-x)/2 := by
    simp [oracleMeanPlus]
    ring
  rw [hid,abs_div]
  norm_num
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) p]

theorem oracleMeanMinus_correct (f : RationalOracle) (x : ℝ) (hf : Approximates f x) :
    Approximates (oracleMeanMinus f) ((1-x)/2) := by
  intro p
  have he := hf p
  have hid : ((oracleMeanMinus f p:ℚ):ℝ)-(1-x)/2=-((f p:ℝ)-x)/2 := by
    simp [oracleMeanMinus]
    ring
  rw [hid,abs_div,abs_neg]
  norm_num
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) p]

def halfCosOracle : ℕ → RationalOracle → RationalOracle
  | 0,f => f
  | n+1,f => oracleSqrt (oracleMeanPlus (halfCosOracle n f))

theorem halfCosOracle_correct (f : RationalOracle) (θ : ℝ)
    (hf : Approximates f (Real.cos θ)) (hθ0 : 0≤θ) (hθπ : θ≤Real.pi) (n : ℕ) :
    Approximates (halfCosOracle n f) (Real.cos (θ/(2:ℝ)^n)) := by
  induction n with
  | zero => simpa only [halfCosOracle,pow_zero,div_one] using hf
  | succ n ih =>
    have hD : (0:ℝ)<2^n := by positivity
    have hD1 : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
    have h0 : 0≤θ/(2:ℝ)^n := by positivity
    have hπ : θ/(2:ℝ)^n≤Real.pi := by
      apply (div_le_iff₀ hD).mpr
      nlinarith [Real.pi_pos]
    rw [pow_succ,div_mul_eq_div_div,Real.cos_half (by linarith [Real.pi_pos]) hπ]
    exact oracleSqrt_correct _ _ (oracleMeanPlus_correct _ _ ih)
      (by linarith [Real.neg_one_le_cos (θ/(2:ℝ)^n)])

theorem mergeAngle_bounds (a b : ℝ) :
    0≤mergeAngle a b ∧ mergeAngle a b≤Real.pi/2 := by
  unfold mergeAngle
  split_ifs
  · constructor
    · exact le_refl _
    · positivity
  · constructor
    · apply Complex.arg_nonneg_iff.mpr
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
      positivity
    · apply Complex.arg_le_pi_div_two_iff.mpr
      left
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      positivity

def mergeCosOracle (A B : ℕ) : RationalOracle :=
  oracleSqrt (oracleConst ((A:ℚ)/(A+B)))

def mergeSinOracle (A B : ℕ) : RationalOracle :=
  oracleSqrt (oracleConst ((B:ℚ)/(A+B)))

theorem mergeCosOracle_correct (A B j : ℕ) (hj : 0<j) (hAB : 0<A+B) :
    Approximates (mergeCosOracle A B) (Real.cos (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j))) := by
  rw [(rational_mergeAngle_trig A B j hj hAB).1]
  exact oracleSqrt_correct _ _ (by simpa using oracleConst_correct ((A:ℚ)/(A+B)))
    (by positivity)

theorem mergeSinOracle_correct (A B j : ℕ) (hj : 0<j) (hAB : 0<A+B) :
    Approximates (mergeSinOracle A B) (Real.sin (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j))) := by
  rw [(rational_mergeAngle_trig A B j hj hAB).2]
  exact oracleSqrt_correct _ _ (by simpa using oracleConst_correct ((B:ℚ)/(A+B)))
    (by positivity)

theorem halvedMergeCosOracle_correct (A B j n : ℕ) (hj : 0<j) (hAB : 0<A+B) :
    Approximates (halfCosOracle n (mergeCosOracle A B))
      (Real.cos (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)/(2:ℝ)^n)) := by
  have hb := mergeAngle_bounds ((A:ℝ)/j) ((B:ℝ)/j)
  exact halfCosOracle_correct _ _ (mergeCosOracle_correct A B j hj hAB) hb.1
    (by linarith [Real.pi_pos]) n

def halfSinOracle (n : ℕ) (f g : RationalOracle) : RationalOracle :=
  match n with
  | 0 => g
  | n+1 => oracleSqrt (oracleMeanMinus (halfCosOracle n f))

theorem halfSinOracle_correct (f g : RationalOracle) (θ : ℝ)
    (hf : Approximates f (Real.cos θ)) (hg : Approximates g (Real.sin θ))
    (hθ0 : 0≤θ) (hθπ : θ≤Real.pi) (n : ℕ) :
    Approximates (halfSinOracle n f g) (Real.sin (θ/(2:ℝ)^n)) := by
  cases n with
  | zero => simpa only [halfSinOracle,pow_zero,div_one] using hg
  | succ n =>
    have hD : (0:ℝ)<2^n := by positivity
    have hD1 : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
    have h0 : 0≤θ/(2:ℝ)^n := by positivity
    have hπ : θ/(2:ℝ)^n≤2*Real.pi := by
      apply (div_le_iff₀ hD).mpr
      nlinarith [Real.pi_pos]
    rw [pow_succ,div_mul_eq_div_div,Real.sin_half_eq_sqrt h0 hπ]
    exact oracleSqrt_correct _ _
      (oracleMeanMinus_correct _ _ (halfCosOracle_correct f θ hf hθ0 hθπ n))
      (by linarith [Real.cos_le_one (θ/(2:ℝ)^n)])

theorem halvedMergeSinOracle_correct (A B j n : ℕ) (hj : 0<j) (hAB : 0<A+B) :
    Approximates (halfSinOracle n (mergeCosOracle A B) (mergeSinOracle A B))
      (Real.sin (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)/(2:ℝ)^n)) := by
  have hb := mergeAngle_bounds ((A:ℝ)/j) ((B:ℝ)/j)
  exact halfSinOracle_correct _ _ _ (mergeCosOracle_correct A B j hj hAB)
    (mergeSinOracle_correct A B j hj hAB) hb.1 (by linarith [Real.pi_pos]) n

/-- A syntax-level arithmetic program. `root` is precisely the finite
Nat.sqrt/floor routine above; it is not an assumed square-root oracle. -/
inductive ScalarProgram where
  | literal : ℚ → ScalarProgram
  | query : ℕ → ScalarProgram
  | add : ScalarProgram → ScalarProgram → ScalarProgram
  | sub : ScalarProgram → ScalarProgram → ScalarProgram
  | mul : ScalarProgram → ScalarProgram → ScalarProgram
  | root : ℕ → ScalarProgram → ScalarProgram

def ScalarProgram.eval (f : RationalOracle) : ScalarProgram → ℚ
  | .literal q => q
  | .query p => f p
  | .add a b => a.eval f+b.eval f
  | .sub a b => a.eval f-b.eval f
  | .mul a b => a.eval f*b.eval f
  | .root p a => rationalSqrtApprox (max 0 (a.eval f)) p

def ScalarProgram.queries : ScalarProgram → List ℕ
  | .literal _ => []
  | .query p => [p]
  | .add a b | .sub a b | .mul a b => a.queries++b.queries
  | .root _ a => a.queries

def ScalarProgram.sqrtCalls : ScalarProgram → ℕ
  | .literal _ | .query _ => 0
  | .add a b | .sub a b | .mul a b => a.sqrtCalls+b.sqrtCalls
  | .root _ a => a.sqrtCalls+1

def ScalarProgram.rationalCalls : ScalarProgram → ℕ
  | .literal _ | .query _ => 0
  | .add a b | .sub a b | .mul a b => a.rationalCalls+b.rationalCalls+1
  | .root _ a => a.rationalCalls

def halfCosProgram : ℕ → ℕ → ScalarProgram
  | 0,p => .query p
  | n+1,p => .root (p+1) (.mul (.literal (1/2))
      (.add (.literal 1) (halfCosProgram n (2*p+2))))

def halfAngleDemand : ℕ → ℕ → ℕ
  | 0,p => p
  | n+1,p => halfAngleDemand n (2*p+2)

theorem halfCosProgram_eval (f : RationalOracle) (n p : ℕ) :
    (halfCosProgram n p).eval f=halfCosOracle n f p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [halfCosProgram,ScalarProgram.eval,halfCosOracle,oracleSqrt,oracleMeanPlus,ih]
    congr 2
    ring

theorem halfCosProgram_queries (n p : ℕ) :
    (halfCosProgram n p).queries=[halfAngleDemand n p] := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simpa only [halfCosProgram,ScalarProgram.queries,List.nil_append,halfAngleDemand] using ih (2*p+2)

theorem halfCosProgram_calls (n p : ℕ) :
    (halfCosProgram n p).sqrtCalls=n ∧ (halfCosProgram n p).rationalCalls=2*n := by
  induction n generalizing p with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h := ih (2*p+2)
    simp only [halfCosProgram,ScalarProgram.sqrtCalls,ScalarProgram.rationalCalls,
      zero_add,h.1,h.2]
    exact ⟨trivial,by omega⟩

theorem halfAngleDemand_exact (n p : ℕ) : halfAngleDemand n p+2=2^n*(p+2) := by
  induction n generalizing p with
  | zero => simp only [halfAngleDemand,pow_zero,one_mul]
  | succ n ih =>
    rw [halfAngleDemand,ih,pow_succ]
    ring

/-- The precision amplification of all active-register halvings remains
polynomial in the copy count and requested output precision. -/
theorem active_halfAngleDemand_bound (k p : ℕ) :
    halfAngleDemand (activeWires k) p+2≤16*(k+3)^3*(p+2) := by
  rw [halfAngleDemand_exact]
  exact Nat.mul_le_mul_right _ (activeDimension_polynomial k)

def mergeCosProgram (A B : ℕ) : ℕ → ℕ → ScalarProgram
  | 0,p => .root (p+1) (.literal ((A:ℚ)/(A+B)))
  | n+1,p => .root (p+1) (.mul (.literal (1/2))
      (.add (.literal 1) (mergeCosProgram A B n (2*p+2))))

def mergeSinProgram (A B : ℕ) : ℕ → ℕ → ScalarProgram
  | 0,p => .root (p+1) (.literal ((B:ℚ)/(A+B)))
  | n+1,p => .root (p+1) (.mul (.literal (1/2))
      (.sub (.literal 1) (mergeCosProgram A B n (2*p+2))))

theorem mergeCosProgram_eval (A B n p : ℕ) (f : RationalOracle) :
    (mergeCosProgram A B n p).eval f=halfCosOracle n (mergeCosOracle A B) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [mergeCosProgram,ScalarProgram.eval,halfCosOracle,oracleSqrt,oracleMeanPlus,ih]
    congr 2
    ring

theorem mergeSinProgram_eval (A B n p : ℕ) (f : RationalOracle) :
    (mergeSinProgram A B n p).eval f=
      halfSinOracle n (mergeCosOracle A B) (mergeSinOracle A B) p := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [mergeSinProgram,ScalarProgram.eval,halfSinOracle,oracleSqrt,oracleMeanMinus,
      mergeCosProgram_eval]
    congr 2
    ring

theorem mergeCosProgram_resources (A B n p : ℕ) :
    (mergeCosProgram A B n p).queries=[] ∧
    (mergeCosProgram A B n p).sqrtCalls=n+1 ∧
    (mergeCosProgram A B n p).rationalCalls=2*n := by
  induction n generalizing p with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    have h := ih (2*p+2)
    simp only [mergeCosProgram,ScalarProgram.queries,ScalarProgram.sqrtCalls,
      ScalarProgram.rationalCalls,List.nil_append,zero_add,h.1,h.2.1,h.2.2]
    exact ⟨trivial,trivial,by omega⟩

theorem mergeSinProgram_resources (A B n p : ℕ) :
    (mergeSinProgram A B n p).queries=[] ∧
    (mergeSinProgram A B n p).sqrtCalls=n+1 ∧
    (mergeSinProgram A B n p).rationalCalls=2*n := by
  cases n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n =>
    have h := mergeCosProgram_resources A B n (2*p+2)
    simp only [mergeSinProgram,ScalarProgram.queries,ScalarProgram.sqrtCalls,
      ScalarProgram.rationalCalls,List.nil_append,zero_add,h.1,h.2.1,h.2.2]
    exact ⟨trivial,trivial,by omega⟩

def ScalarProgram.maxRootPrecision : ScalarProgram → ℕ
  | .literal _ | .query _ => 0
  | .add a b | .sub a b | .mul a b => max a.maxRootPrecision b.maxRootPrecision
  | .root p a => max p a.maxRootPrecision

theorem halfAngleDemand_ge (n p : ℕ) : p≤halfAngleDemand n p := by
  induction n generalizing p with
  | zero => exact le_refl _
  | succ n ih => exact (by omega : p≤2*p+2).trans (ih (2*p+2))

theorem mergeCosProgram_precision (A B n p : ℕ) :
    (mergeCosProgram A B n p).maxRootPrecision≤halfAngleDemand n p+1 := by
  induction n generalizing p with
  | zero => simp [mergeCosProgram,ScalarProgram.maxRootPrecision,halfAngleDemand]
  | succ n ih =>
    simp only [mergeCosProgram,ScalarProgram.maxRootPrecision,zero_le, max_eq_right,
      halfAngleDemand]
    apply max_le
    · have h := halfAngleDemand_ge n (2*p+2); omega
    · exact ih _

theorem mergeSinProgram_precision (A B n p : ℕ) :
    (mergeSinProgram A B n p).maxRootPrecision≤halfAngleDemand n p+1 := by
  cases n with
  | zero => simp [mergeSinProgram,ScalarProgram.maxRootPrecision,halfAngleDemand]
  | succ n =>
    simp only [mergeSinProgram,ScalarProgram.maxRootPrecision,zero_le,max_eq_right,
      halfAngleDemand]
    apply max_le
    · have h := halfAngleDemand_ge n (2*p+2); omega
    · exact mergeCosProgram_precision A B n _

theorem mergePhaseProgram_correct (A B j n p : ℕ) (hj : 0<j) (hAB : 0<A+B)
    (f : RationalOracle) :
    |(((mergeCosProgram A B n p).eval f:ℚ):ℝ)-
      Real.cos (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)/(2:ℝ)^n)|≤(1/2:ℝ)^p ∧
    |(((mergeSinProgram A B n p).eval f:ℚ):ℝ)-
      Real.sin (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)/(2:ℝ)^n)|≤(1/2:ℝ)^p := by
  rw [mergeCosProgram_eval,mergeSinProgram_eval]
  exact ⟨halvedMergeCosOracle_correct A B j n hj hAB p,
    halvedMergeSinOracle_correct A B j n hj hAB p⟩

theorem mergeCosProgram_range (A B n p : ℕ) (f : RationalOracle) :
    0≤(mergeCosProgram A B n p).eval f ∧ (mergeCosProgram A B n p).eval f≤1 := by
  induction n generalizing p with
  | zero =>
    apply rationalSqrtApprox_range
    apply max_le (by norm_num)
    exact div_le_one_of_le₀ (le_add_of_nonneg_right (by positivity)) (by positivity)
  | succ n ih =>
    apply rationalSqrtApprox_range
    apply max_le (by norm_num)
    have h := ih (2*p+2)
    change (1/2:ℚ)*(1+(mergeCosProgram A B n (2*p+2)).eval f)≤1
    linarith

theorem mergeCosProgram_dyadic (A B n p : ℕ) (f : RationalOracle) :
    ∃ s : ℕ,s≤2^(p+1) ∧ (mergeCosProgram A B n p).eval f=(s:ℚ)/(2:ℚ)^(p+1) := by
  cases n with
  | zero =>
    apply rationalSqrtApprox_dyadic
    apply max_le (by norm_num)
    exact div_le_one_of_le₀ (le_add_of_nonneg_right (by positivity)) (by positivity)
  | succ n =>
    apply rationalSqrtApprox_dyadic
    apply max_le (by norm_num)
    have h := mergeCosProgram_range A B n (2*p+2) f
    change (1/2:ℚ)*(1+(mergeCosProgram A B n (2*p+2)).eval f)≤1
    linarith

theorem mergeSinProgram_dyadic (A B n p : ℕ) (f : RationalOracle) :
    ∃ s : ℕ,s≤2^(p+1) ∧ (mergeSinProgram A B n p).eval f=(s:ℚ)/(2:ℚ)^(p+1) := by
  cases n with
  | zero =>
    apply rationalSqrtApprox_dyadic
    apply max_le (by norm_num)
    exact div_le_one_of_le₀ (le_add_of_nonneg_left (by positivity)) (by positivity)
  | succ n =>
    apply rationalSqrtApprox_dyadic
    apply max_le (by norm_num)
    have h := mergeCosProgram_range A B n (2*p+2) f
    change (1/2:ℚ)*(1-(mergeCosProgram A B n (2*p+2)).eval f)≤1
    linarith

theorem active_mergePhaseProgram_resources (A B k p : ℕ) :
    (mergeCosProgram A B (activeWires k) p).sqrtCalls≤6*Nat.clog 2 (k+3)+3 ∧
    (mergeSinProgram A B (activeWires k) p).sqrtCalls≤6*Nat.clog 2 (k+3)+3 ∧
    (mergeCosProgram A B (activeWires k) p).maxRootPrecision≤16*(k+3)^3*(p+2) ∧
    (mergeSinProgram A B (activeWires k) p).maxRootPrecision≤16*(k+3)^3*(p+2) := by
  have hc := mergeCosProgram_resources A B (activeWires k) p
  have hs := mergeSinProgram_resources A B (activeWires k) p
  have hw := activeWires_log_bound k
  have hp := active_halfAngleDemand_bound k p
  refine ⟨?_,?_,?_,?_⟩
  · rw [hc.2.1]; omega
  · rw [hs.2.1]; omega
  · exact (mergeCosProgram_precision A B (activeWires k) p).trans (by omega)
  · exact (mergeSinProgram_precision A B (activeWires k) p).trans (by omega)

end CircuitRecursion
