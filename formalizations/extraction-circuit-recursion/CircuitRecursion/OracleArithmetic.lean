import CircuitRecursion.ConditionedConjugacy

namespace CircuitRecursion

/-- Finite-precision real input: query p returns a rational within 2^-p.
The semantic real is used only in the correctness predicate below. -/
abbrev RationalOracle := ℕ → ℚ

def Approximates (f : RationalOracle) (x : ℝ) : Prop :=
  ∀ p,|(f p:ℝ)-x|≤(1/2:ℝ)^p

def oracleAdd (f g : RationalOracle) (p : ℕ) : ℚ := f (p+1)+g (p+1)

def oracleNeg (f : RationalOracle) (p : ℕ) : ℚ := -f p

def oracleMul (b : ℕ) (f g : RationalOracle) (p : ℕ) : ℚ :=
  f (p+b+2)*g (p+b+2)

def oracleInv (b : ℕ) (f : RationalOracle) (p : ℕ) : ℚ :=
  (f (p+2*b+2))⁻¹

theorem oracleAdd_correct (f g : RationalOracle) (x y : ℝ)
    (hf : Approximates f x) (hg : Approximates g y) :
    Approximates (oracleAdd f g) (x+y) := by
  intro p
  have he := abs_add_le ((f (p+1):ℝ)-x) ((g (p+1):ℝ)-y)
  have h₁ := hf (p+1)
  have h₂ := hg (p+1)
  have ht : ((oracleAdd f g p:ℚ):ℝ)-(x+y)=
      ((f (p+1):ℝ)-x)+((g (p+1):ℝ)-y) := by simp [oracleAdd]; ring
  rw [ht]
  rw [pow_succ] at h₁ h₂
  linarith

theorem oracleNeg_correct (f : RationalOracle) (x : ℝ) (hf : Approximates f x) :
    Approximates (oracleNeg f) (-x) := by
  intro p
  simpa only [oracleNeg,Rat.cast_neg,neg_sub_neg,abs_sub_comm] using hf p

theorem dyadic_scale (p b : ℕ) :
    (2:ℝ)^b*(1/2:ℝ)^(p+b+2)=(1/2:ℝ)^p/4 := by
  calc
    _=((2:ℝ)^b*(1/2:ℝ)^b)*(1/2:ℝ)^p*(1/2:ℝ)^2 := by rw [pow_add,pow_add]; ring
    _=_ := by rw [← mul_pow]; norm_num; ring

theorem oracleMul_correct (b : ℕ) (f g : RationalOracle) (x y : ℝ)
    (hf : Approximates f x) (hg : Approximates g y)
    (hx : |x|≤(2:ℝ)^b) (hy : |y|≤(2:ℝ)^b) :
    Approximates (oracleMul b f g) (x*y) := by
  intro p
  let q := p+b+2
  let δ := (1/2:ℝ)^q
  let M := (2:ℝ)^b
  let a : ℝ := f q
  let c : ℝ := g q
  have hδ : 0≤δ := by positivity
  have hδ1 : δ≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hM : 1≤M := one_le_pow₀ (by norm_num)
  have hf' : |a-x|≤δ := hf q
  have hg' : |c-y|≤δ := hg q
  have ha : |a|≤M+δ := by
    have ht := abs_add_le (a-x) x
    rw [sub_add_cancel] at ht
    linarith
  have hid : a*c-x*y=a*(c-y)+y*(a-x) := by ring
  have he : |a*c-x*y|≤(M+δ)*δ+M*δ := by
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul ha hg' (abs_nonneg _) (by positivity))
      (mul_le_mul hy hf' (abs_nonneg _) (by positivity))
  have hscale : M*δ=(1/2:ℝ)^p/4 := dyadic_scale p b
  simp only [oracleMul,Rat.cast_mul]
  change |a*c-x*y|≤_
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1),mul_nonneg hδ (sub_nonneg.mpr hM)]

theorem oracleInv_correct (b : ℕ) (f : RationalOracle) (x : ℝ)
    (hf : Approximates f x) (hx : (1/2:ℝ)^b≤x) :
    Approximates (oracleInv b f) x⁻¹ := by
  intro p
  let L := (1/2:ℝ)^b
  let ε := (1/2:ℝ)^p
  let δ := (1/2:ℝ)^(p+2*b+2)
  let a : ℝ := f (p+2*b+2)
  have hL : 0<L := by positivity
  have hL1 : L≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hε : 0≤ε := by positivity
  have hε1 : ε≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδ : δ=ε*L^2/4 := by
    have ht : (1/2:ℝ)^(2*b)=L^2 := by
      dsimp [L]
      rw [← pow_mul]
      congr 1
      omega
    dsimp only [δ,ε]
    rw [pow_add,pow_add,ht]
    norm_num
    ring
  have hδL : δ≤L/2 := by
    have hh := mul_le_mul_of_nonneg_right hε1 (sq_nonneg L)
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hL1)]
  have he : |a-x|≤δ := hf _
  have ha : L/2≤a := by have he' := (abs_le.mp he).1; linarith
  have ha0 : 0<a := by linarith
  have hx0 : 0<x := hL.trans_le hx
  have hprod : L^2/2≤a*x := by
    have ht := mul_le_mul ha hx hL.le ha0.le
    nlinarith
  have hδprod : δ≤ε*(a*x) := by
    have ht := mul_le_mul_of_nonneg_left hprod hε
    nlinarith [mul_nonneg hε (sq_nonneg L)]
  have hid : a⁻¹-x⁻¹=(x-a)/(a*x) := by field_simp [ha0.ne',hx0.ne']
  simp only [oracleInv,Rat.cast_inv]
  change |a⁻¹-x⁻¹|≤ε
  rw [hid,abs_div,abs_of_pos (mul_pos ha0 hx0),abs_sub_comm]
  exact (div_le_iff₀ (mul_pos ha0 hx0)).mpr (he.trans hδprod)

end CircuitRecursion
