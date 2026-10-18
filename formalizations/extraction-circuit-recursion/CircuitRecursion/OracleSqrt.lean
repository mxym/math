import CircuitRecursion.OracleArithmetic

namespace CircuitRecursion

/-- Rational square-root approximation using natural floor and the actual
integer square-root algorithm. No real comparison or square-root oracle is
called by this program. -/
def rationalSqrtApprox (q : ℚ) (p : ℕ) : ℚ :=
  (Nat.sqrt ⌊max 0 q*((2:ℚ)^p)^2⌋₊:ℚ)/(2:ℚ)^p

theorem rationalSqrtApprox_correct (q : ℚ) (hq : 0≤q) (p : ℕ) :
    |((rationalSqrtApprox q p:ℚ):ℝ)-Real.sqrt (q:ℝ)|≤(1/2:ℝ)^p := by
  let N := ⌊q*((2:ℚ)^p)^2⌋₊
  let s := Nat.sqrt N
  let D := (2:ℝ)^p
  have hD : 0<D := by positivity
  have hq' : (0:ℝ)≤q := by exact_mod_cast hq
  have hfloor : (N:ℝ)≤(q:ℝ)*D^2 := by
    have h : (N:ℚ)≤q*((2:ℚ)^p)^2 := Nat.floor_le (by positivity)
    have h' : ((N:ℚ):ℝ)≤((q*((2:ℚ)^p)^2:ℚ):ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using h'
  have hfloor' : (q:ℝ)*D^2<(N:ℝ)+1 := by
    have h : q*((2:ℚ)^p)^2<(N:ℚ)+1 := Nat.lt_floor_add_one _
    have h' : ((q*((2:ℚ)^p)^2:ℚ):ℝ)<(((N:ℚ)+1:ℚ):ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_one] using h'
  have hs : (s:ℝ)^2≤N := by exact_mod_cast Nat.sqrt_le' N
  have hs' : (N:ℝ)+1≤((s:ℝ)+1)^2 := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_succ_sqrt' N))
  have hr : Real.sqrt (q:ℝ)^2=(q:ℝ) := Real.sq_sqrt hq'
  have hprod : (Real.sqrt (q:ℝ)*D)^2=(q:ℝ)*D^2 := by rw [mul_pow,hr]
  have hprod0 : 0≤Real.sqrt (q:ℝ)*D := by positivity
  have hlo : (s:ℝ)≤Real.sqrt (q:ℝ)*D := by nlinarith
  have hhi : Real.sqrt (q:ℝ)*D≤(s:ℝ)+1 := by nlinarith
  have hlo' : (s:ℝ)/D≤Real.sqrt (q:ℝ) := (div_le_iff₀ hD).mpr hlo
  have hhi' : Real.sqrt (q:ℝ)≤(s:ℝ)/D+1/D := by
    rw [← add_div]
    exact (le_div_iff₀ hD).mpr hhi
  have heval : ((rationalSqrtApprox q p:ℚ):ℝ)=(s:ℝ)/D := by
    simp only [rationalSqrtApprox,max_eq_right hq,Rat.cast_div,Rat.cast_natCast,
      Rat.cast_pow,Rat.cast_ofNat]
    rfl
  have hprec : (1/2:ℝ)^p=1/D := by simp only [D,div_pow,one_pow]
  rw [heval,hprec]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sqrt_input_error (x y ε : ℝ) (hx : 0≤x) (hy : 0≤y) (hε : 0≤ε)
    (he : |x-y|≤ε^2) : |Real.sqrt x-Real.sqrt y|≤ε := by
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hx0 := Real.sqrt_nonneg x
  have hy0 := Real.sqrt_nonneg y
  have h := abs_le.mp he
  by_cases hxy : Real.sqrt y≤Real.sqrt x
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hxy)]
  · have hyx : Real.sqrt x≤Real.sqrt y := (lt_of_not_ge hxy).le
    rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hyx)]

def oracleSqrt (f : RationalOracle) (p : ℕ) : ℚ :=
  rationalSqrtApprox (max 0 (f (2*p+2))) (p+1)

theorem oracleSqrt_correct (f : RationalOracle) (x : ℝ)
    (hf : Approximates f x) (hx : 0≤x) :
    Approximates (oracleSqrt f) (Real.sqrt x) := by
  intro p
  let q := max 0 (f (2*p+2))
  let ε := (1/2:ℝ)^(p+1)
  have hq : (0:ℚ)≤q := le_max_left _ _
  have hq' : (0:ℝ)≤q := by exact_mod_cast hq
  have hinput : |(q:ℝ)-x|≤ε^2 := by
    have he := hf (2*p+2)
    have hp : (1/2:ℝ)^(2*p+2)=ε^2 := by
      dsimp [ε]
      rw [← pow_mul]
      congr 1
      omega
    rw [hp] at he
    dsimp [q]
    by_cases hf0 : 0≤f (2*p+2)
    · simpa only [max_eq_right hf0] using he
    · have hf0' : (f (2*p+2):ℝ)≤0 := by exact_mod_cast (lt_of_not_ge hf0).le
      rw [max_eq_left (lt_of_not_ge hf0).le,Rat.cast_zero,zero_sub,abs_neg,abs_of_nonneg hx]
      have he' := (abs_le.mp he).1
      linarith
  have hs := sqrt_input_error (q:ℝ) x ε hq' hx (by positivity) hinput
  have happrox := rationalSqrtApprox_correct q hq (p+1)
  have ht := abs_add_le (((rationalSqrtApprox q (p+1):ℚ):ℝ)-Real.sqrt (q:ℝ))
    (Real.sqrt (q:ℝ)-Real.sqrt x)
  rw [sub_add_sub_cancel] at ht
  change |((rationalSqrtApprox q (p+1):ℚ):ℝ)-Real.sqrt x|≤_
  have hε : 2*ε=(1/2:ℝ)^p := by dsimp [ε]; rw [pow_succ]; ring
  linarith

/-- Bounded inputs produce an explicit dyadic numerator of bounded size. -/
theorem rationalSqrtApprox_dyadic (q : ℚ) (hq : q≤1) (p : ℕ) :
    ∃ s : ℕ,s≤2^p ∧ rationalSqrtApprox q p=(s:ℚ)/(2:ℚ)^p := by
  let N := ⌊max 0 q*((2:ℚ)^p)^2⌋₊
  have hq' : max 0 q≤(1:ℚ) := max_le (by norm_num) hq
  have hN : N≤(2^p)^2 := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_left (by positivity) hq'
  have hs : Nat.sqrt N≤2^p := by
    have ht := Nat.sqrt_le_sqrt hN
    simpa only [Nat.sqrt_eq'] using ht
  exact ⟨Nat.sqrt N,hs,rfl⟩

theorem rationalSqrtApprox_range (q : ℚ) (hq : q≤1) (p : ℕ) :
    0≤rationalSqrtApprox q p ∧ rationalSqrtApprox q p≤1 := by
  obtain ⟨s,hs,he⟩ := rationalSqrtApprox_dyadic q hq p
  rw [he]
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0:ℚ)<2^p)).mpr
    exact_mod_cast hs

end CircuitRecursion
