import CircuitRecursion.LocalDiscard
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

theorem bellPairYield_feasible (k : ℕ) :
    occupationRank k≤4^(k-bellPairYield k) := by
  have he : k-bellPairYield k=encodingPairs k := by
    have h := encodingPairs_le_copy k
    unfold bellPairYield
    omega
  rw [he]
  exact Nat.le_pow_clog (by decide) _

theorem bellPairYield_maximal (k h : ℕ) (hh : h≤k)
    (hr : occupationRank k≤4^(k-h)) : h≤bellPairYield k := by
  have hc : encodingPairs k≤k-h := Nat.clog_le_of_le_pow hr
  unfold bellPairYield
  omega

theorem bellPairYield_floor_log4 (k : ℕ) :
    (bellPairYield k : ℤ)=⌊(k : ℝ)-Real.logb 4 (occupationRank k : ℝ)⌋ := by
  have hl : 0≤Real.logb 4 (occupationRank k : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast occupationRank_pos k)
  have hc : (encodingPairs k : ℤ)=⌈Real.logb 4 (occupationRank k : ℝ)⌉ := by
    rw [← Int.natCast_ceil_eq_ceil hl]
    exact congrArg Int.ofNat (by
      simpa only [Nat.cast_ofNat,encodingPairs] using (Real.natCeil_logb_natCast 4 (occupationRank k)).symm)
  rw [sub_eq_add_neg,Int.floor_natCast_add,Int.floor_neg,← hc]
  unfold bellPairYield
  rw [Nat.cast_sub (encodingPairs_le_copy k)]
  ring

theorem log4_eq_half_log2 (x : ℝ) : Real.logb 4 x=(1/2 : ℝ)*Real.logb 2 x := by
  have hl : Real.log 2≠0 := (Real.log_pos (by norm_num)).ne'
  have he : Real.log 4=2*Real.log 2 := by
    have ht := Real.log_pow (2 : ℝ) 2
    norm_num at ht
    exact ht
  simp only [Real.logb,he]
  field_simp

/-- The exact integer yield in the manuscript's real-log/floor notation. -/
theorem bellPairYield_floor (k : ℕ) :
    (bellPairYield k : ℤ)=
      ⌊(k : ℝ)-(1/2 : ℝ)*Real.logb 2 (occupationRank k : ℝ)⌋ := by
  rw [← log4_eq_half_log2,bellPairYield_floor_log4]

/-- The existing fully physical cPPT converse excludes every larger integer
Bell-pair output, even for an arbitrary original-space global unitary. -/
theorem bellPairYield_cPPT_maximal (k h : ℕ) {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h)×Fin (2^h)) (Fin (2^k)×Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k)×Fin (2^k)) ℂ)
    (hexact : ∀ z : Fin 4 → ℂ,IsUnitVector z →
      1≤(Extraction.bellProjector (d := Fin (2^h))*Extraction.krausApply A
        ((U : Matrix (Fin (2^k)×Fin (2^k)) (Fin (2^k)×Fin (2^k)) ℂ)*
          SpectralProtocol.purePowerInput 2 2 k z*
          (U : Matrix (Fin (2^k)×Fin (2^k)) (Fin (2^k)×Fin (2^k)) ℂ)ᴴ)).trace.re) :
    h≤bellPairYield k := by
  have hb := SpectralProtocol.purePower_fidelity_guarantee_upper 2 2 k (2^h)
    (by decide) (by decide) (by positivity) A hcomplete hpt U 1 hexact
  have hs : 1≤Real.sqrt ((4 : ℝ)^k/((2^h : ℕ)^2*(occupationRank k : ℝ))) := by
    exact hb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnonneg : 0≤(4 : ℝ)^k/((2^h : ℕ)^2*(occupationRank k : ℝ)) := by positivity
  have hr : 1≤(4 : ℝ)^k/((2^h : ℕ)^2*(occupationRank k : ℝ)) := by
    nlinarith [Real.sq_sqrt hnonneg]
  have hpos : 0<(2^h : ℕ)^2*(occupationRank k : ℝ) := by
    have hp := occupationRank_pos k
    positivity
  have hm := (le_div_iff₀ hpos).mp hr
  have hp : ((2^h : ℕ)^2 : ℝ)=(4 : ℝ)^h := by
    push_cast
    rw [← pow_mul, Nat.mul_comm h 2,pow_mul]
    norm_num
  rw [one_mul,hp] at hm
  have hn : 4^h*occupationRank k≤4^k := by exact_mod_cast hm
  have hpow : 4^h≤4^k := by
    have ht' : 4^h≤4^h*occupationRank k := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (4^h) (Nat.succ_le_iff.mpr (occupationRank_pos k))
    exact ht'.trans hn
  have hh : h≤k := (Nat.pow_le_pow_iff_right (by decide : 1<4)).mp hpow
  apply bellPairYield_maximal k h hh
  have hk : k=k-h+h := by omega
  have he : 4^k=4^(k-h)*4^h := by
    conv_lhs => rw [hk]
    rw [Nat.pow_add]
  rw [he] at hn
  have hp : 0<4^h := by positivity
  exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [Nat.mul_comm] using hn)

end CircuitRecursion
