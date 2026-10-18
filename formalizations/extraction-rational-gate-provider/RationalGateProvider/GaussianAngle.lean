import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! An elementary infinite-order certificate for the rational unit phase.
This is an auxiliary fact for a prospective concrete gate library, not a
standalone SU(2) density or compiler-time theorem. -/
namespace RationalGateProvider

def gaussianNumerator : GaussianInt := ⟨3, 4⟩

def residueFive : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(2 : ZMod 5), by decide⟩

theorem residueFive_numerator : residueFive gaussianNumerator = 1 := by
  norm_num [residueFive, gaussianNumerator, Zsqrtd.lift] <;> decide

theorem gaussianNumerator_pow_ne (n : ℕ) (hn : 0 < n) :
    gaussianNumerator ^ n ≠ (5 : GaussianInt) ^ n := by
  intro h
  have hfive : residueFive (5 : GaussianInt) = 0 := by
    change residueFive ((5 : ℕ) : GaussianInt) = 0
    rw [map_natCast]
    decide
  have hmod := congrArg residueFive h
  simp only [map_pow, residueFive_numerator, hfive, one_pow,
    zero_pow (by omega : n ≠ 0)] at hmod
  exact (by decide : (1 : ZMod 5) ≠ 0) hmod

noncomputable def rationalPhase : ℂ := GaussianInt.toComplex gaussianNumerator / 5

theorem rationalPhase_formula : rationalPhase = (3 + 4 * Complex.I) / 5 := by
  simp [rationalPhase, gaussianNumerator, GaussianInt.toComplex_def]

theorem rationalPhase_normSq : Complex.normSq rationalPhase = 1 := by
  rw [rationalPhase_formula]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem rationalPhase_pow_ne_one (n : ℕ) (hn : 0 < n) : rationalPhase ^ n ≠ 1 := by
  intro h
  apply gaussianNumerator_pow_ne n hn
  apply GaussianInt.toComplex_injective
  have hc : (GaussianInt.toComplex gaussianNumerator) ^ n = (5 : ℂ) ^ n := by
    have hd : (GaussianInt.toComplex gaussianNumerator) ^ n / (5 : ℂ) ^ n = 1 := by
      simpa only [rationalPhase, div_pow] using h
    exact (div_eq_one_iff_eq (pow_ne_zero n (by norm_num : (5 : ℂ) ≠ 0))).mp hd
  simpa only [map_pow, map_ofNat] using hc

end RationalGateProvider
