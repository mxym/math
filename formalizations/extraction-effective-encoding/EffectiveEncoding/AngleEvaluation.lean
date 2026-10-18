import EffectiveEncoding.Elementary

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

def AngleAtom.cosOracle : AngleAtom → RationalOracle
  | .pi => oracleConst (-1)
  | .merge A B j =>
      if j=0 ∨ A+B=0 then oracleConst 1 else mergeCosOracle A B

def AngleAtom.sinOracle : AngleAtom → RationalOracle
  | .pi => oracleConst 0
  | .merge A B j =>
      if j=0 ∨ A+B=0 then oracleConst 0 else mergeSinOracle A B

theorem mergeAngle_degenerate (A B j : ℕ) (h : j=0 ∨ A+B=0) :
    mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)=0 := by
  rcases h with h|h
  · simp [h,mergeAngle]
  · have hA : A=0 := by omega
    have hB : B=0 := by omega
    simp [hA,hB,mergeAngle]

theorem AngleAtom.cosOracle_correct (a : AngleAtom) :
    Approximates a.cosOracle (Real.cos a.value) := by
  cases a with
  | pi => simpa [AngleAtom.cosOracle,AngleAtom.value] using oracleConst_correct (-1)
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simpa only [AngleAtom.cosOracle,if_pos h,AngleAtom.value,mergeAngle_degenerate A B j h,Real.cos_zero,Rat.cast_one] using
        oracleConst_correct 1
    · simp only [AngleAtom.cosOracle,if_neg h,AngleAtom.value]
      exact mergeCosOracle_correct A B j (by omega) (by omega)

theorem AngleAtom.sinOracle_correct (a : AngleAtom) :
    Approximates a.sinOracle (Real.sin a.value) := by
  cases a with
  | pi => simpa [AngleAtom.sinOracle,AngleAtom.value] using oracleConst_correct 0
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simpa only [AngleAtom.sinOracle,if_pos h,AngleAtom.value,mergeAngle_degenerate A B j h,Real.sin_zero,Rat.cast_zero] using
        oracleConst_correct 0
    · simp only [AngleAtom.sinOracle,if_neg h,AngleAtom.value]
      exact mergeSinOracle_correct A B j (by omega) (by omega)

theorem AngleAtom.value_bounds (a : AngleAtom) : 0≤a.value ∧ a.value≤Real.pi := by
  cases a with
  | pi => exact ⟨Real.pi_pos.le,le_rfl⟩
  | merge A B j =>
    have h := mergeAngle_bounds ((A:ℝ)/j) ((B:ℝ)/j)
    exact ⟨h.1,h.2.trans (by linarith [Real.pi_pos])⟩

def AngleCode.cosOracle (a : AngleCode) : RationalOracle :=
  halfCosOracle a.halvings a.atom.cosOracle

def AngleCode.sinOracle (a : AngleCode) : RationalOracle :=
  if a.negative then
    oracleNeg (halfSinOracle a.halvings a.atom.cosOracle a.atom.sinOracle)
  else halfSinOracle a.halvings a.atom.cosOracle a.atom.sinOracle

theorem AngleCode.cosOracle_correct (a : AngleCode) :
    Approximates a.cosOracle (Real.cos a.value) := by
  have h := halfCosOracle_correct a.atom.cosOracle a.atom.value a.atom.cosOracle_correct
    a.atom.value_bounds.1 a.atom.value_bounds.2 a.halvings
  cases hn : a.negative
  · simpa [AngleCode.cosOracle,AngleCode.value,hn] using h
  · simpa [AngleCode.cosOracle,AngleCode.value,hn,neg_div] using h

theorem AngleCode.sinOracle_correct (a : AngleCode) :
    Approximates a.sinOracle (Real.sin a.value) := by
  have h := halfSinOracle_correct a.atom.cosOracle a.atom.sinOracle a.atom.value
    a.atom.cosOracle_correct a.atom.sinOracle_correct
    a.atom.value_bounds.1 a.atom.value_bounds.2 a.halvings
  cases hn : a.negative
  · simpa [AngleCode.sinOracle,AngleCode.value,hn] using h
  · simpa [AngleCode.sinOracle,AngleCode.value,hn,neg_div] using
      oracleNeg_correct _ _ h

/-- Each angle carried by an actual phase gate has a total, finite rational
evaluation procedure, including zero denominators and zero masses. -/
theorem AngleCode.evaluation (a : AngleCode) (p : ℕ) :
    |(a.cosOracle p:ℝ)-Real.cos a.value|≤(1/2:ℝ)^p ∧
    |(a.sinOracle p:ℝ)-Real.sin a.value|≤(1/2:ℝ)^p :=
  ⟨a.cosOracle_correct p,a.sinOracle_correct p⟩

end EffectiveEncoding

