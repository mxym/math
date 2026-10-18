import RationalGateProvider.Fifths

namespace RationalGateProvider

structure SignedBits where
  negative : Bool
  magnitude : List Bool
  deriving Repr

def SignedBits.value (s : SignedBits) : ℤ :=
  if s.negative then -(bitValue s.magnitude : ℤ) else (bitValue s.magnitude : ℤ)

def signedRun (negative : Bool) (initial : Remainder) (precision : ℕ) : SignedBits :=
  ⟨negative, (run initial precision).bits⟩

def denominatorBits (precision : ℕ) : List Bool :=
  List.replicate precision false ++ [true]

theorem denominator_value (precision : ℕ) :
    bitValue (denominatorBits precision) = 2 ^ precision := by
  induction precision with
  | zero => simp [denominatorBits, bitValue]
  | succ p ih =>
      simp only [denominatorBits, List.replicate_succ, List.cons_append, bitValue,
        Bool.toNat_false, zero_add]
      change 2 * bitValue (denominatorBits p) = 2 ^ (p + 1)
      rw [ih, pow_succ]
      omega

theorem denominator_length (precision : ℕ) :
    (denominatorBits precision).length = precision + 1 := by
  simp [denominatorBits]

theorem denominator_positive (precision : ℕ) :
    0 < bitValue (denominatorBits precision) := by
  rw [denominator_value]
  positivity

theorem signedRun_length (negative : Bool) (initial : Remainder) (precision : ℕ) :
    (signedRun negative initial precision).magnitude.length = precision := by
  exact run_bits_length initial precision

theorem signedRun_value (negative : Bool) (initial : Remainder) (precision : ℕ) :
    (signedRun negative initial precision).value =
      if negative then -((initial.value * 2 ^ precision / 5 : ℕ) : ℤ) else
        ((initial.value * 2 ^ precision / 5 : ℕ) : ℤ) := by
  simp [signedRun, SignedBits.value, run_quotient]

def signedTarget (negative : Bool) (initial : Remainder) : ℚ :=
  if negative then -(initial.value : ℚ) / 5 else (initial.value : ℚ) / 5

theorem signedRun_error (negative : Bool) (initial : Remainder) (precision : ℕ) :
    |((signedRun negative initial precision).value : ℚ) / 2 ^ precision -
      signedTarget negative initial| < 1 / (2 : ℚ) ^ precision := by
  have h := run_dyadic_error initial precision
  cases negative
  · have habs : |(bitValue (run initial precision).bits : ℚ) / 2 ^ precision -
        (initial.value : ℚ) / 5| < 1 / (2 : ℚ) ^ precision := by
      rw [abs_sub_comm, abs_of_nonneg h.1]
      exact h.2
    simpa [signedRun, SignedBits.value, signedTarget] using habs
  · have heq : ((signedRun true initial precision).value : ℚ) / 2 ^ precision -
        signedTarget true initial = (initial.value : ℚ) / 5 -
          (bitValue (run initial precision).bits : ℚ) / 2 ^ precision := by
      simp only [signedRun, SignedBits.value, ite_true, Int.cast_neg,
        Int.cast_natCast, signedTarget]
      ring
    rw [heq, abs_of_nonneg h.1]
    exact h.2

theorem signedRun_error_real (negative : Bool) (initial : Remainder) (precision : ℕ) :
    |((signedRun negative initial precision).value : ℝ) / 2 ^ precision -
      (signedTarget negative initial : ℝ)| < (1 / 2 : ℝ) ^ precision := by
  have h := signedRun_error negative initial precision
  have hc := (Rat.cast_lt (K := ℝ)).2 h
  have hcast : |((signedRun negative initial precision).value : ℝ) / 2 ^ precision -
      (signedTarget negative initial : ℝ)| < 1 / (2 : ℝ) ^ precision := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_one] using hc
  simpa [one_div_pow] using hcast

theorem total_output_bits (negative : Bool) (initial : Remainder) (precision : ℕ) :
    (signedRun negative initial precision).magnitude.length +
      (denominatorBits precision).length = 2 * precision + 1 := by
  rw [signedRun_length, denominator_length]
  omega

end RationalGateProvider
