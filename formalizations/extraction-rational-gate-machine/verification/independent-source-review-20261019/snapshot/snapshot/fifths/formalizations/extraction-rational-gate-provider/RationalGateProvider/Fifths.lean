import Mathlib.Tactic

/-! A concrete five-state binary-output transducer for rational fifths.
The returned bit list is little endian. The state table uses no division.
The transition count concerns this transducer, not the complete compiler. -/
namespace RationalGateProvider

inductive Remainder where
  | r0 | r1 | r2 | r3 | r4
  deriving DecidableEq, Repr

def Remainder.value : Remainder → ℕ
  | .r0 => 0 | .r1 => 1 | .r2 => 2 | .r3 => 3 | .r4 => 4

def transition : Remainder → Bool × Remainder
  | .r0 => (false, .r0)
  | .r1 => (false, .r2)
  | .r2 => (false, .r4)
  | .r3 => (true, .r1)
  | .r4 => (true, .r3)

def bitValue : List Bool → ℕ
  | [] => 0
  | bit :: tail => bit.toNat + 2 * bitValue tail

structure Output where
  bits : List Bool
  remainder : Remainder
  deriving Repr

def next (s : Output) : Output :=
  let digit := transition s.remainder
  ⟨digit.1 :: s.bits, digit.2⟩

def run (initial : Remainder) : ℕ → Output
  | 0 => ⟨[], initial⟩
  | precision + 1 => next (run initial precision)

theorem remainder_lt_five (r : Remainder) : r.value < 5 := by
  cases r <;> norm_num [Remainder.value]

theorem transition_conserves (r : Remainder) :
    5 * (transition r).1.toNat + (transition r).2.value = 2 * r.value := by
  cases r <;> norm_num [transition, Remainder.value, Bool.toNat]

theorem next_conserves (s : Output) :
    5 * bitValue (next s).bits + (next s).remainder.value =
      2 * (5 * bitValue s.bits + s.remainder.value) := by
  have h := transition_conserves s.remainder
  simp only [next, bitValue]
  omega

theorem run_conserves (initial : Remainder) (precision : ℕ) :
    5 * bitValue (run initial precision).bits + (run initial precision).remainder.value =
      initial.value * 2 ^ precision := by
  induction precision with
  | zero => simp [run, bitValue]
  | succ p ih =>
      change 5 * bitValue (next (run initial p)).bits +
        (next (run initial p)).remainder.value = initial.value * 2 ^ (p + 1)
      rw [next_conserves, ih, pow_succ]
      ring

theorem run_bits_length (initial : Remainder) (precision : ℕ) :
    (run initial precision).bits.length = precision := by
  induction precision with
  | zero => rfl
  | succ p ih => simpa [run, next] using congrArg Nat.succ ih

theorem run_quotient (initial : Remainder) (precision : ℕ) :
    bitValue (run initial precision).bits = initial.value * 2 ^ precision / 5 := by
  have h := run_conserves initial precision
  have hr := remainder_lt_five (run initial precision).remainder
  omega

theorem run_remainder (initial : Remainder) (precision : ℕ) :
    (run initial precision).remainder.value = initial.value * 2 ^ precision % 5 := by
  have h := run_conserves initial precision
  have hr := remainder_lt_five (run initial precision).remainder
  omega

theorem run_dyadic_error (initial : Remainder) (precision : ℕ) :
    0 ≤ (initial.value : ℚ) / 5 -
      (bitValue (run initial precision).bits : ℚ) / 2 ^ precision ∧
    (initial.value : ℚ) / 5 -
      (bitValue (run initial precision).bits : ℚ) / 2 ^ precision <
      1 / (2 : ℚ) ^ precision := by
  have h := run_conserves initial precision
  have hr := remainder_lt_five (run initial precision).remainder
  have hc : 5 * (bitValue (run initial precision).bits : ℚ) +
      ((run initial precision).remainder.value : ℚ) =
      (initial.value : ℚ) * (2 : ℚ) ^ precision := by exact_mod_cast h
  have hrc : ((run initial precision).remainder.value : ℚ) < 5 := by exact_mod_cast hr
  have hp : (0 : ℚ) < 2 ^ precision := by positivity
  have residual : (initial.value : ℚ) / 5 -
      (bitValue (run initial precision).bits : ℚ) / 2 ^ precision =
      ((run initial precision).remainder.value : ℚ) / (5 * 2 ^ precision) := by
    field_simp
    nlinarith
  rw [residual]
  constructor
  · positivity
  · apply (div_lt_div_iff₀ (by positivity : (0 : ℚ) < 5 * 2 ^ precision) hp).2
    nlinarith

/-- One actual table transition emits one bit and retains the same list tail. -/
inductive Steps : ℕ → Output → Output → Prop
  | zero (s : Output) : Steps 0 s s
  | step {n : ℕ} {start finish : Output} : Steps n start finish →
      Steps (n + 1) start (next finish)

theorem run_steps (initial : Remainder) (precision : ℕ) :
    Steps precision ⟨[], initial⟩ (run initial precision) := by
  induction precision with
  | zero => exact .zero _
  | succ p ih => exact .step ih

theorem three_fifths (precision : ℕ) :
    bitValue (run .r3 precision).bits = 3 * 2 ^ precision / 5 := by
  exact run_quotient .r3 precision

theorem four_fifths (precision : ℕ) :
    bitValue (run .r4 precision).bits = 4 * 2 ^ precision / 5 := by
  exact run_quotient .r4 precision

end RationalGateProvider
