import BapatMixedFischer
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace BapatRankTwo.Exact

abbrev GI := Zsqrtd (-1)
abbrev Coeffs := List GI

noncomputable def toComplex : GI →+* ℂ := Zsqrtd.lift ⟨Complex.I, by simp⟩

/-- Ascending coefficient lists, interpreted by Horner's rule. No trimming or
degree hypothesis is built into the representation. -/
noncomputable def interpret : Coeffs → ℂ[X]
  | [] => 0
  | c :: cs => C (toComplex c) + X * interpret cs

noncomputable def add : Coeffs → Coeffs → Coeffs
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: add xs ys

noncomputable def scale (z : GI) : Coeffs → Coeffs
  | [] => []
  | c :: cs => (z * c) :: scale z cs

noncomputable def neg : Coeffs → Coeffs
  | [] => []
  | c :: cs => (-c) :: neg cs

noncomputable def sub (P Q : Coeffs) : Coeffs := add P (neg Q)

noncomputable def shift (P : Coeffs) : Coeffs := 0 :: P

noncomputable def mulLinear (a b : GI) (P : Coeffs) : Coeffs :=
  add (scale a P) (shift (scale b P))

noncomputable def derivativeAux (k : ℕ) : Coeffs → Coeffs
  | [] => []
  | c :: cs => ((k : GI) * c) :: derivativeAux (k + 1) cs

noncomputable def derivative (P : Coeffs) : Coeffs := derivativeAux 1 P.tail

/-- m is the number of old factors, before appending the new vector (a,b). -/
noncomputable def sStep (m : ℕ) (a b : GI) (F S : Coeffs) : Coeffs :=
  sub (add (mulLinear a b S)
    (scale b (sub (scale (m : GI) F) (shift (derivative F)))))
    (scale a (derivative F))

noncomputable def state (v : ℕ → GI × GI) : ℕ → Coeffs × Coeffs
  | 0 => ([1], [])
  | m + 1 =>
      let old := state v m
      (mulLinear (v m).1 (v m).2 old.1,
        sStep m (v m).1 (v m).2 old.1 old.2)

noncomputable def vectorAt (v : List (GI × GI)) (m : ℕ) : GI × GI :=
  (v[m]?).getD (0, 0)

noncomputable def squareAbs (z : GI) : ℤ := z.re * z.re + z.im * z.im

/-- This deliberately reads exactly n+1 coefficients, padding with zero and
ignoring any further coefficients. Thus the norm interpretation requires no
list length or no-trailing-zero side condition. -/
noncomputable def fischerInt (n : ℕ) (P : Coeffs) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.factorial (n - k) * Nat.factorial k : ℕ) : ℤ) *
      squareAbs ((P[k]?).getD 0)

@[simp] theorem interpret_nil : interpret [] = 0 := rfl

theorem interpret_add (P Q : Coeffs) :
    interpret (add P Q) = interpret P + interpret Q := by
  induction P generalizing Q with
  | nil => simp [add, interpret]
  | cons c P ih =>
      cases Q with
      | nil => simp [add, interpret]
      | cons d Q =>
          simp only [add, interpret, ih, map_add]
          ring

theorem interpret_scale (z : GI) (P : Coeffs) :
    interpret (scale z P) = C (toComplex z) * interpret P := by
  induction P with
  | nil => simp [scale, interpret]
  | cons c P ih =>
      simp only [scale, interpret, ih, map_mul]
      ring

theorem interpret_neg (P : Coeffs) : interpret (neg P) = -interpret P := by
  induction P with
  | nil => simp [neg, interpret]
  | cons c P ih =>
      simp only [neg, interpret, ih, map_neg]
      ring

theorem interpret_sub (P Q : Coeffs) :
    interpret (sub P Q) = interpret P - interpret Q := by
  rw [sub, interpret_add, interpret_neg, sub_eq_add_neg]

theorem interpret_shift (P : Coeffs) : interpret (shift P) = X * interpret P := by
  simp [shift, interpret]

theorem interpret_mulLinear (a b : GI) (P : Coeffs) :
    interpret (mulLinear a b P) =
      (C (toComplex a) + C (toComplex b) * X) * interpret P := by
  rw [mulLinear, interpret_add, interpret_scale, interpret_shift, interpret_scale]
  ring

theorem interpret_derivativeAux (k : ℕ) (P : Coeffs) :
    interpret (derivativeAux k P) =
      C (k : ℂ) * interpret P + X * (interpret P).derivative := by
  induction P generalizing k with
  | nil => simp [derivativeAux, interpret]
  | cons c P ih =>
      simp only [derivativeAux, interpret, ih, map_mul, map_natCast,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, zero_add, one_mul, Nat.cast_add, Nat.cast_one,
        map_add, map_one]
      ring

theorem interpret_derivative (P : Coeffs) :
    interpret (derivative P) = (interpret P).derivative := by
  cases P with
  | nil => simp [derivative, derivativeAux, interpret]
  | cons c P =>
      simp only [derivative, List.tail_cons, interpret_derivativeAux, interpret,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, Nat.cast_one, map_one, one_mul, zero_add]

theorem interpret_sStep (m : ℕ) (a b : GI) (F S : Coeffs) :
    interpret (sStep m a b F S) =
      (C (toComplex a) + C (toComplex b) * X) * interpret S +
        C (toComplex b) * (C (m : ℂ) * interpret F - X * (interpret F).derivative) -
          C (toComplex a) * (interpret F).derivative := by
  simp only [sStep, interpret_sub, interpret_add, interpret_mulLinear,
    interpret_scale, interpret_shift, interpret_derivative, map_natCast]

theorem coeff_interpret (P : Coeffs) (k : ℕ) :
    (interpret P).coeff k = toComplex ((P[k]?).getD 0) := by
  induction P generalizing k with
  | nil => simp [interpret]
  | cons c P ih =>
      cases k with
      | zero => simp [interpret]
      | succ k => simp [interpret, Polynomial.coeff_X_mul, ih]

theorem squareAbs_toComplex (z : GI) :
    (squareAbs z : ℝ) = Complex.normSq (toComplex z) := by
  simp [squareAbs, Complex.normSq_apply, toComplex, Zsqrtd.lift_apply_apply]

/-- Exact integer Fischer computation agrees with the genuine polynomial
norm, for every list and every supplied homogeneous degree, including lists
with trailing zeroes or lists longer/shorter than the degree bound. -/
theorem fischerInt_correct (n : ℕ) (P : Coeffs) :
    (fischerInt n P : ℝ) = BapatFischer.fischerNormSq n (interpret P) := by
  simp only [fischerInt, BapatFischer.fischerNormSq, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, coeff_interpret, squareAbs_toComplex]

end BapatRankTwo.Exact
