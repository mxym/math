import RationalGateProvider.SignedFifths
import RationalGateProvider.GaussianAngle
import CircuitRecursion.PrecomputedNet

open scoped ComplexConjugate
open CircuitRecursion RationalGateProvider
namespace RationalGateInterface

noncomputable def rationalGate : Fin 4 → SU2 := ![
  quaternionSU2 rationalPhase 0 (by simp [rationalPhase_normSq]),
  quaternionSU2 ((3 - 4 * Complex.I) / 5) 0 (by
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]),
  quaternionSU2 (3 / 5) (4 * Complex.I / 5) (by
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]),
  quaternionSU2 (3 / 5) (-4 * Complex.I / 5) (by
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im])]

def inverseLabel : Fin 4 → Fin 4 := ![1, 0, 3, 2]

def coordinateShape : Fin 4 → Fin 4 → Bool × Remainder := ![
  ![(false,.r3), (false,.r4), (false,.r0), (false,.r0)],
  ![(false,.r3), (true,.r4), (false,.r0), (false,.r0)],
  ![(false,.r3), (false,.r0), (false,.r0), (false,.r4)],
  ![(false,.r3), (false,.r0), (false,.r0), (true,.r4)]]

def rationalCoordinate (i j : Fin 4) : ℚ :=
  signedTarget (coordinateShape i j).1 (coordinateShape i j).2

theorem rationalGate_coordinates (i j : Fin 4) :
    quaternionCoordinates (rationalGate i) j = (rationalCoordinate i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalGate, quaternionCoordinates, quaternionSU2, quaternionMatrix,
      rationalPhase_formula, rationalCoordinate, coordinateShape, signedTarget,
      Remainder.value, Complex.div_re, Complex.div_im]

theorem rationalGate_inverse (i : Fin 4) :
    rationalGate (inverseLabel i) = (rationalGate i)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  change (rationalGate (inverseLabel i)).val * (rationalGate i).val =
    (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    apply Complex.ext <;>
    norm_num [rationalGate, inverseLabel, quaternionSU2, quaternionMatrix,
      rationalPhase_formula, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

/-- Four concrete finite-state queries; the output contains binary lists.
Integer materialization below is a separate value interface, not a bit-time bound. -/
def entryBits (i : Fin 4) (precision : ℕ) : List.Vector SignedBits 4 :=
  List.Vector.ofFn fun j =>
    signedRun (coordinateShape i j).1 (coordinateShape i j).2 precision

def dyadicEntry (i : Fin 4) : DyadicQuaternionOracle := fun precision =>
  (entryBits i precision).map SignedBits.value

theorem entryBits_error (i j : Fin 4) (precision : ℕ) :
    |(((entryBits i precision).get j).value : ℝ) / 2 ^ precision -
      (rationalCoordinate i j : ℝ)| ≤ (1 / 2 : ℝ) ^ precision := by
  simpa only [entryBits, List.Vector.get_ofFn, rationalCoordinate] using
    (signedRun_error_real (coordinateShape i j).1
      (coordinateShape i j).2 precision).le

theorem dyadicEntry_correct (i : Fin 4) :
    DyadicQApproximates (dyadicEntry i) (rationalGate i) := by
  intro precision j
  simp only [dyadicQuaternionOracle, dyadicEntry, List.Vector.get_map,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
  rw [rationalGate_coordinates]
  exact entryBits_error i j precision

theorem entryBits_length (i j : Fin 4) (precision : ℕ) :
    ((entryBits i precision).get j).magnitude.length = precision := by
  simpa only [entryBits, List.Vector.get_ofFn] using
    signedRun_length (coordinateShape i j).1 (coordinateShape i j).2 precision

theorem entryBits_total_length (i : Fin 4) (precision : ℕ) :
    (∑ j : Fin 4, ((entryBits i precision).get j).magnitude.length) +
      (denominatorBits precision).length = 5 * precision + 1 := by
  simp only [entryBits_length, denominator_length]
  norm_num
  omega

end RationalGateInterface
