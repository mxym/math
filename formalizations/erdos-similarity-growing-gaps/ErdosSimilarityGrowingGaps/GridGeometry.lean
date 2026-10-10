import ErdosSimilarityGrowingGaps.Avoidance
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/
namespace ErdosSimilarityGrowingGaps

noncomputable def periodicGridKey (N : ℕ) (z : ℝ) : ℤ :=
  Int.floor ((N : ℝ) * z) % (N : ℤ)

noncomputable def periodicGridSet (N : ℕ) (cells : Finset ℤ) : Set ℝ :=
  {z | periodicGridKey N z ∈ cells}

theorem periodicGridKey_nonneg (N : ℕ) (hN : 0 < N) (z : ℝ) :
    0 ≤ periodicGridKey N z := by
  exact Int.emod_nonneg _ (by exact_mod_cast hN.ne')

theorem periodicGridKey_lt (N : ℕ) (hN : 0 < N) (z : ℝ) :
    periodicGridKey N z < N := by
  exact Int.emod_lt_of_pos _ (by exact_mod_cast hN)

noncomputable def gridAddress (b : ℕ) (z : ℝ) : Fin (2 ^ (b + 3)) :=
  ⟨(periodicGridKey (2 ^ (b + 3)) z).toNat, by
    have hp : 0 < (2 : ℕ) ^ (b + 3) := pow_pos (by decide) _
    have hl := periodicGridKey_nonneg (2 ^ (b + 3)) hp z
    have hu := periodicGridKey_lt (2 ^ (b + 3)) hp z
    omega⟩

@[simp] theorem gridAddress_intCast (b : ℕ) (z : ℝ) :
    ((gridAddress b z).val : ℤ) = periodicGridKey (2 ^ (b + 3)) z := by
  exact Int.toNat_of_nonneg
    (periodicGridKey_nonneg _ (pow_pos (by decide) _) z)

theorem gridAddress_eq_iff (b : ℕ) (z z' : ℝ) :
    gridAddress b z = gridAddress b z' ↔
      periodicGridKey (2 ^ (b + 3)) z = periodicGridKey (2 ^ (b + 3)) z' := by
  constructor
  · intro h
    simpa using congrArg (fun q : Fin (2 ^ (b + 3)) => (q.val : ℤ)) h
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h

theorem periodicGridKey_fract (N : ℕ) (hN : 0 < N) (z : ℝ) :
    periodicGridKey N z = Int.floor ((N : ℝ) * Int.fract z) := by
  have hfloor : Int.floor ((N : ℝ) * z) =
      Int.floor ((N : ℝ) * Int.fract z) + (N : ℤ) * Int.floor z := by
    have hz : (N : ℝ) * z = (N : ℝ) * Int.fract z +
        (((N : ℤ) * Int.floor z : ℤ) : ℝ) := by
      simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hz, Int.floor_add_intCast]
  have hl : 0 ≤ Int.floor ((N : ℝ) * Int.fract z) :=
    Int.floor_nonneg.2 (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _))
  have hu : Int.floor ((N : ℝ) * Int.fract z) < N := by
    apply Int.floor_lt.2
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one z) hNr
  simp only [periodicGridKey, hfloor, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt hl hu

/-- A fine dyadic key determines the exact coarse key, including boundary keys. -/
theorem periodicGridKey_refinement (N r : ℕ) (hN : 0 < N) (hr : 0 < r) (z : ℝ) :
    periodicGridKey (r * N) z / (r : ℤ) = periodicGridKey N z := by
  rw [periodicGridKey_fract (r * N) (Nat.mul_pos hr hN),
    periodicGridKey_fract N hN]
  have heq : ((r * N : ℕ) : ℝ) * Int.fract z =
      (r : ℝ) * ((N : ℝ) * Int.fract z) := by push_cast; ring
  rw [heq]
  exact Int.natCast_mul_floor_div_cancel hr.ne' _

theorem dyadic_grid_key_refinement (b b' : ℕ) (hb : b ≤ b') (z : ℝ) :
    periodicGridKey (2 ^ (b' + 3)) z / ((2 : ℤ) ^ (b' - b)) =
      periodicGridKey (2 ^ (b + 3)) z := by
  have heq : (2 : ℕ) ^ (b' + 3) = 2 ^ (b' - b) * 2 ^ (b + 3) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [heq, Nat.cast_pow, Nat.cast_ofNat] using
    periodicGridKey_refinement (2 ^ (b + 3)) (2 ^ (b' - b))
      (pow_pos (by decide) _) (pow_pos (by decide) _) z

theorem dyadic_grid_eq_of_finer_eq (b b' : ℕ) (hb : b ≤ b') (z z' : ℝ)
    (h : gridAddress b' z = gridAddress b' z') :
    gridAddress b z = gridAddress b z' := by
  apply (gridAddress_eq_iff b z z').2
  rw [← dyadic_grid_key_refinement b b' hb z,
    ← dyadic_grid_key_refinement b b' hb z']
  rw [(gridAddress_eq_iff b' z z').1 h]

def NoGridBoundary (N : ℕ) (x R : ℝ) : Prop :=
  ∀ b : ℤ, ¬ (x < (b : ℝ) / N ∧ (b : ℝ) / N ≤ x + R)

/-- The left boundary is allowed and the right boundary is excluded exactly. -/
theorem periodicGridKey_eq_of_no_boundary (N : ℕ) (hN : 0 < N) (x R z : ℝ)
    (hz : x ≤ z ∧ z ≤ x + R) (hs : NoGridBoundary N x R) :
    periodicGridKey N z = periodicGridKey N x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : Int.floor ((N : ℝ) * z) = Int.floor ((N : ℝ) * x) := by
    apply le_antisymm
    · by_contra hn
      have hh : Int.floor ((N : ℝ) * x) < Int.floor ((N : ℝ) * z) := by omega
      apply hs (Int.floor ((N : ℝ) * z))
      constructor
      · apply (lt_div_iff₀ hNr).2
        simpa [mul_comm] using Int.floor_lt.1 hh
      · apply (div_le_iff₀ hNr).2
        have hh' := (Int.floor_le ((N : ℝ) * z)).trans
          (mul_le_mul_of_nonneg_left hz.2 hNr.le)
        simpa [mul_comm] using hh'
    · exact Int.floor_mono (mul_le_mul_of_nonneg_left hz.1 hNr.le)
  simp only [periodicGridKey, hf]

/-- Same periodic keys cannot be separated by more than one cell while staying
strictly short of a full turn. This proves actual address separation at boundaries. -/
theorem periodicGridKey_ne_of_scaled_gap (N : ℕ) (hN : 0 < N) (z z' : ℝ)
    (hl : 1 ≤ (N : ℝ) * (z' - z))
    (hu : (N : ℝ) * (z' - z) ≤ (N : ℝ) - 1) :
    periodicGridKey N z ≠ periodicGridKey N z' := by
  have hNi : (0 : ℤ) < N := by exact_mod_cast hN
  have hlow : Int.floor ((N : ℝ) * z) < Int.floor ((N : ℝ) * z') := by
    have hh : Int.floor ((N : ℝ) * z) + 1 ≤ Int.floor ((N : ℝ) * z') := by
      apply Int.le_floor.2
      push_cast
      nlinarith [Int.floor_le ((N : ℝ) * z)]
    omega
  have hupp : Int.floor ((N : ℝ) * z') <
      (N : ℤ) + Int.floor ((N : ℝ) * z) := by
    have hh := Int.lt_floor_add_one ((N : ℝ) * z)
    have hh' := Int.floor_le ((N : ℝ) * z')
    have : (Int.floor ((N : ℝ) * z') : ℝ) <
        (N : ℝ) + (Int.floor ((N : ℝ) * z) : ℝ) := by nlinarith
    exact_mod_cast this
  intro heq
  have hdvd : (N : ℤ) ∣ Int.floor ((N : ℝ) * z') - Int.floor ((N : ℝ) * z) := by
    rw [Int.dvd_iff_emod_eq_zero]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.1 heq.symm
  have hh := (Int.le_add_iff_lt_of_dvd_sub hNi hdvd).2 hlow
  omega


end ErdosSimilarityGrowingGaps
