import APPTReview.AsymptoticUpper
import APPTReview.ProjectionState

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Exact deficit from the continuous rank optimum; no asymptotic substitution. -/
theorem plateau_rounding_identity (m n k : ℝ) (hm : m^2-1≠0)
    (hZ : m*n*(m-1)+2*k≠0) :
    m^2/(m^2-1)-(m*n)*((m*n*(m-1)^2+4*m*k)/(m*n*(m-1)+2*k)^2) =
      (m^2/(m^2-1))*(2*k-(m-1)*n)^2/(m*n*(m-1)+2*k)^2 := by
  rw [← mul_div_assoc, div_sub_div _ _ hm (pow_ne_zero 2 hZ)]
  have he : m^2*(m*n*(m-1)+2*k)^2-
      (m^2-1)*(m*n*(m*n*(m-1)^2+4*m*k))=
      m^2*(2*k-(m-1)*n)^2 := by ring
  rw [he, ← div_div]
  ring

/-- The actual broad-plateau density approaches the fixed-m optimum from below,
with a dimension-uniform rounding error at most 1/n^2. -/
theorem exists_appt_fixed_local_lower {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      (m:ℝ)^2/((m:ℝ)^2-1)-1/(n:ℝ)^2 ≤ ((m:ℝ)*n)*APPT.Quantum.purity A ∧
      ((m:ℝ)*n)*APPT.Quantum.purity A ≤ (m:ℝ)^2/((m:ℝ)^2-1) := by
  let k := ((m-1)*n+1)/2
  have hkN : (m-1)*n≤2*k ∧ 2*k≤(m-1)*n+1 := by dsimp [k]; omega
  have hcast : (((m-1)*n:ℕ):ℝ)=((m:ℝ)-1)*n := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1≤m), Nat.cast_one]
  have hk0 : ((m:ℝ)-1)*n≤2*(k:ℝ) := by
    rw [← hcast]
    exact_mod_cast hkN.1
  have hk1 : 2*(k:ℝ)≤((m:ℝ)-1)*n+1 := by
    rw [← hcast]
    exact_mod_cast hkN.2
  let s : ℝ := 2*(k:ℝ)-((m:ℝ)-1)*n
  let Z := plateauDenominator m n k
  let C : ℝ := (m:ℝ)^2/((m:ℝ)^2-1)
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hnP : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hmP : (0:ℝ)<m := by linarith
  have hbase : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have hs0 : 0≤s := by dsimp [s]; linarith
  have hs1 : s≤1 := by dsimp [s]; linarith
  have hs2 : s^2≤1 := by nlinarith
  have hC0 : 0≤C := div_nonneg (sq_nonneg _) hbase.le
  have hCm : C≤(m:ℝ)^2 := by
    apply (div_le_iff₀ hbase).2
    have htwo : (1:ℝ)≤(m:ℝ)^2-1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left htwo (sq_nonneg (m:ℝ))
  have hZ : (m:ℝ)*n≤Z := by
    have hm2 : (m:ℝ)≤(m:ℝ)^2-1 := by nlinarith
    have hx := mul_le_mul_of_nonneg_right hm2 hnP.le
    dsimp [Z, plateauDenominator]
    nlinarith
  have hDP : (0:ℝ)<(m:ℝ)*n := mul_pos hmP hnP
  have hZP : 0<Z := hDP.trans_le hZ
  have hCs : C*s^2≤(m:ℝ)^2 := (mul_le_mul_of_nonneg_left hs2 hC0).trans (by simpa using hCm)
  have hdiff : 0≤C*s^2/Z^2 := by positivity
  have hsmall : C*s^2/Z^2≤1/(n:ℝ)^2 := by
    calc
      _ ≤ (m:ℝ)^2/Z^2 := div_le_div_of_nonneg_right hCs (sq_nonneg Z)
      _ ≤ (m:ℝ)^2/((m:ℝ)*n)^2 := div_le_div_of_nonneg_left
        (sq_nonneg _) (sq_pos_of_pos hDP) (pow_le_pow_left₀ hDP.le hZ 2)
      _ = _ := by field_simp <;> ring
  obtain ⟨A,hd,ha,hpur⟩ := exists_broad_plateau hm hmn
  have hid := plateau_rounding_identity (m:ℝ) (n:ℝ) (k:ℝ) (ne_of_gt hbase)
    (show (m:ℝ)*n*((m:ℝ)-1)+2*(k:ℝ)≠0 from ne_of_gt hZP)
  have hq : C-((m:ℝ)*n)*APPT.Quantum.purity A=C*s^2/Z^2 := by
    rw [hpur]
    exact hid
  refine ⟨A,hd,ha,?_,?_⟩
  · change C-1/(n:ℝ)^2≤((m:ℝ)*n)*APPT.Quantum.purity A
    linarith
  · change ((m:ℝ)*n)*APPT.Quantum.purity A≤C
    linarith

end APPTReview
