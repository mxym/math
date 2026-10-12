import APPTReview.FixedLocalUpper
import APPTReview.PlateauApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- The objective set consists of scaled purities of genuine APPT density matrices. -/
def scaledAPPTPurities (m n : ℕ) : Set ℝ :=
  {x | ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
    APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
    x=((m:ℝ)*n)*APPT.Quantum.purity A}

noncomputable def scaledAPPTPuritySup (m n : ℕ) : ℝ := sSup (scaledAPPTPurities m n)

/-- A finite two-sided estimate for the true spectral optimization, with an
actual attaining-family lower bound and an unrestricted physical upper bound. -/
theorem fixed_local_sup_bounds {m n : ℕ} (hm : 2≤m) (hn : 2*m≤n) :
    (m:ℝ)^2/((m:ℝ)^2-1)-1/(n:ℝ)^2 ≤ scaledAPPTPuritySup m n ∧
    scaledAPPTPuritySup m n ≤ (m:ℝ)^2/((m:ℝ)^2-1)+13*(m:ℝ)/n := by
  obtain ⟨A,hd,ha,hlo,hhi⟩ := exists_appt_fixed_local_lower hm (by omega : m≤n)
  have hmem : ((m:ℝ)*n)*APPT.Quantum.purity A ∈ scaledAPPTPurities m n :=
    ⟨A,hd,ha,rfl⟩
  have hub (x : ℝ) (hx : x∈scaledAPPTPurities m n) :
      x≤(m:ℝ)^2/((m:ℝ)^2-1)+13*(m:ℝ)/n := by
    obtain ⟨B,hB,hp,rfl⟩ := hx
    exact density_appt_fixed_local_upper hm hn hB hp
  have hbd : BddAbove (scaledAPPTPurities m n) := ⟨_,hub⟩
  exact ⟨hlo.trans (le_csSup hbd hmem), csSup_le ⟨_,hmem⟩ hub⟩

/-- The complementary fixed-first-dimension asymptotic is proved as an actual
filter limit of the supremum over physical states, not a formal parameter substitution. -/
theorem appt_fixed_local_scaled_sup_tendsto (m : ℕ) (hm : 2≤m) :
    Tendsto (fun n : ℕ => scaledAPPTPuritySup m n) atTop
      (𝓝 ((m:ℝ)^2/((m:ℝ)^2-1))) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (max (2*(m:ℝ)) (26*(m:ℝ)/ε))
  refine ⟨N,?_⟩
  intro n hn
  have hnR : (N:ℝ)≤n := by exact_mod_cast hn
  have hnm : 2*(m:ℝ)<n := (le_max_left _ _).trans_lt (hN.trans_le hnR)
  have hne : 26*(m:ℝ)/ε<(n:ℝ) := (le_max_right _ _).trans_lt (hN.trans_le hnR)
  have hnNat : 2*m≤n := by exact_mod_cast hnm.le
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hnP : (0:ℝ)<n := by linarith
  have hn1 : (1:ℝ)≤n := by linarith
  have hmul : 26*(m:ℝ)<(n:ℝ)*ε := (div_lt_iff₀ hε).1 hne
  have herr : 13*(m:ℝ)/(n:ℝ)<ε := (div_lt_iff₀ hnP).2 (by nlinarith)
  have hsmall : 1/(n:ℝ)^2 ≤ 13*(m:ℝ)/(n:ℝ) := by
    calc
      _ ≤ 1/(n:ℝ) := div_le_div_of_nonneg_left (by norm_num) hnP (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hnP.le
  have hb := fixed_local_sup_bounds hm hnNat
  rw [Real.dist_eq]
  apply abs_lt.2
  constructor <;> linarith [hb.1,hb.2]

end APPTReview

namespace APPTReview

def apptPurityValues (m n : ℕ) : Set ℝ :=
  {x | ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
    APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧ x=APPT.Quantum.purity A}

noncomputable def apptPuritySup (m n : ℕ) : ℝ := sSup (apptPurityValues m n)

/-- Scaling the objective is justified for the actual nonempty bounded state set. -/
theorem scaled_sup_eq_dimension_mul_purity_sup {m n : ℕ} (hm : 2≤m) (hn : 2*m≤n) :
    scaledAPPTPuritySup m n=((m:ℝ)*n)*apptPuritySup m n := by
  have hD : (0:ℝ)<(m:ℝ)*n := by
    have hmP : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
    have hnP : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    positivity
  let U : ℝ := (m:ℝ)^2/((m:ℝ)^2-1)+13*(m:ℝ)/n
  obtain ⟨A,hd,ha,_,_⟩ := exists_appt_fixed_local_lower hm (by omega : m≤n)
  have hmem : APPT.Quantum.purity A∈apptPurityValues m n := ⟨A,hd,ha,rfl⟩
  have hsmem : ((m:ℝ)*n)*APPT.Quantum.purity A∈scaledAPPTPurities m n := ⟨A,hd,ha,rfl⟩
  have hsbound (x) (hx : x∈scaledAPPTPurities m n) : x≤U := by
    obtain ⟨B,hB,hp,rfl⟩ := hx
    exact density_appt_fixed_local_upper hm hn hB hp
  have hpbound (x) (hx : x∈apptPurityValues m n) : x≤U/((m:ℝ)*n) := by
    obtain ⟨B,hB,hp,rfl⟩ := hx
    apply (le_div_iff₀ hD).2
    simpa only [mul_comm, U] using density_appt_fixed_local_upper hm hn hB hp
  have hsbdd : BddAbove (scaledAPPTPurities m n) := ⟨U,hsbound⟩
  have hpbdd : BddAbove (apptPurityValues m n) := ⟨_,hpbound⟩
  apply le_antisymm
  · apply csSup_le ⟨_,hsmem⟩
    intro x hx
    obtain ⟨B,hB,hp,rfl⟩ := hx
    exact mul_le_mul_of_nonneg_left (le_csSup hpbdd ⟨B,hB,hp,rfl⟩) hD.le
  · have hle : apptPuritySup m n≤scaledAPPTPuritySup m n/((m:ℝ)*n) := by
      apply csSup_le ⟨_,hmem⟩
      intro x hx
      obtain ⟨B,hB,hp,rfl⟩ := hx
      apply (le_div_iff₀ hD).2
      simpa only [mul_comm, scaledAPPTPuritySup] using (le_csSup hsbdd
        (show ((m:ℝ)*n)*APPT.Quantum.purity B∈scaledAPPTPurities m n from ⟨B,hB,hp,rfl⟩))
    simpa only [mul_comm] using (le_div_iff₀ hD).1 hle

/-- The fixed-local purity-supremum asymptotic in the paper's normalization. -/
theorem appt_fixed_local_purity_sup_tendsto (m : ℕ) (hm : 2≤m) :
    Tendsto (fun n : ℕ => ((m:ℝ)*n)*apptPuritySup m n) atTop
      (𝓝 ((m:ℝ)^2/((m:ℝ)^2-1))) := by
  apply Filter.Tendsto.congr' _ (appt_fixed_local_scaled_sup_tendsto m hm)
  filter_upwards [eventually_ge_atTop (2*m)] with n hn
  exact scaled_sup_eq_dimension_mul_purity_sup hm hn

/-- The fixed-local first excess-purity coefficient, in the natural
dimension-scaled normalization.  This is the direct consequence of the
scaled supremum limit after subtracting the maximally mixed baseline. -/
theorem appt_fixed_local_excess_sup_tendsto (m : ℕ) (hm : 2≤m) :
    Tendsto (fun n : ℕ => ((m:ℝ)*n) *
      (apptPuritySup m n - 1/((m:ℝ)*n))) atTop
      (𝓝 (1/((m:ℝ)^2-1))) := by
  have hsub := (appt_fixed_local_purity_sup_tendsto m hm).sub_const (1 : ℝ)
  have hvalue : (m:ℝ)^2/((m:ℝ)^2-1)-1 = 1/((m:ℝ)^2-1) := by
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hden : (m:ℝ)^2-1 ≠ 0 := by nlinarith
    field_simp [hden]
    ring
  rw [← hvalue]
  apply Filter.Tendsto.congr' _ hsub
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hmR : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  field_simp [ne_of_gt hmR, ne_of_gt hnR]

end APPTReview

namespace APPTReview

/-- The physical purity objective is nonnegative and at most one for every density matrix. -/
theorem density_purity_unit_interval {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    {A : Matrix (a × b) (a × b) ℂ} (hρ : APPT.Quantum.IsDensity A) :
    0≤APPT.Quantum.purity A ∧ APPT.Quantum.purity A≤1 := by
  let f := hρ.1.isHermitian.eigenvalues₀
  have hn (i) : 0≤f i := by
    have hi := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hi
  have hs : (∑ i, f i)=1 := ordered_eigenvalues_sum hρ.1.isHermitian hρ.2
  have hu (i) : f i≤1 := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hn j) (Finset.mem_univ i)
    rwa [hs] at hh
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _),?_⟩
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    show (f i)^2≤f i by nlinarith [hn i, hu i])
  exact hh.trans hs.le

/-- The unscaled physical objective set is nonempty and bounded; the supremum
is not being assigned a value through the empty-set or unbounded-set convention. -/
theorem appt_purity_values_nonempty_bounded {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    (apptPurityValues m n).Nonempty ∧ BddAbove (apptPurityValues m n) := by
  obtain ⟨A,hd,ha,_,_⟩ := exists_appt_fixed_local_lower hm hmn
  refine ⟨⟨_,A,hd,ha,rfl⟩,⟨1,?_⟩⟩
  intro x hx
  obtain ⟨B,hB,hp,rfl⟩ := hx
  exact (density_purity_unit_interval hB).2

end APPTReview
