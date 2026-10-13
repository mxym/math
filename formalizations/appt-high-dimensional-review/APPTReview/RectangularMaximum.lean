import APPTReview.PhysicalCut
import APPTReview.OuterCutBound
import APPTReview.RectangularCutoff
import APPTReview.FixedLocalLimit

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The complete two-branch outer upper bound follows from actual density and
all-global-unitary APPT, with no caller-supplied spectral cut or shape hypothesis. -/
theorem density_appt_two_branch_upper {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    APPT.Quantum.purity A ≤ max (outerSpikePurity m n) (roundedPlateauPurity m n) := by
  let D := Fintype.card (Fin m × Fin n)
  let R := Fintype.card (UpperPair m)
  have hcard : 2*R+m=m*m := upperPair_card m
  have hplace : 2*R+m ≤ D := pairPlacementBound hmn
  have hR : 0 < R := by nlinarith
  let r : Fin D := ⟨R-1,by omega⟩
  let q : Fin D := ⟨D-R-m-1,by omega⟩
  have hr : r.val+1=R := by dsimp [r];omega
  have hq : q.val+1+R+m=D := by dsimp [q];omega
  have hrq : r ≤ q := by change R-1 ≤ D-R-m-1;omega
  have hcut := density_appt_ordered_prefix_cut hm hmn hρ happt r q hr hq
  have hn (i : Fin D) : 0 ≤ hρ.1.isHermitian.eigenvalues₀ i := by
    have h := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using h
  have hupper := ordered_rectangular_cut_upper hm hmn
    (show D=m*n by simp [D]) r q hrq (by omega) (by omega)
    hρ.1.isHermitian.eigenvalues₀ hρ.1.isHermitian.eigenvalues₀_antitone hn
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) hcut
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  exact hupper

theorem rectangular_cutoff_implies_dimensions {m n : ℕ} (hm : 3 ≤ m)
    (hcut : m^3-m-2 ≤ n) : m ≤ n := by
  have h1 := Nat.mul_le_mul_left m hm
  have h2 := Nat.mul_le_mul_left (m*m) hm
  have hlarge : 2*m+2 ≤ m^3 := by nlinarith
  omega

/-- The rounded scalar value is exactly the original normalized quantum purity formula. -/
theorem roundedPlateauPurity_formula {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    let t := ((m-1)*n+1)/2
    roundedPlateauPurity m n=
      ((m:ℝ)*n*((m:ℝ)-1)^2+4*m*t)/((m:ℝ)*n*((m:ℝ)-1)+2*t)^2 := by
  dsimp only
  have hmP : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnP : (0:ℝ) < n := by exact_mod_cast hn
  unfold roundedPlateauPurity plateauScaledPurity plateauDenominator
  field_simp

/-- Actual APPT attainment of the rounded plateau value, as a member of the
physical purity objective set. -/
theorem roundedPlateauPurity_mem {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    roundedPlateauPurity m n ∈ apptPurityValues m n := by
  obtain ⟨A,hA,happt,hp⟩ := exists_broad_plateau hm hmn
  refine ⟨A,hA,happt,?_⟩
  rw [roundedPlateauPurity_formula hm (by omega),hp]
  rfl

/-- The exact unrestricted APPT purity maximum in the rectangular region.
The state set and objective are the original quantum ones; both its upper bound
and actual attainment are proved. This statement alone does not classify equality. -/
theorem appt_rectangular_purity_isGreatest {m n : ℕ} (hm : 3 ≤ m)
    (hcut : m^3-m-2 ≤ n) :
    IsGreatest (apptPurityValues m n) (roundedPlateauPurity m n) := by
  have hmn := rectangular_cutoff_implies_dimensions hm hcut
  refine ⟨roundedPlateauPurity_mem (by omega) hmn,?_⟩
  intro x hx
  obtain ⟨A,hA,happt,rfl⟩ := hx
  have h := density_appt_two_branch_upper hm hmn hA happt
  rwa [max_eq_right (outerSpike_lt_roundedPlateau hm hmn hcut).le] at h

/-- The exact finite formula, with the ceiling rank and original matrix semantics. -/
theorem appt_rectangular_maximum_formula {m n : ℕ} (hm : 3 ≤ m)
    (hcut : m^3-m-2 ≤ n) :
    let t := ((m-1)*n+1)/2
    IsGreatest (apptPurityValues m n)
      (((m:ℝ)*n*((m:ℝ)-1)^2+4*m*t)/((m:ℝ)*n*((m:ℝ)-1)+2*t)^2) := by
  have hmn := rectangular_cutoff_implies_dimensions hm hcut
  have h := appt_rectangular_purity_isGreatest hm hcut
  rwa [roundedPlateauPurity_formula (by omega) (by omega)] at h

theorem appt_rectangular_purity_sup_eq {m n : ℕ} (hm : 3 ≤ m)
    (hcut : m^3-m-2 ≤ n) : apptPuritySup m n=roundedPlateauPurity m n := by
  exact (appt_rectangular_purity_isGreatest hm hcut).csSup_eq

end APPTReview
