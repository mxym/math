import ErdosSimilarityGrowingGaps.First

namespace ErdosSimilarityGrowingGaps
open Filter

/-- A local bound on consecutive gaps over one annulus. -/
def GapBoundOn (Z : LogScale) (U R D : ℝ) : Prop :=
  ∀ n : ℕ, U / R ≤ Z.z n → Z.z n ≤ R * U →
    Z.z (n + 1) - Z.z n ≤ D

/-- The first occupied point is already inside the first window of the
annulus.  This is the endpoint condition needed when no predecessor lies
inside the annulus. -/
def AnnulusAnchor (Z : LogScale) (U R D : ℝ) : Prop :=
  ∃ m : ℕ, U / R ≤ Z.z m ∧ Z.z m ≤ U / R + D

/-- Exact finite sampling lemma: an anchor plus a local gap bound fills every
closed interval of length `D` in the annulus. -/
theorem fillsAnnulus_of_anchor_gap
    {Z : LogScale} {U R D : ℝ}
    (hU : 0 < U) (hR : 2 ≤ R) (hD : 1 ≤ D)
    (hanchor : AnnulusAnchor Z U R D)
    (hgap : GapBoundOn Z U R D) :
    FillsAnnulus Z U R D := by
  refine ⟨hU, hR, hD, ?_⟩
  intro v hv hvD
  obtain ⟨n, hn, hmin⟩ := exists_first_ge Z v
  by_cases hle : Z.z n ≤ v + D
  · exact ⟨n, hn, hle⟩
  have hgt : v + D < Z.z n := lt_of_not_ge hle
  obtain ⟨m, hmlo, hmhi⟩ := hanchor
  have hmn : m ≤ n := by
    by_contra hmn
    have hnm : n < m := Nat.lt_of_not_ge hmn
    have hznm : Z.z n < Z.z m := Z.strictMono hnm
    linarith
  have hmnlt : m < n := by
    by_contra hmnlt
    have hmn_eq : m = n := Nat.le_antisymm hmn (Nat.le_of_not_gt hmnlt)
    subst hmn_eq
    linarith
  have hnpos : 0 < n := Nat.zero_lt_of_lt hmnlt
  have hprev_lt : Z.z (n - 1) < v := by
    apply hmin
    exact Nat.sub_lt (Nat.zero_lt_of_lt hmnlt) (by omega)
  have hm_prev : m ≤ n - 1 := by omega
  have hzmono : Z.z m ≤ Z.z (n - 1) :=
    Z.strictMono.monotone hm_prev
  have hprev_lo : U / R ≤ Z.z (n - 1) := hmlo.trans hzmono
  have hprev_hi : Z.z (n - 1) ≤ R * U := by
    have hvU : v ≤ R * U := by linarith
    exact hprev_lt.le.trans hvU
  have hbound := hgap (n - 1) hprev_lo hprev_hi
  have hindex : (n - 1) + 1 = n := by omega
  rw [hindex] at hbound
  linarith

/-- The local formulation is exactly the part of the paper's annular
sampling argument that is independent of the probabilistic blocker. -/
theorem fillsAnnulus_sample_mem
    {Z : LogScale} {U R D v : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) :
    ∃ n : ℕ, v ≤ Z.z n ∧ Z.z n ≤ v + D := by
  exact h.2.2.2 v hv hvD

end ErdosSimilarityGrowingGaps
