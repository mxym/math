import ContinuumGeometric.RoutingGeometry
import ContinuumGeometric.PeriodicRepair

/-!
Measured stable-center boundary costs for the ACTUAL `NoGridBoundary`
predicate.  The left boundary is allowed and the right boundary is excluded;
the bad centers therefore form left half-open strips of length R.
-/
namespace ContinuumGeometric

open Set MeasureTheory
open scoped ENNReal

def gridBoundaryBad (N : ℕ) (R : ℝ) : Set ℝ :=
  {x | ¬ NoGridBoundary N x R}

def gridBoundaryStable (N : ℕ) (R : ℝ) : Set ℝ :=
  {x | NoGridBoundary N x R}

noncomputable def gridBoundaryCore (N : ℕ) (R : ℝ) : Set ℝ :=
  ⋃ j ∈ Finset.Ico 0 (N : ℤ), Ico ((j : ℝ) / N - R) ((j : ℝ) / N)

theorem mem_gridBoundaryBad_iff (N : ℕ) (R x : ℝ) :
    x ∈ gridBoundaryBad N R ↔ ∃ b : ℤ, x ∈ Ico ((b : ℝ) / N - R) ((b : ℝ) / N) := by
  classical
  simp only [gridBoundaryBad, NoGridBoundary, mem_setOf_eq, not_forall, not_not]
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, ?_⟩ <;>
    constructor <;> linarith [hb.1, hb.2]

theorem gridBoundaryBad_eq_iUnion (N : ℕ) (R : ℝ) :
    gridBoundaryBad N R = ⋃ b : ℤ, Ico ((b : ℝ) / N - R) ((b : ℝ) / N) := by
  ext x
  simp only [mem_gridBoundaryBad_iff, mem_iUnion]

theorem gridBoundary_div_decomposition (N : ℕ) (hN : 0 < N) (b : ℤ) :
    (b : ℝ) / N = ((b % (N : ℤ) : ℤ) : ℝ) / N + ((b / (N : ℤ) : ℤ) : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : b % (N : ℤ) + (N : ℤ) * (b / (N : ℤ)) = b := by
    rw [Int.emod_def]
    ring
  have hr : ((b % (N : ℤ) : ℤ) : ℝ) + (N : ℝ) * ((b / (N : ℤ) : ℤ) : ℝ) = b := by
    exact_mod_cast hi
  field_simp
  nlinarith

/-- Canonical strips and integer periodization account for every lifted
boundary, including negative lifts and wraps across zero. -/
theorem gridBoundaryBad_eq_integerPeriodization (N : ℕ) (hN : 0 < N) (R : ℝ) :
    gridBoundaryBad N R = integerPeriodization (gridBoundaryCore N R) := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (mem_gridBoundaryBad_iff N R x).1 hx
    refine mem_iUnion.2 ⟨-(b / (N : ℤ)), mem_iUnion₂.2 ⟨b % (N : ℤ), ?_, ?_⟩⟩
    · exact Finset.mem_Ico.2 ⟨Int.emod_nonneg _ (by exact_mod_cast hN.ne'),
        Int.emod_lt_of_pos _ (by exact_mod_cast hN)⟩
    · have hdecomp := gridBoundary_div_decomposition N hN b
      simp only [mem_Ico, Int.cast_neg]
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj, hcell⟩ := mem_iUnion₂.1 hn
    apply (mem_gridBoundaryBad_iff N R x).2
    refine ⟨j - (N : ℤ) * n, ?_⟩
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hshift : ((j - (N : ℤ) * n : ℤ) : ℝ) / N = (j : ℝ) / N - n := by
      push_cast
      field_simp
    rw [hshift]
    exact ⟨by linarith [hcell.1], by linarith [hcell.2]⟩

theorem measurableSet_gridBoundaryBad (N : ℕ) (R : ℝ) :
    MeasurableSet (gridBoundaryBad N R) := by
  rw [gridBoundaryBad_eq_iUnion]
  exact MeasurableSet.iUnion fun _ => measurableSet_Ico

theorem onePeriodic_gridBoundaryBad (N : ℕ) (hN : 0 < N) (R : ℝ) :
    OnePeriodic (gridBoundaryBad N R) := by
  rw [gridBoundaryBad_eq_integerPeriodization N hN R]
  exact onePeriodic_integerPeriodization _

theorem gridBoundaryStable_eq_compl (N : ℕ) (R : ℝ) :
    gridBoundaryStable N R = (gridBoundaryBad N R)ᶜ := by
  ext x
  simp [gridBoundaryStable, gridBoundaryBad]

theorem measurableSet_gridBoundaryStable (N : ℕ) (R : ℝ) :
    MeasurableSet (gridBoundaryStable N R) := by
  rw [gridBoundaryStable_eq_compl]
  exact (measurableSet_gridBoundaryBad N R).compl

theorem onePeriodic_gridBoundaryStable (N : ℕ) (hN : 0 < N) (R : ℝ) :
    OnePeriodic (gridBoundaryStable N R) := by
  rw [gridBoundaryStable_eq_compl]
  intro x
  exact not_congr (onePeriodic_gridBoundaryBad N hN R x)

/-- Exact boundary cost N*R; no factor two or endpoint loss is required. -/
theorem unitDensity_gridBoundaryBad_le (N : ℕ) (hN : 0 < N) (R : ℝ) :
    unitDensity (gridBoundaryBad N R) ≤ ENNReal.ofReal ((N : ℝ) * R) := by
  rw [gridBoundaryBad_eq_integerPeriodization N hN R]
  calc
    unitDensity (integerPeriodization (gridBoundaryCore N R)) ≤ volume (gridBoundaryCore N R) :=
      unitDensity_integerPeriodization_le _
        (MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ico)
    _ ≤ ∑ j ∈ Finset.Ico 0 (N : ℤ), volume (Ico ((j : ℝ) / N - R) ((j : ℝ) / N)) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((N : ℝ) * R) := by
      simp only [Real.volume_Ico, sub_sub_cancel, Finset.sum_const, Int.card_Ico,
        sub_zero, Int.toNat_natCast]
      rw [← ENNReal.ofReal_nsmul, nsmul_eq_mul]

theorem unitDensity_iUnion_gridBoundaryBad_le {ι : Type*} [Fintype ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (R : ι → ℝ) :
    unitDensity (⋃ i, gridBoundaryBad (N i) (R i)) ≤
      ∑ i, ENNReal.ofReal ((N i : ℝ) * R i) := by
  unfold unitDensity
  rw [iUnion_inter]
  calc
    volume (⋃ i, gridBoundaryBad (N i) (R i) ∩ Ico 0 1) ≤
        ∑' i, volume (gridBoundaryBad (N i) (R i) ∩ Ico 0 1) := measure_iUnion_le _
    _ = ∑ i, unitDensity (gridBoundaryBad (N i) (R i)) := tsum_fintype _
    _ ≤ ∑ i, ENNReal.ofReal ((N i : ℝ) * R i) :=
      Finset.sum_le_sum fun i _ => unitDensity_gridBoundaryBad_le (N i) (hN i) (R i)

noncomputable def stableDyadicRadius (b g : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((b + g : ℕ) : ℤ))

/-- The predecessor scale cancels exactly from the boundary cost. -/
theorem dyadic_gridBoundary_cost (b g : ℕ) :
    (((2 : ℕ) ^ (b + 3) : ℕ) : ℝ) * stableDyadicRadius b g =
      (2 : ℝ) ^ ((3 : ℤ) - (g : ℤ)) := by
  simp only [stableDyadicRadius, Nat.cast_pow, Nat.cast_ofNat]
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

theorem unitDensity_dyadic_gridBoundaryBad_le (b g : ℕ) :
    unitDensity (gridBoundaryBad (2 ^ (b + 3)) (stableDyadicRadius b g)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((3 : ℤ) - (g : ℤ))) := by
  simpa only [dyadic_gridBoundary_cost] using unitDensity_gridBoundaryBad_le
    (2 ^ (b + 3)) (pow_pos (by decide) _) (stableDyadicRadius b g)

def routingStableCenters {ι : Type*} (b₀ : ι → ℕ) (g : ℕ) : Set ℝ :=
  {x | ∀ e, NoGridBoundary (2 ^ (b₀ e + 3)) x (stableDyadicRadius (b₀ e) g)}

noncomputable def routingUnstableCenters {ι : Type*} (b₀ : ι → ℕ) (g : ℕ) : Set ℝ :=
  ⋃ e, gridBoundaryBad (2 ^ (b₀ e + 3)) (stableDyadicRadius (b₀ e) g)

theorem routingStableCenters_eq_compl {ι : Type*} (b₀ : ι → ℕ) (g : ℕ) :
    routingStableCenters b₀ g = (routingUnstableCenters b₀ g)ᶜ := by
  classical
  ext x
  simp [routingStableCenters, routingUnstableCenters, gridBoundaryBad]

theorem measurableSet_routingUnstableCenters {ι : Type*} [Countable ι]
    (b₀ : ι → ℕ) (g : ℕ) : MeasurableSet (routingUnstableCenters b₀ g) := by
  exact MeasurableSet.iUnion fun _ => measurableSet_gridBoundaryBad _ _

theorem onePeriodic_routingUnstableCenters {ι : Type*} (b₀ : ι → ℕ) (g : ℕ) :
    OnePeriodic (routingUnstableCenters b₀ g) := by
  intro x
  simp only [routingUnstableCenters, mem_iUnion]
  exact exists_congr fun e => onePeriodic_gridBoundaryBad _ (pow_pos (by decide) _)
    (stableDyadicRadius (b₀ e) g) x

theorem measurableSet_routingStableCenters {ι : Type*} [Countable ι]
    (b₀ : ι → ℕ) (g : ℕ) : MeasurableSet (routingStableCenters b₀ g) := by
  rw [routingStableCenters_eq_compl]
  exact (measurableSet_routingUnstableCenters b₀ g).compl

theorem onePeriodic_routingStableCenters {ι : Type*} (b₀ : ι → ℕ) (g : ℕ) :
    OnePeriodic (routingStableCenters b₀ g) := by
  rw [routingStableCenters_eq_compl]
  intro x
  exact not_congr (onePeriodic_routingUnstableCenters b₀ g x)

/-- Exact finite-edge instability cost for any actual predecessor-scale
vector b₀.  The vector remains an input; the measure bound is proved here. -/
theorem unitDensity_routingUnstableCenters_le {ι : Type*} [Fintype ι]
    (b₀ : ι → ℕ) (g : ℕ) :
    unitDensity (routingUnstableCenters b₀ g) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 : ℝ) ^ ((3 : ℤ) - (g : ℤ))) := by
  calc
    unitDensity (routingUnstableCenters b₀ g) ≤
        ∑ e, ENNReal.ofReal ((((2 : ℕ) ^ (b₀ e + 3) : ℕ) : ℝ) * stableDyadicRadius (b₀ e) g) :=
      unitDensity_iUnion_gridBoundaryBad_le _ (fun _ => pow_pos (by decide) _) _
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 : ℝ) ^ ((3 : ℤ) - (g : ℤ))) := by
      simp only [dyadic_gridBoundary_cost, Finset.sum_const, Finset.card_univ]
      rw [← ENNReal.ofReal_nsmul, nsmul_eq_mul]

theorem unitDensity_routingStable_compl_le {ι : Type*} [Fintype ι]
    (b₀ : ι → ℕ) (g : ℕ) :
    unitDensity (routingStableCenters b₀ g)ᶜ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 : ℝ) ^ ((3 : ℤ) - (g : ℤ))) := by
  rw [routingStableCenters_eq_compl, compl_compl]
  exact unitDensity_routingUnstableCenters_le b₀ g

end ContinuumGeometric
