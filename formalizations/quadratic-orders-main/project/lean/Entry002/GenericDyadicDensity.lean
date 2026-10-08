import Entry002.ArithmeticInterface
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# Actual dyadic prime batches from A5

The positive asymptotic density in `ArithmeticInterface.density` implies a
uniform lower bound for every sufficiently large dyadic batch. All batch
members are the actual primes in `SignedResidueData.primes`. No walk or start
point enters the threshold. The density itself remains an explicit arithmetic
input; this file does not assert its supply for arbitrary quadratic orders.

The pure `thin_bins` proof below is reused verbatim from OpenAI family028,
GaussianMoat/BatchCertificate.lean lines 151--170, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (https://github.com/openai/math),
Apache-2.0; see ../../upstream-028/LICENSE. Its namespace and imports are
adapted. The generic Chebyshev cap is also replayed verbatim from
GaussianMoat/DenseBins.lean lines 28--38. All other proofs are new.
-/
set_option autoImplicit false

namespace Entry002
open Filter Module
open scoped BigOperators Topology Classical

/-- Actual finite prime batch in the closed dyadic interval. -/
noncomputable def dyadicPrimeBatch (P : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2*(2:ℝ)^j⌋₊+1)).filter
    (fun p => p ∈ P ∧ (2:ℝ)^j ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*(2:ℝ)^j)

@[simp] theorem dyadicPrimeBatch_card (P : Set ℕ) (j : ℕ) :
    (dyadicPrimeBatch P j).card = dyadicPrimeCount P ((2:ℝ)^j) := rfl

@[simp] theorem mem_dyadicPrimeBatch (P : Set ℕ) (j p : ℕ) :
    p ∈ dyadicPrimeBatch P j ↔ p ∈ P ∧ (2:ℝ)^j ≤ (p:ℝ) ∧ (p:ℝ) ≤ (2:ℝ)^(j+1) := by
  classical
  simp only [dyadicPrimeBatch, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hP, hlo, hhi⟩
    exact ⟨hP, hlo, by simpa only [pow_succ, mul_comm] using hhi⟩
  · rintro ⟨hP, hlo, hhi⟩
    have hupper : (p:ℝ) ≤ 2*(2:ℝ)^j := by
      simpa only [pow_succ, mul_comm] using hhi
    exact ⟨by have hh := Nat.le_floor hupper; omega, hP, hlo, hupper⟩

/-- Every selected member is an actual prime, with its actual dyadic bounds. -/
theorem dyadicPrimeBatch_prime_bounds {L : Type*} [AddCommGroup L]
    (data : SignedResidueData L) (j : ℕ) :
    ∀ p ∈ dyadicPrimeBatch data.primes j,
      Nat.Prime p ∧ (2:ℝ)^j ≤ (p:ℝ) ∧ (p:ℝ) ≤ (2:ℝ)^(j+1) := by
  intro p hp
  obtain ⟨hP, hlo, hhi⟩ := (mem_dyadicPrimeBatch _ _ _).mp hp
  exact ⟨data.prime_mem p hP, hlo, hhi⟩


/-- A finite actual prime set has its Chebyshev upper bound. -/
lemma prime_log_mass_le_theta (S : Finset ℕ) {U : ℝ} (hU : 0 ≤ U)
    (hp : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ U) :
    (∑ p ∈ S, Real.log p) ≤ Real.log 4*U := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hU)
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hpS
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.le_floor_iff hU).mpr (hp p hpS).2,(hp p hpS).1⟩
  · intro p hpS _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hpS).2.one_le)


/-- Actual dyadic batch log weight, uniformly bounded without density assumptions. -/
theorem dyadicPrimeBatch_log_weight_le {L : Type*} [AddCommGroup L]
    (data : SignedResidueData L) (j : ℕ) :
    (∑ p ∈ dyadicPrimeBatch data.primes j, Real.log (p : ℝ)) ≤
      Real.log 4 * (2 : ℝ) ^ (j + 1) := by
  apply prime_log_mass_le_theta _ (by positivity)
  intro p hp
  exact ⟨(dyadicPrimeBatch_prime_bounds data j p hp).1,
    (dyadicPrimeBatch_prime_bounds data j p hp).2.2⟩

/-- The two signs have total log weight at most a fixed multiple of the scale. -/
theorem dyadicPrimeBatch_signed_log_weight_le {L : Type*} [AddCommGroup L]
    (data : SignedResidueData L) (j : ℕ) :
    2 * (∑ p ∈ dyadicPrimeBatch data.primes j, Real.log (p : ℝ)) ≤
      (4 * Real.log 4) * (2 : ℝ) ^ j := by
  have h := mul_le_mul_of_nonneg_left (dyadicPrimeBatch_log_weight_le data j)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1; ring

/-- A batch satisfying a positive density lower bound is genuinely nonempty. -/
theorem dyadicPrimeBatch_nonempty_of_dense (P : Set ℕ) (j : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch P j).card) :
    (dyadicPrimeBatch P j).Nonempty := by
  have hlog : 0 < Real.log ((2:ℝ)^(j+1)) :=
    Real.log_pos (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : j+1≠0))
  have hpos : 0 < δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) := by positivity
  apply Finset.card_pos.mp
  exact_mod_cast hpos.trans_le hdense

/-- A5 gives a fixed positive density and fixed threshold, uniformly over all
sufficiently large dyadic bins. -/
theorem uniform_dyadic_density_of_tendsto (P : Set ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdensity : Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      atTop (nhds ρ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ j0 : ℕ, ∀ j ≥ j0,
      δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch P j).card := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hd := (hdensity.comp hp).eventually
    (eventually_gt_nhds (by linarith : ρ/2 < ρ))
  obtain ⟨j0, hj0⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and hd)
  refine ⟨ρ/2, by linarith, j0, ?_⟩
  intro j hj
  obtain ⟨hj1, hratio⟩ := hj0 j hj
  have hT : (0:ℝ) < (2:ℝ)^j := by positivity
  have hlog : 0 < Real.log ((2:ℝ)^j) :=
    Real.log_pos (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : j≠0))
  have hlogle : Real.log ((2:ℝ)^j) ≤ Real.log ((2:ℝ)^(j+1)) := by
    apply Real.log_le_log hT
    rw [pow_succ]
    nlinarith only [hT]
  have hmass := (le_div_iff₀ (div_pos hT hlog)).mp hratio.le
  have hsmall := div_le_div_of_nonneg_left
    (mul_nonneg (show (0:ℝ) ≤ ρ/2 by linarith) hT.le) hlog hlogle
  rw [dyadicPrimeBatch_card]
  calc
    _ ≤ (ρ/2)*(2:ℝ)^j / Real.log ((2:ℝ)^j) := hsmall
    _ ≤ _ := by simpa only [mul_div_assoc] using hmass

/-- The density field of the literal arithmetic interface supplies the uniform
batch estimate. The resulting δ and j0 do not depend on a walk or start. -/
theorem ArithmeticInterface.uniform_dyadic_density {L : Type*} [AddCommGroup L]
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ j0 : ℕ, ∀ j ≥ j0,
      δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card := by
  obtain ⟨ρ, hρ, hdensity⟩ := A.density
  exact uniform_dyadic_density_of_tendsto data.primes hρ hdensity

/-- Actual nonempty prime batches with their density and prime-size bounds,
all at one arithmetic threshold independent of walks and starts. -/
theorem ArithmeticInterface.uniform_dyadic_batches {L : Type*} [AddCommGroup L]
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ j0 : ℕ, ∀ j ≥ j0,
      (dyadicPrimeBatch data.primes j).Nonempty ∧
      (∀ p ∈ dyadicPrimeBatch data.primes j,
        Nat.Prime p ∧ (2:ℝ)^j ≤ (p:ℝ) ∧ (p:ℝ) ≤ (2:ℝ)^(j+1)) ∧
      δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card := by
  obtain ⟨δ, hδ, j0, hdense⟩ := A.uniform_dyadic_density
  exact ⟨δ, hδ, j0, fun j hj =>
    ⟨dyadicPrimeBatch_nonempty_of_dense _ j hδ (hdense j hj),
      dyadicPrimeBatch_prime_bounds data j, hdense j hj⟩⟩

theorem thin_bins (J : Finset ℕ) {K : ℕ} (hK : 0<K) :
    ∃ a<K, ((J.card:ℝ)/K)≤(J.filter (fun j => j%K=a)).card ∧
      ∀ i∈J.filter (fun j => j%K=a), ∀ j∈J.filter (fun j => j%K=a),
        i<j → i+K≤j := by
  have hh : (Finset.range K).card • ((J.card:ℝ)/K)≤(J.card:ℝ) := by
    rw [Finset.card_range,nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hK.ne')]
  obtain ⟨a,ha,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := J) (t := Finset.range K) (f := fun j => j%K)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hK))
    (Finset.nonempty_range_iff.mpr hK.ne') hh
  refine ⟨a,Finset.mem_range.mp ha,hc,?_⟩
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hd : i%K=j%K := hi'.trans hj'.symm
  have hei := Nat.mod_add_div i K
  have hej := Nat.mod_add_div j K
  have hq : i/K<j/K := by nlinarith only [hei,hej,hd,hij]
  nlinarith only [hei,hej,hd,hq]


/-- A concrete family of dyadic bins in a narrow logarithmic window. -/
noncomputable def dyadicLogWindow (X : ℝ) : Finset ℕ :=
  Finset.Ico ⌈X / Real.log 2⌉₊
    (⌈X / Real.log 2⌉₊ + ⌊X / (40 * Real.log 2)⌋₊)

/-- The window contains linearly many bins, each with the actual narrow
logarithmic bounds needed by the separated schedule construction. -/
theorem dyadicLogWindow_bounds {X : ℝ} (hX : 80 * Real.log 2 ≤ X) :
    X / (80 * Real.log 2) ≤ (dyadicLogWindow X).card ∧
    ∀ j ∈ dyadicLogWindow X,
      X ≤ (j : ℝ) * Real.log 2 ∧ (j : ℝ) * Real.log 2 ≤ 21/20 * X := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 ≤ X := (by positivity : (0:ℝ) ≤ 80 * Real.log 2).trans hX
  have hdiv : 0 ≤ X / Real.log 2 := div_nonneg hx hl.le
  have hdiv40 : 0 ≤ X / (40 * Real.log 2) := div_nonneg hx (by positivity)
  constructor
  · have hfloor := Nat.lt_floor_add_one (X / (40 * Real.log 2))
    have hunit : 1 ≤ X / (80 * Real.log 2) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa using hX)
    have hscale : X / (40 * Real.log 2) = 2 * (X / (80 * Real.log 2)) := by
      field_simp
      ring
    rw [dyadicLogWindow, Nat.card_Ico, Nat.add_sub_cancel_left]
    linarith only [hfloor, hunit, hscale]
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
    have hloR : (⌈X / Real.log 2⌉₊ : ℝ) ≤ j := by exact_mod_cast hlo
    have hhiR : (j:ℝ) < (⌈X / Real.log 2⌉₊ : ℝ) +
        (⌊X / (40 * Real.log 2)⌋₊ : ℝ) := by exact_mod_cast hhi
    have hceil := Nat.ceil_lt_add_one hdiv
    have hfloor := Nat.floor_le hdiv40
    constructor
    · have hh := mul_le_mul_of_nonneg_right ((Nat.le_ceil _).trans hloR) hl.le
      simpa only [div_mul_cancel₀ _ hl.ne'] using hh
    · have hjupper : (j:ℝ) ≤ X / Real.log 2 + 1 + X / (40 * Real.log 2) := by
        linarith only [hhiR, hceil, hfloor]
      have hh := mul_le_mul_of_nonneg_right hjupper hl.le
      have he : (X / Real.log 2 + 1 + X / (40 * Real.log 2)) * Real.log 2 =
          X + Real.log 2 + X / 40 := by field_simp
      rw [he] at hh
      nlinarith only [hh, hX, hx]

/-- Positive actual dyadic density yields linearly many separated dense batches
in every sufficiently large narrow logarithmic window. All selections here are
computed from the actual prime set; no batch certificate is assumed. -/
theorem separated_dyadic_batches_of_tendsto (P : Set ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdensity : Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      atTop (nhds ρ)) (K : ℕ) (hK : 0 < K) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∃ J : Finset ℕ,
        c * X ≤ J.card ∧
        (∀ i ∈ J, ∀ j ∈ J, i < j → i + K ≤ j) ∧
        ∀ j ∈ J,
          X ≤ (j:ℝ) * Real.log 2 ∧ (j:ℝ) * Real.log 2 ≤ 21/20 * X ∧
          δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch P j).card := by
  obtain ⟨δ, hδ, j0, hdense⟩ := uniform_dyadic_density_of_tendsto P hρ hdensity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  refine ⟨1 / (80 * Real.log 2 * K), δ, by positivity, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop (max (80 * Real.log 2) ((j0:ℝ) * Real.log 2))]
    with X hX
  have hwindow := dyadicLogWindow_bounds ((le_max_left _ _).trans hX)
  obtain ⟨a, _, hcard, hsep⟩ := thin_bins (dyadicLogWindow X) hK
  refine ⟨(dyadicLogWindow X).filter (fun j => j % K = a), ?_, hsep, ?_⟩
  · have hh := (div_le_div_of_nonneg_right hwindow.1 hKR.le).trans hcard
    have he : (1 / (80 * Real.log 2 * K)) * X = (X / (80 * Real.log 2)) / K := by
      field_simp
    rwa [he]
  · intro j hj
    have hjmem := (Finset.mem_filter.mp hj).1
    obtain ⟨hlo, hhi⟩ := hwindow.2 j hjmem
    have hstart := (le_max_right _ _).trans hX
    have hj0 : j0 ≤ j := by
      have hh : (j0:ℝ) ≤ j := (mul_le_mul_iff_left₀ hl).mp (hstart.trans hlo)
      exact_mod_cast hh
    exact ⟨hlo, hhi, hdense j hj0⟩

/-- The literal A5 interface provides a walk-independent separated dense-bin
schedule for every fixed positive separation. -/
theorem ArithmeticInterface.separated_dyadic_batches {L : Type*} [AddCommGroup L]
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    (K : ℕ) (hK : 0 < K) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∃ J : Finset ℕ,
        c * X ≤ J.card ∧
        (∀ i ∈ J, ∀ j ∈ J, i < j → i + K ≤ j) ∧
        ∀ j ∈ J,
          X ≤ (j:ℝ) * Real.log 2 ∧ (j:ℝ) * Real.log 2 ≤ 21/20 * X ∧
          δ * (2:ℝ)^j / Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card := by
  obtain ⟨ρ, hρ, hdensity⟩ := A.density
  exact separated_dyadic_batches_of_tendsto data.primes hρ hdensity K hK

end Entry002
