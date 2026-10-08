import Entry002.GenericResidueGrowth

/-!
# Finite growth against the actual shared-law information telescope

The final summation argument adapts upstream-028/GaussianMoat/BatchCertificate.lean
lines 111–148 (OpenAI math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Apache-2.0). The input is a genuine local selected-family rate on the one literal
common time law. The conclusion is conditional until those local rates and the
scalar multiscale excess have been instantiated. No Gaussian no-walk theorem is
imported or asserted for a general lattice.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- Successive actual increment-word charges of the selected families telescope
on one common time law. Costs are bounded by the preselected batches. -/
theorem actual_residue_growth_rate_bound
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (ns : List ℕ) (N n : ℕ) (len : ℕ → ℕ)
    (pool : Finset ℕ) (hpool : ∀ p ∈ pool, p ∈ data.primes)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ) (r : ℕ → ℝ)
    (hL : ∀ j ≤ n, 0 < len j) (hdiv : ∀ j < n, len j ∣ len (j+1))
    (hN : ∀ j < n, len (j+1) ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < len (j+1),
      2 * Real.binEntropy ((a : ℝ)/(N+1)) +
      ((a : ℝ)/(N+1)) * ((len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * residueGrowthWeight S (j+1)) ≤ ε)
    (hstep : ResidueGrowthStep data
      ((TimeLaw.at 0).advance (commonSchedule z ns N)) z len pool S bcap r n) :
    (∑ j ∈ Finset.range (n+1), r j) ≤
      Real.log (wordStepBall b e D).card + n * ε := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z ns N)
  obtain ⟨W⟩ := actual_residue_growth data Q z len pool hpool S bcap r n hstep
  have herrW : ∀ j < n, ∀ a < len (j+1),
      2 * Real.binEntropy ((a : ℝ)/(N+1)) +
      ((a : ℝ)/(N+1)) * ((len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * (W.family (j+1)).sum (fun i => Real.log i.1)) ≤ ε := by
    intro j hj a ha
    have hw := W.weight_le (j+1)
    have ht : 0 ≤ (a : ℝ)/(N+1) := div_nonneg (Nat.cast_nonneg _)
      (by positivity)
    have hmul := mul_le_mul_of_nonneg_left (show
      (len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * residueLabelWeight (W.family (j+1)) ≤
      (len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * residueGrowthWeight S (j+1) by linarith) ht
    have hbound := herr j hj a ha
    dsimp only [residueLabelWeight] at hmul
    linarith
  have htel := schedule_lattice_information_telescope b e data z D hs ns N n
    W.family W.prime_mem W.nested len hL hdiv hN hε herrW
  have hsum : (∑ j ∈ Finset.range (n+1), r j) ≤
      ∑ j ∈ Finset.range (n+1), residueWordCharge data Q z (len j)
        (W.family j) (W.family (j+1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact W.charge_le j (by have := Finset.mem_range.mp hj; omega)
  exact hsum.trans htel

/-- A finite contradiction from actual repeated family growth and a scalar
strict excess. The local-rate premise is explicit, rather than an assumption
of the contradiction or the no-walk theorem. -/
theorem finite_residue_growth_contradiction
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (ns : List ℕ) (N n : ℕ) (len : ℕ → ℕ)
    (pool : Finset ℕ) (hpool : ∀ p ∈ pool, p ∈ data.primes)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ) (r : ℕ → ℝ)
    (hL : ∀ j ≤ n, 0 < len j) (hdiv : ∀ j < n, len j ∣ len (j+1))
    (hN : ∀ j < n, len (j+1) ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < len (j+1),
      2 * Real.binEntropy ((a : ℝ)/(N+1)) +
      ((a : ℝ)/(N+1)) * ((len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * residueGrowthWeight S (j+1)) ≤ ε)
    (hstep : ResidueGrowthStep data
      ((TimeLaw.at 0).advance (commonSchedule z ns N)) z len pool S bcap r n)
    (hexcess : Real.log (wordStepBall b e D).card + n * ε <
      ∑ j ∈ Finset.range (n+1), r j) : False := by
  exact (not_lt_of_ge (actual_residue_growth_rate_bound b e data z D hs ns N n
    len pool hpool S bcap r hL hdiv hN hε herr hstep)) hexcess

/-- Choose terminal smoothing from the known batch budgets before selecting
any residue family. Thus the one common law is fixed before growth. -/
theorem exists_uniform_growth_smoothing_size
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (D : ℝ) (len : ℕ → ℕ) (n : ℕ) (S : ℕ → Finset ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (∀ j < n, len (j+1) ≤ N) ∧
      ∀ j < n, ∀ a < len (j+1),
        2 * Real.binEntropy ((a : ℝ)/(N+1)) +
        ((a : ℝ)/(N+1)) * ((len j : ℝ) * Real.log (wordStepBall b e D).card +
          2 * residueGrowthWeight S (j+1)) ≤ ε := by
  exact exists_common_block_smoothing_size len n (residueGrowthWeight S)
    (Real.log (wordStepBall b e D).card) hε

/-- Instantiate the scalar sum with the actual finite dyadic bins. The
multiscale rate lower bound is proved by `allBins_rate`, not assumed as a
replacement for the information telescope. -/
theorem finite_allBins_growth_contradiction
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (ns : List ℕ) (N n : ℕ) (len : ℕ → ℕ)
    (pool : Finset ℕ) (hpool : ∀ p ∈ pool, p ∈ data.primes)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ)
    (J : ℕ → Finset ℕ) (W : ℕ) {X c t : ℝ}
    (hX : 0 < X) (hc : 0 < c)
    (hb : ∀ w < W, ∀ j ∈ J w,
      (100 : ℝ)^w * X ≤ j * Real.log 2 ∧
      j * Real.log 2 ≤ 21/20 * ((100 : ℝ)^w * X))
    (hdense : ∀ w < W, t * ((100 : ℝ)^w * X) ≤ (J w).card)
    (hcard : (allBins W J).card = n+1)
    (hL : ∀ j ≤ n, 0 < len j) (hdiv : ∀ j < n, len j ∣ len (j+1))
    (hN : ∀ j < n, len (j+1) ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < len (j+1),
      2 * Real.binEntropy ((a : ℝ)/(N+1)) +
      ((a : ℝ)/(N+1)) * ((len j : ℝ) * Real.log (wordStepBall b e D).card +
        2 * residueGrowthWeight S (j+1)) ≤ ε)
    (hstep : ResidueGrowthStep data
      ((TimeLaw.at 0).advance (commonSchedule z ns N)) z len pool S bcap
      (fun j => c/(10000000*Real.log ((2 : ℝ)^(binEnum (allBins W J) j)))) n)
    (hexcess : Real.log (wordStepBall b e D).card + n * ε <
      (W : ℝ) * (c*t/10500000)) : False := by
  have hlower := allBins_rate J hX hc hb hdense
  have heq := binEnum_sum (allBins W J)
    (fun j => c/(10000000*Real.log ((2 : ℝ)^j)))
  rw [hcard] at heq
  rw [← heq] at hlower
  exact finite_residue_growth_contradiction b e data z D hs ns N n len pool
    hpool S bcap _ hL hdiv hN hε herr hstep (hexcess.trans_le hlower)

end Entry002

