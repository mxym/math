import ErdosSimilarityGrowingGaps.RoutingSampleMap
import ErdosSimilarityGrowingGaps.SequenceTransfer

namespace ErdosSimilarityGrowingGaps

open Set

/-!
Concrete first-ge transfer lemmas for a filled late annulus.  The hypotheses
are exactly the finite routing guards: every tested integer starts after the
annulus origin, its `D`-buffer stays inside the annulus, and the activation or
point margin absorbs that buffer.  No density or routing probability premise is
used here.
-/

/-- The first logarithmic sample has the required two-sided `D` bounds at every
integer test in the annulus. -/
theorem filled_firstGe_sample_bounds
    {Z : LogScale} {U R D : ℝ}
    (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ)
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U) :
    ∀ n : ℕ, n ∈ tests →
      (n : ℝ) ≤ Z.z (firstGeIndex Z (n : ℝ)) ∧
      Z.z (firstGeIndex Z (n : ℝ)) ≤ (n : ℝ) + D := by
  intro n hn
  have hU : 0 ≤ U := hfill.1.le
  have hRU : 0 < R := by linarith
  have hdiv : U / R ≤ U := by
    apply (div_le_iff₀ hRU).2
    nlinarith
  obtain ⟨m, hmlo, hmhi⟩ := hfill.sample_mem
    (hlo n hn) (hhi n hn)
  exact ⟨(firstGeIndex_spec Z (n : ℝ)).1,
    firstGeIndex_value_le_of_mem Z (n : ℝ) D m ⟨hmlo, hmhi⟩⟩

/-- Activation transfer for the first-ge sample map.  The endpoint equalities
are retained as non-strict bounds, while activation itself remains strict. -/
theorem filled_firstGe_sequence_activation
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    (hmargin : ∀ n : ℕ, n ∈ tests → ∀ e : Fin W,
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ))) :
    ∀ n : ℕ, n ∈ tests → ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ windowActivations n k windows →
      p ∈ sequenceWindowActivations Z (sample n) k windows := by
  intro n hn p hp
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hp
  have hbounds := filled_firstGe_sample_bounds hfill hR tests hlo hhi n hn
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by
    rw [hsample]
  rw [hsamp]
  exact sequence_activation_of_sample_interval windows e D p hK he
    hbounds.1 hbounds.2 (hmargin n hn e p he)

/-- Point transfer for the same first-ge sample map.  The ideal dyadic point
is rewritten exactly as `2 ^ (-(n : ℝ))`, so no approximation premise is
hidden in this bridge. -/
theorem filled_firstGe_sequence_point_transfer
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    {G : Set ℝ} (ρ : ℝ)
    (hwidth : ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      |p.2.1 * ((2 : ℝ) ^ k)| *
          ((2 : ℝ) ^ (-((n : ℝ) * p.1.1)) -
            (2 : ℝ) ^ (-(((n : ℝ) + D) * p.1.1))) < ρ) :
    ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G := by
  intro n hn x p hideal
  have hbounds := filled_firstGe_sample_bounds hfill hR tests hlo hhi n hn
  have hsamp : sample n = firstGeIndex Z (n : ℝ) := by rw [hsample]
  rw [hsamp]
  have hdyadic : dyadic n = (2 : ℝ) ^ (-(n : ℝ)) := by
    unfold dyadic
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
    simp
  have hideal' := hideal
  rw [hdyadic] at hideal'
  apply powerPoint_mem_thickening_of_z_bounds hK
    (by linarith [hfill.2.2.1]) hbounds.1 hbounds.2 (by positivity)
    hideal'
  simpa only [neg_mul] using hwidth n hn x p hideal

/-- A lower bound on all prior logarithms forces first-ge samples into the
requested input tail.  This is the explicit index-tail guard needed when the
logarithmic test coordinate is not itself a sequence index. -/
theorem firstGe_image_tail_of_prefix_bound
    {Z : LogScale} (tests : Finset ℕ) (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (N : ℕ)
    (hprefix : ∀ n : ℕ, n ∈ tests →
      ∀ m : ℕ, m < N → Z.z m < (n : ℝ)) :
    ∀ n : ℕ, n ∈ tests.image sample → N ≤ n := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn
  have hsamp : sample m = firstGeIndex Z (m : ℝ) := by rw [hsample]
  rw [hsamp]
  by_contra hN
  have hlt : firstGeIndex Z (m : ℝ) < N := Nat.lt_of_not_ge hN
  exact (not_lt_of_ge (firstGeIndex_spec Z (m : ℝ)).1)
    (hprefix m hm (firstGeIndex Z (m : ℝ)) hlt)

/-! A single conjunction with exactly the three transfer fields consumed by
`UniformPowerTransferSpec`.  The density/error fields remain independent
finite-routing obligations. -/
theorem filled_firstGe_transfer_subfields
    {Z : LogScale} {K : ℕ} (hK : 2 ≤ K)
    {U R D : ℝ} (hfill : FillsAnnulus Z U R D) (hR : 2 ≤ R)
    (tests : Finset ℕ) {k : ℤ} {W : ℕ}
    (windows : Fin W → ℝ × ℝ)
    (sample : ℕ → ℕ)
    (hsample : sample = fun n : ℕ => firstGeIndex Z (n : ℝ))
    (hlo : ∀ n : ℕ, n ∈ tests → U / R ≤ (n : ℝ))
    (hhi : ∀ n : ℕ, n ∈ tests → (n : ℝ) + D ≤ R * U)
    (hmargin : ∀ n : ℕ, n ∈ tests → ∀ e : Fin W,
      ∀ p : PowerParams (1 / (K : ℝ)) K,
      p ∈ powerActivation n k (windows e).1 (windows e).2 →
      p.1.1 * D < (windows e).2 -
        (p.1.1 * (n : ℝ) - (k : ℝ)))
    {G : Set ℝ} (ρ : ℝ)
    (hwidth : ∀ n : ℕ, n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      |p.2.1 * ((2 : ℝ) ^ k)| *
          ((2 : ℝ) ^ (-((n : ℝ) * p.1.1)) -
            (2 : ℝ) ^ (-(((n : ℝ) + D) * p.1.1))) < ρ)
    (N : ℕ)
    (hprefix : ∀ n : ℕ, n ∈ tests →
      ∀ m : ℕ, m < N → Z.z m < (n : ℝ)) :
    (∀ n : ℕ, n ∈ tests →
      ∀ p : PowerParams (1 / (K : ℝ)) K,
        p ∈ windowActivations n k windows →
        p ∈ sequenceWindowActivations Z (sample n) k windows) ∧
    (∀ (n : ℕ), n ∈ tests → ∀ (x : ℝ)
      (p : PowerParams (1 / (K : ℝ)) K),
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∈ G →
      powerPoint (input Z (sample n)) ((2 : ℝ) ^ k) (x, p) ∈
        Metric.thickening ρ G) ∧
    (∀ n : ℕ, n ∈ tests.image sample → N ≤ n) := by
  have hA := filled_firstGe_sequence_activation hK hfill hR tests windows sample
      hsample hlo hhi hmargin
  have hB := filled_firstGe_sequence_point_transfer hK hfill hR tests windows sample
      hsample hlo hhi ρ hwidth
  have hC := firstGe_image_tail_of_prefix_bound tests sample hsample N hprefix
  exact And.intro hA (And.intro hB hC)

end ErdosSimilarityGrowingGaps
