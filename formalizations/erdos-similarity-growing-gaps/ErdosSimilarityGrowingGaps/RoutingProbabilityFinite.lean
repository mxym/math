import ErdosSimilarityGrowingGaps.RoutingLaw
import ErdosSimilarityGrowingGaps.RoutingMeasure
import ErdosSimilarityGrowingGaps.RoutingModel
import ErdosSimilarityGrowingGaps.PowerCore
import ErdosSimilarityGrowingGaps.LocalSignatures
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

theorem routed_terminal_probability {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (address : (S → Bool) → T) :
    tableProbability p (fun ω => ω.terminals (address ω.selectors) = true) = p := by
  classical
  have hterminal (σ : S → Bool) :
      (∑ τ : T → Bool, bitTableWeight p τ *
        if τ (address σ) = true then (1 : ℝ) else 0) = p := by
    have h := weighted_distinct_reads (I := Unit) (fun _ => address σ)
      (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ b => bernoulliWeight p b) (fun _ => bernoulliWeight_sum p)
      (fun _ b => if b = true then 1 else 0)
    simpa [bitTableWeight, bernoulliWeight] using h
  unfold tableProbability
  have hinner (σ : S → Bool) :
      (∑ τ : T → Bool, bitTableWeight (1 / 2) σ * bitTableWeight p τ *
        if τ (address σ) = true then (1 : ℝ) else 0) = bitTableWeight (1 / 2) σ * p := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hterminal]
  have hsum : (∑ σ : S → Bool, ∑ τ : T → Bool,
    bitTableWeight (1 / 2) σ * bitTableWeight p τ *
      if τ (address σ) = true then (1 : ℝ) else 0) =
      ∑ σ : S → Bool, bitTableWeight (1 / 2) σ * p :=
    Finset.sum_congr rfl (fun σ _ => hinner σ)
  calc
    _ = (∑ σ : S → Bool, ∑ τ : T → Bool,
        bitTableWeight (1 / 2) σ * bitTableWeight p τ *
          if τ (address σ) = true then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      exact congrArg (fun z : ℝ => bitTableWeight (1 / 2) σ * bitTableWeight p τ * z)
        (ite_cond_congr rfl)
    _ = (∑ σ : S → Bool, bitTableWeight (1 / 2) σ * p) := hsum
    _ = p := by rw [← Finset.sum_mul, bitTableWeight_sum, one_mul]

theorem tableProbability_eq_finiteOutcomeProbability {S T : Type*}
    [Fintype S] [Fintype T] (p : ℝ) (E : FiniteRoutingTables S T → Prop) :
    tableProbability p E = finiteOutcomeProbability (finiteRoutingWeight p) E := by
  classical
  rw [tableProbability_eq_weight_sum]
  unfold finiteOutcomeProbability
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

/-- Exact law of the ACTUAL default-center exposure: one fair bit per selector
edge table, including every off-route table. -/
theorem actual_center_atom_probability {M d : ℕ} (c : RoutingTemplate M d)
    (hd : 0 < d) (p x : ℝ) (bits : SelectorEdge M d → Bool) :
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) =
      (1 / 2 : ℝ) ^ Fintype.card (SelectorEdge M d) := by
  classical
  rw [center_atom_probability]
  rw [Fintype.prod_sigma]
  have he (e : SelectorEdge M d) :
      (∏ a : Fin (2 ^ (c.selectorEnd e + 3)),
        exposureMass (actualCenterExposure c x bits ⟨e, a⟩)) = (1 / 2 : ℝ) := by
    have hpoint (a : Fin (2 ^ (c.selectorEnd e + 3))) :
        exposureMass (actualCenterExposure c x bits ⟨e, a⟩) =
          if a = gridAddress (c.selectorEnd e) x then (1 / 2 : ℝ) else 1 := by
      by_cases h : a = gridAddress (c.selectorEnd e) x <;>
        simp [actualCenterExposure, exposureMass, h]
    simp_rw [hpoint]
    simp
  simp_rw [he]
  simp

/-- Center exposure is the actual selector-key readout, not a conditioning
assumption about a globally chosen path. -/
theorem actual_center_atom_iff_reads {M d : ℕ} (c : RoutingTemplate M d)
    (x : ℝ) (bits : SelectorEdge M d → Bool) (σ : SelectorAddress c → Bool) :
    centerExposureAtom (actualCenterExposure c x bits) σ ↔
      ∀ e : SelectorEdge M d, σ (selectorAddress c e x) = bits e := by
  classical
  constructor
  · intro h e; exact centerExposure_reads c x bits σ h e
  · intro h s v hs
    have hkey : s.2 = gridAddress (c.selectorEnd s.1) x := by
      by_contra hn
      simp [actualCenterExposure, hn] at hs
    have hv : v = bits s.1 := by
      simpa [actualCenterExposure, hkey] using hs.symm
    rw [hv]
    have heq : s = selectorAddress c s.1 x := by
      cases s with
      | mk e a => simp_all [selectorAddress]
    rw [heq]
    exact h s.1

/-- All actual center atoms have total mass one. -/
theorem actual_center_atoms_sum_one {M d : ℕ} (c : RoutingTemplate M d)
    (hd : 0 < d) (p x : ℝ) :
    (∑ bits : SelectorEdge M d → Bool,
      tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors)) = 1 := by
  classical
  simp_rw [actual_center_atom_probability c hd p x]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- Actual routed points have the required Bernoulli marginal. -/
theorem actual_routedSet_probability {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p z : ℝ) :
    tableProbability p (fun ω => z ∈ routedSet c hM hd ω) = p :=
  routed_terminal_probability p (fun σ => terminalAddress c hd (routeLeaf c hM σ z) z)

/-- Fubini now applies to actual finite routing-table weights. -/
theorem actual_routedSet_expected_density {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hB : ∀ ω, MeasurableSet (routedSet c hM hd ω)) :
    expectedUnitDensity (finiteRoutingWeight p) (routedSet c hM hd) = ENNReal.ofReal p := by
  apply expectedUnitDensity_eq_of_probability_eq (finiteRoutingWeight p)
    (finiteRoutingWeight_nonneg p hp₀ hp₁) _ hB p
  intro z _
  rw [← tableProbability_eq_finiteOutcomeProbability]
  exact actual_routedSet_probability c hM hd p z

/-- The ACTUAL local-grid signature representatives give a joint continuum
union bound on each center atom. The route readout must factor through the
proved activation/grid vector; no measurability of the representatives is used. -/
theorem local_grid_continuum_joint_union_bound {S T : Type*} [Fintype S] [Fintype T]
    {P : ℕ} (p s₀ s₁ x : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hs : s₀ ≤ s₁)
    (indices u v b : Fin P → ℕ) (k : ℤ) (ell : ℕ)
    (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell)
    (exposed : S → Option Bool)
    (readout : FiniteRoutingTables S T → (Fin P → Option ℤ) → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hfixed : ∀ r : PowerParams s₀ s₁,
      tableProbability p (fun ω => centerExposureAtom exposed ω.selectors ∧
        readout ω (localGridVector x indices (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) r)) ≤
        tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) * ε) :
    tableProbability p (fun ω => centerExposureAtom exposed ω.selectors ∧
      ∃ r : PowerParams s₀ s₁, readout ω
        (localGridVector x indices (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) r)) ≤
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
        tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) * ε := by
  classical
  obtain ⟨reps, hcard, hrep⟩ := actual_local_representatives_entropy_bound
    s₀ s₁ x hs indices u v b k ell hspan
  let F := fun (r : PowerParams s₀ s₁) (ω : FiniteRoutingTables S T) =>
    centerExposureAtom exposed ω.selectors ∧ readout ω
      (localGridVector x indices (fun i => 2 ^ (b i + 3)) k
        (fun i => ((u i : ℝ), (v i : ℝ))) r)
  have hub := tableProbability_union_bound p hp₀ hp₁ reps
    (fun ω => centerExposureAtom exposed ω.selectors ∧ ∃ r : PowerParams s₀ s₁,
      readout ω (localGridVector x indices (fun i => 2 ^ (b i + 3)) k
        (fun i => ((u i : ℝ), (v i : ℝ))) r)) F (by
    intro ω hω
    obtain ⟨ha, r, hr⟩ := hω
    obtain ⟨r', hr', heq⟩ := hrep r
    exact ⟨r', hr', ha, by simpa only [heq] using hr⟩)
  apply hub.trans
  calc
    _ ≤ ∑ _r ∈ reps,
        tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) * ε := by
      apply Finset.sum_le_sum
      intro r _
      exact hfixed r
    _ = (reps.card : ℝ) *
        tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) * ε := by
      simp [mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hε
      apply mul_le_mul_of_nonneg_right _ (tableProbability_nonneg p hp₀ hp₁ _)
      exact_mod_cast hcard

end ErdosSimilarityGrowingGaps
