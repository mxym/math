import ErdosSimilarityGrowingGaps.FiniteRouting
import ErdosSimilarityGrowingGaps.Avoidance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

structure FiniteRoutingTables (S T : Type*) where
  selectors : S → Bool
  terminals : T → Bool

def centerExposureAtom {S : Type*} (exposed : S → Option Bool) (σ : S → Bool) : Prop :=
  ∀ (s : S) (v : Bool), exposed s = some v → σ s = v

def localRoutingSuccess {S T : Type*} {m : ℕ}
    (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (ω : FiniteRoutingTables S T) (i : Fin m) : Prop :=
  ω.selectors (own i) = true ∧ ω.terminals (terminal ω.selectors i) = true

def localRoutingAllMiss {S T : Type*} {m : ℕ}
    (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (ω : FiniteRoutingTables S T) : Prop :=
  ∀ i : Fin m, ¬localRoutingSuccess own terminal ω i

def LocalAddressSeparation {S T : Type*} {m : ℕ}
    (exposed : S → Option Bool) (own : Fin m → S)
    (terminal : (S → Bool) → Fin m → T) : Prop :=
  Function.Injective own ∧ (∀ i : Fin m, exposed (own i) = none) ∧
    ∀ σ : S → Bool, centerExposureAtom exposed σ → Function.Injective (terminal σ)

noncomputable def finiteRoutingWeight {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (ω : FiniteRoutingTables S T) : ℝ :=
  bitTableWeight (1 / 2) ω.selectors * bitTableWeight p ω.terminals

theorem finiteRoutingWeight_nonneg {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ω : FiniteRoutingTables S T) :
    0 ≤ finiteRoutingWeight p ω := by
  apply mul_nonneg <;> apply Finset.prod_nonneg
  · intro s _; exact bernoulliWeight_nonneg _ (by norm_num) (by norm_num) _
  · intro t _; exact bernoulliWeight_nonneg p hp₀ hp₁ _

noncomputable def tableProbability {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (E : FiniteRoutingTables S T → Prop) : ℝ :=
  ∑ σ : S → Bool, ∑ τ : T → Bool,
    bitTableWeight (1 / 2) σ * bitTableWeight p τ *
      if E ⟨σ, τ⟩ then 1 else 0

noncomputable def routingTablesEquiv (S T : Type*) :
    FiniteRoutingTables S T ≃ (S → Bool) × (T → Bool) where
  toFun ω := (ω.selectors, ω.terminals)
  invFun u := ⟨u.1, u.2⟩
  left_inv ω := by cases ω; rfl
  right_inv u := by cases u; rfl

noncomputable instance routingTablesFintype {S T : Type*} [Fintype S] [Fintype T] :
    Fintype (FiniteRoutingTables S T) := by
  classical
  exact Fintype.ofEquiv ((S → Bool) × (T → Bool)) (routingTablesEquiv S T).symm

theorem finiteRoutingWeight_sum {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) : (∑ ω : FiniteRoutingTables S T, finiteRoutingWeight p ω) = 1 := by
  classical
  rw [Fintype.sum_equiv (routingTablesEquiv S T) (finiteRoutingWeight p)
    (fun u => bitTableWeight (1 / 2) u.1 * bitTableWeight p u.2)
    (fun _ => rfl)]
  simp [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, bitTableWeight_sum]

theorem tableProbability_eq_weight_sum {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (E : FiniteRoutingTables S T → Prop) :
    tableProbability p E =
      ∑ ω : FiniteRoutingTables S T, finiteRoutingWeight p ω * if E ω then 1 else 0 := by
  classical
  rw [Fintype.sum_equiv (routingTablesEquiv S T)
    (fun ω => finiteRoutingWeight p ω * if E ω then 1 else 0)
    (fun u => bitTableWeight (1 / 2) u.1 * bitTableWeight p u.2 *
      if E ⟨u.1, u.2⟩ then 1 else 0) (fun _ => rfl)]
  simp [tableProbability, Fintype.sum_prod_type]

theorem indicator_forall_eq_product {I : Type*} [Fintype I] (P : I → Prop)
    [DecidablePred P] [Decidable (∀ i, P i)] :
    (if ∀ i, P i then (1 : ℝ) else 0) = ∏ i, if P i then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    simp only [h, ite_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem local_miss_indicator_product {S T : Type*} {m : ℕ}
    (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (σ : S → Bool) (τ : T → Bool) :
    (if localRoutingAllMiss own terminal ⟨σ, τ⟩ then (1 : ℝ) else 0) =
      ∏ i, if σ (own i) = true ∧ τ (terminal σ i) = true then 0 else 1 := by
  classical
  calc
    _ = (if ∀ i, ¬localRoutingSuccess own terminal ⟨σ, τ⟩ i then (1 : ℝ) else 0) :=
      ite_cond_congr rfl
    _ = ∏ i, if ¬localRoutingSuccess own terminal ⟨σ, τ⟩ i then (1 : ℝ) else 0 :=
      indicator_forall_eq_product (fun i => ¬localRoutingSuccess own terminal ⟨σ, τ⟩ i)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      cases hs : σ (own i) <;> cases ht : τ (terminal σ i) <;>
        simp [localRoutingSuccess, hs, ht]

/-- Conditional on ALL selectors, distinct routed terminal coordinates have
the Bernoulli product failure law.  No independent-path hypothesis occurs. -/
theorem terminal_average_local_miss {S T : Type*} [Fintype T] [DecidableEq T] {m : ℕ}
    (p : ℝ) (own : Fin m → S) (terminal : (S → Bool) → Fin m → T)
    (σ : S → Bool) (hinj : Function.Injective (terminal σ)) :
    (∑ τ : T → Bool, bitTableWeight p τ *
      if localRoutingAllMiss own terminal ⟨σ, τ⟩ then 1 else 0) =
      ∏ i, if σ (own i) = true then 1 - p else 1 := by
  classical
  simp_rw [local_miss_indicator_product]
  simp only [bitTableWeight]
  rw [weighted_distinct_reads (terminal σ) hinj
    (fun _ b => bernoulliWeight p b) (fun _ => bernoulliWeight_sum p)
    (fun i b => if σ (own i) = true ∧ b = true then 0 else 1)]
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ (own i) <;> simp [bernoulliWeight, h]

noncomputable def exposureLaw (o : Option Bool) (b : Bool) : ℝ :=
  match o with
  | none => bernoulliWeight (1 / 2) b
  | some v => if b = v then 1 else 0

noncomputable def exposureMass (o : Option Bool) : ℝ :=
  match o with
  | none => 1
  | some _ => 1 / 2

theorem exposureLaw_sum (o : Option Bool) : (∑ b : Bool, exposureLaw o b) = 1 := by
  cases o with
  | none => exact bernoulliWeight_sum _
  | some v => cases v <;> simp [exposureLaw]

theorem center_atom_weight_factorization {S : Type*} [Fintype S]
    (exposed : S → Option Bool) (σ : S → Bool) :
    bitTableWeight (1 / 2) σ * (if centerExposureAtom exposed σ then 1 else 0) =
      (∏ s, exposureMass (exposed s)) * ∏ s, exposureLaw (exposed s) (σ s) := by
  classical
  have hind : (if centerExposureAtom exposed σ then (1 : ℝ) else 0) =
      ∏ s, if ∀ v, exposed s = some v → σ s = v then (1 : ℝ) else 0 := by
    calc
      _ = (if ∀ s v, exposed s = some v → σ s = v then (1 : ℝ) else 0) :=
        ite_cond_congr rfl
      _ = _ := indicator_forall_eq_product (fun s => ∀ v,
        exposed s = some v → σ s = v)
  rw [hind]
  simp only [bitTableWeight]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  cases h : exposed s with
  | none => simp [exposureMass, exposureLaw, h]
  | some v => cases v <;> cases hv : σ s <;>
      norm_num [exposureMass, exposureLaw, bernoulliWeight, h, hv]

theorem center_atom_probability {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (exposed : S → Option Bool) :
    tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) =
      ∏ s, exposureMass (exposed s) := by
  classical
  simp only [tableProbability]
  have hsum (σ : S → Bool) :
      (∑ τ : T → Bool, bitTableWeight (1 / 2) σ * bitTableWeight p τ *
        if centerExposureAtom exposed σ then 1 else 0) =
      bitTableWeight (1 / 2) σ * if centerExposureAtom exposed σ then 1 else 0 := by
    by_cases h : centerExposureAtom exposed σ
    · simp only [h, ite_true, mul_one]
      rw [← Finset.mul_sum, bitTableWeight_sum, mul_one]
    · simp [h]
  simp_rw [hsum, center_atom_weight_factorization]
  rw [← Finset.mul_sum,
    ← Fintype.prod_sum (fun s b => exposureLaw (exposed s) b)]
  simp only [exposureLaw_sum, Finset.prod_const_one, mul_one]

/-- Exact JOINT center-atom / all-miss identity.  Terminal routing may depend on
every selector coordinate, including shared auxiliary entries.  The theorem
never divides by the atom probability and is valid also for p=0 and p=1. -/
theorem joint_center_atom_all_miss {S T : Type*} [Fintype S] [Fintype T] {m : ℕ}
    (p : ℝ) (exposed : S → Option Bool) (own : Fin m → S)
    (terminal : (S → Bool) → Fin m → T)
    (hsep : LocalAddressSeparation exposed own terminal) :
    tableProbability p (fun ω => centerExposureAtom exposed ω.selectors ∧
      localRoutingAllMiss own terminal ω) =
      tableProbability (T := T) p (fun ω => centerExposureAtom exposed ω.selectors) *
        (1 - p / 2) ^ m := by
  classical
  obtain ⟨hown, houtside, hterminal⟩ := hsep
  have hinner (σ : S → Bool) :
      (∑ τ : T → Bool, bitTableWeight (1 / 2) σ * bitTableWeight p τ *
        if centerExposureAtom exposed σ ∧ localRoutingAllMiss own terminal ⟨σ, τ⟩
          then 1 else 0) =
      bitTableWeight (1 / 2) σ * (if centerExposureAtom exposed σ then 1 else 0) *
        ∏ i, if σ (own i) = true then 1 - p else 1 := by
    by_cases hσ : centerExposureAtom exposed σ
    · simp only [hσ, true_and, ite_true, mul_one]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, terminal_average_local_miss p own terminal σ (hterminal σ hσ)]
    · simp [hσ]
  rw [center_atom_probability]
  have hsum : tableProbability p (fun ω => centerExposureAtom exposed ω.selectors ∧
      localRoutingAllMiss own terminal ω) =
      ∑ σ : S → Bool, bitTableWeight (1 / 2) σ *
        (if centerExposureAtom exposed σ then (1 : ℝ) else 0) *
          ∏ i, if σ (own i) = true then 1 - p else 1 := by
    unfold tableProbability
    apply Finset.sum_congr rfl
    intro σ _
    calc
      _ = (∑ τ : T → Bool, bitTableWeight (1 / 2) σ * bitTableWeight p τ *
          if centerExposureAtom exposed σ ∧ localRoutingAllMiss own terminal ⟨σ, τ⟩
            then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro τ _
        exact congrArg (fun z : ℝ => bitTableWeight (1 / 2) σ * bitTableWeight p τ * z)
          (ite_cond_congr rfl)
      _ = _ := hinner σ
  rw [hsum]
  simp_rw [center_atom_weight_factorization]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have havg := weighted_distinct_reads own hown
    (fun s b => exposureLaw (exposed s) b) (fun s => exposureLaw_sum (exposed s))
    (fun _ b => if b = true then 1 - p else 1)
  rw [havg]
  have hcoordinate (i : Fin m) :
      (∑ b : Bool, exposureLaw (exposed (own i)) b *
        if b = true then 1 - p else 1) = 1 - p / 2 := by
    simp [houtside, exposureLaw, bernoulliWeight]
    ring
  simp_rw [hcoordinate]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem tableProbability_nonneg {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (E : FiniteRoutingTables S T → Prop) :
    0 ≤ tableProbability p E := by
  classical
  rw [tableProbability_eq_weight_sum]
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (finiteRoutingWeight_nonneg p hp₀ hp₁ ω) (by split <;> norm_num)

theorem tableProbability_mono {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (E F : FiniteRoutingTables S T → Prop) (hEF : ∀ ω, E ω → F ω) :
    tableProbability p E ≤ tableProbability p F := by
  classical
  simp_rw [tableProbability_eq_weight_sum]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (finiteRoutingWeight_nonneg p hp₀ hp₁ ω)
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp_all

/-- A finite union bound on explicit finite table outcomes. -/
theorem tableProbability_union_bound {S T A : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (reps : Finset A)
    (E : FiniteRoutingTables S T → Prop) (F : A → FiniteRoutingTables S T → Prop)
    (hcover : ∀ ω, E ω → ∃ r ∈ reps, F r ω) :
    tableProbability p E ≤ ∑ r ∈ reps, tableProbability p (F r) := by
  classical
  simp_rw [tableProbability_eq_weight_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (finiteRoutingWeight_nonneg p hp₀ hp₁ ω)
  by_cases hE : E ω
  · obtain ⟨r, hr, hF⟩ := hcover ω hE
    simp only [hE, ite_true]
    calc
      1 = (if F r ω then (1 : ℝ) else 0) := by simp [hF]
      _ ≤ ∑ a ∈ reps, if F a ω then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun a => if F a ω then (1 : ℝ) else 0)
          (fun a _ => by split <;> norm_num) hr
  · simp only [hE, ite_false]
    exact Finset.sum_nonneg fun a _ => by split <;> norm_num

end ErdosSimilarityGrowingGaps
