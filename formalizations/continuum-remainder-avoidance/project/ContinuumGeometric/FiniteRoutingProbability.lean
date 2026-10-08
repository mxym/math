import ContinuumGeometric.RoutingInterfaces
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import ContinuumGeometric.RoutingModel
import ContinuumGeometric.RoutingMeasure

/-!
Finite product probabilities for the actual routing tables.  Selector-dependent
terminal addresses are averaged only after every selector has been fixed.
-/
namespace ContinuumGeometric

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable def bernoulliWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

noncomputable def bitTableWeight {S : Type*} [Fintype S]
    (p : ℝ) (σ : S → Bool) : ℝ := ∏ s, bernoulliWeight p (σ s)

noncomputable def finiteRoutingWeight {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (ω : FiniteRoutingTables S T) : ℝ :=
  bitTableWeight (1 / 2) ω.selectors * bitTableWeight p ω.terminals

noncomputable def tableProbability {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (E : FiniteRoutingTables S T → Prop) : ℝ :=
  ∑ σ : S → Bool, ∑ τ : T → Bool,
    bitTableWeight (1 / 2) σ * bitTableWeight p τ *
      if E ⟨σ, τ⟩ then 1 else 0

theorem bernoulliWeight_sum (p : ℝ) : (∑ b : Bool, bernoulliWeight p b) = 1 := by
  simp [bernoulliWeight]

theorem bitTableWeight_sum {S : Type*} [Fintype S] [DecidableEq S] (p : ℝ) :
    (∑ σ : S → Bool, bitTableWeight p σ) = 1 := by
  classical
  simp only [bitTableWeight]
  rw [← Fintype.prod_sum]
  simp only [bernoulliWeight_sum, Finset.prod_const_one]

theorem bernoulliWeight_nonneg (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight p b := by
  cases b <;> simp [bernoulliWeight] <;> linarith

theorem finiteRoutingWeight_nonneg {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ω : FiniteRoutingTables S T) :
    0 ≤ finiteRoutingWeight p ω := by
  apply mul_nonneg <;> apply Finset.prod_nonneg
  · intro s _; exact bernoulliWeight_nonneg _ (by norm_num) (by norm_num) _
  · intro t _; exact bernoulliWeight_nonneg p hp₀ hp₁ _

/-- Each read can be assigned to its actual coordinate, even before injectivity.
Shared auxiliary selector reads play no role in this identity. -/
theorem product_reads_by_coordinate {I S : Type*} [Fintype I] [Fintype S]
    [DecidableEq S]
    (address : I → S) (f : I → Bool → ℝ) (σ : S → Bool) :
    (∏ i, f i (σ (address i))) =
      ∏ s, ∏ i, if address i = s then f i (σ s) else 1 := by
  classical
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- Product averaging at distinct actual addresses, with normalized coordinate
weights.  This is an intermediate finite algebra theorem, not a routing premise. -/
theorem weighted_distinct_reads {I S : Type*} [Fintype I] [Fintype S]
    [DecidableEq S]
    (address : I → S) (hinj : Function.Injective address)
    (w : S → Bool → ℝ) (hw : ∀ s, (∑ b : Bool, w s b) = 1)
    (f : I → Bool → ℝ) :
    (∑ σ : S → Bool, (∏ s, w s (σ s)) * ∏ i, f i (σ (address i))) =
      ∏ i, ∑ b : Bool, w (address i) b * f i b := by
  classical
  have hc (σ : S → Bool) := product_reads_by_coordinate address f σ
  simp_rw [hc, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s b => w s b *
    ∏ i, if address i = s then f i b else 1)]
  let g : S → ℝ := fun s => ∑ b : Bool, w s b *
    ∏ i, if address i = s then f i b else 1
  change (∏ s, g s) = _
  have hout (s : S) (hs : s ∉ Finset.univ.image address) : g s = 1 := by
    have hne : ∀ i, address i ≠ s := by
      intro i h; exact hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
    simpa only [g, hne, ite_false, Finset.prod_const_one, mul_one] using hw s
  have hat (i : I) : g (address i) = ∑ b : Bool, w (address i) b * f i b := by
    have heq : ∀ j, address j = address i ↔ j = i := fun j => hinj.eq_iff
    simp [g, heq]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image address))
    (fun s _ hs => hout s hs)]
  rw [Finset.prod_image hinj.injOn]
  exact Finset.prod_congr rfl fun i _ => hat i

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

/-- Every point has Bernoulli-p occupancy even when its terminal address depends
on all selectors.  This is the finite tower calculation used for E density(B)=p. -/
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

end ContinuumGeometric
