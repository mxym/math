import ErdosSimilarityGrowingGaps.RoutingProbability
import ErdosSimilarityGrowingGaps.RoutingLaw
import ErdosSimilarityGrowingGaps.RoutingChoices
import Mathlib.Tactic


/-!
The exact no-default probability of the actual complete ordered routing tree.
Each prescribed nondefault path fixes its earlier sibling selector bits and its
chosen bit at every depth.  Their actual table addresses are pairwise distinct.
The disjoint path probabilities then sum over the finite tree; no independent
path or global routing-probability premise is used.
-/
namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable local instance {M d : ℕ} : DecidableEq (RoutingLeaf M d) := Classical.decEq _

theorem chooseRoutingChild_eq_nondefault_iff (M : ℕ) (hM : 0 < M)
    (bits : Fin (M - 1) → Bool) (i : Fin (M - 1)) :
    chooseRoutingChild M hM bits = nondefaultChild i ↔
      bits i = true ∧ ∀ j : Fin (M - 1), j.val < i.val → bits j = false := by
  constructor
  · intro h
    cases hf : (List.ofFn (fun j : Fin (M - 1) => j)).find? bits with
    | none =>
      have hv := congrArg Fin.val h
      simp [chooseRoutingChild, hf, defaultChild, nondefaultChild] at hv
      omega
    | some j =>
      have hv := congrArg Fin.val h
      simp [chooseRoutingChild, hf, nondefaultChild] at hv
      have hj : j = i := Fin.ext hv
      subst j
      have hfirst := (List.find?_ofFn_eq_some_of_injective (fun _ _ h => h)).1 hf
      exact ⟨hfirst.1, fun j hj => by
        simpa only [Bool.not_eq_true] using hfirst.2 j hj⟩
  · rintro ⟨hi, hprev⟩
    exact chooseRoutingChild_of_first_true M hM bits i hi hprev

theorem chooseRoutingChild_eq_default_iff_all_false (M : ℕ) (hM : 0 < M)
    (bits : Fin (M - 1) → Bool) :
    chooseRoutingChild M hM bits = defaultChild M hM ↔
      ∀ i : Fin (M - 1), bits i = false := by
  constructor
  · intro h
    cases hf : (List.ofFn (fun j : Fin (M - 1) => j)).find? bits with
    | none =>
      intro i
      have hn := List.find?_eq_none.mp hf i (by simp)
      simpa only [Bool.not_eq_true] using hn
    | some j =>
      have hv := congrArg Fin.val h
      simp [chooseRoutingChild, hf, defaultChild, nondefaultChild] at hv
      have hj := j.isLt
      omega
  · exact chooseRoutingChild_of_all_false M hM bits

/-- A prescribed path using only genuine selector-bearing children. -/
abbrev NondefaultLeaf (M d : ℕ) := Fin d → Fin (M - 1)

def embedNondefaultLeaf {M d : ℕ} (leaf : NondefaultLeaf M d) : RoutingLeaf M d :=
  fun j => nondefaultChild (leaf j)

theorem embedNondefaultLeaf_injective (M d : ℕ) :
    Function.Injective (@embedNondefaultLeaf M d) := by
  intro a b h
  funext j
  apply Fin.ext
  exact congrArg (fun l : RoutingLeaf M d => (l j).val) h

/-- Earlier sibling reads and the selected sibling read at each actual prefix. -/
abbrev NondefaultPathRead {M d : ℕ} (leaf : NondefaultLeaf M d) :=
  Σ j : Fin d, Fin ((leaf j).val + 1)

def nondefaultPathNode {M d : ℕ} (leaf : NondefaultLeaf M d) (j : Fin d) :
    InternalNode M d :=
  nodeOfPrefix ((List.ofFn (embedNondefaultLeaf leaf)).take j.val) (by
    simp)

def nondefaultPathEdge {M d : ℕ} (leaf : NondefaultLeaf M d)
    (r : NondefaultPathRead leaf) : SelectorEdge M d :=
  ⟨nondefaultPathNode leaf r.1,
    Fin.castLE (Nat.succ_le_of_lt (leaf r.1).isLt) r.2⟩

noncomputable def nondefaultPathAddress {M d : ℕ} (c : RoutingTemplate M d)
    (leaf : NondefaultLeaf M d) (z : ℝ) (r : NondefaultPathRead leaf) : SelectorAddress c :=
  selectorAddress c (nondefaultPathEdge leaf r) z

def nondefaultPathRequired {M d : ℕ} {leaf : NondefaultLeaf M d}
    (r : NondefaultPathRead leaf) : Bool :=
  if r.2.val = (leaf r.1).val then true else false

@[simp] theorem nondefaultPathNode_depth {M d : ℕ} (leaf : NondefaultLeaf M d)
    (j : Fin d) : (nondefaultPathNode leaf j).1.val = j.val := by
  simp [nondefaultPathNode, nodeOfPrefix]

/-- Different depths have different nodes; at a fixed depth sibling table tags
are distinct.  Consequently the actual reads are distinct for every real z.
-/
theorem nondefaultPathAddress_injective {M d : ℕ} (c : RoutingTemplate M d)
    (leaf : NondefaultLeaf M d) (z : ℝ) :
    Function.Injective (nondefaultPathAddress c leaf z) := by
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  have he : nondefaultPathEdge leaf ⟨j, i⟩ = nondefaultPathEdge leaf ⟨j', i'⟩ :=
    congrArg Sigma.fst h
  have hjv := congrArg (fun e : SelectorEdge M d => e.1.1.val) he
  simp only [nondefaultPathEdge, nondefaultPathNode_depth] at hjv
  have hj : j = j' := Fin.ext hjv
  subst j'
  have hiv := congrArg (fun e : SelectorEdge M d => e.2.val) he
  have hi : i = i' := Fin.ext hiv
  subst i'
  rfl

/-- Fixed actual route = exactly the first-true bits along its own prefixes. -/
theorem routeLeaf_eq_nondefault_iff_reads {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ)
    (leaf : NondefaultLeaf M d) :
    routeLeaf c hM σ z = embedNondefaultLeaf leaf ↔
      ∀ r : NondefaultPathRead leaf,
        σ (nondefaultPathAddress c leaf z r) = nondefaultPathRequired r := by
  rw [routeLeaf_eq_iff_prefix_choices]
  change (∀ j : Fin d, chooseRoutingChild M hM
    (nodeSelectorBits c σ z (nondefaultPathNode leaf j)) = nondefaultChild (leaf j)) ↔ _
  simp_rw [chooseRoutingChild_eq_nondefault_iff]
  constructor
  · intro h r
    obtain ⟨j, i⟩ := r
    by_cases hi : i.val = (leaf j).val
    · have heq : Fin.castLE (Nat.succ_le_of_lt (leaf j).isLt) i = leaf j := Fin.ext hi
      simpa [nondefaultPathAddress, nondefaultPathEdge, nondefaultPathRequired, hi, heq,
        nodeSelectorBits] using (h j).1
    · have hlt : i.val < (leaf j).val := by omega
      simpa [nondefaultPathAddress, nondefaultPathEdge, nondefaultPathRequired, hi,
        nodeSelectorBits] using (h j).2
          (Fin.castLE (Nat.succ_le_of_lt (leaf j).isLt) i) hlt
  · intro h j
    constructor
    · have hr := h ⟨j, ⟨(leaf j).val, by omega⟩⟩
      have heq : Fin.castLE (Nat.succ_le_of_lt (leaf j).isLt)
          (⟨(leaf j).val, by omega⟩ : Fin ((leaf j).val + 1)) = leaf j := Fin.ext rfl
      simpa [nondefaultPathAddress, nondefaultPathEdge, nondefaultPathRequired, heq,
        nodeSelectorBits] using hr
    · intro i hi
      have hr := h ⟨j, ⟨i.val, by omega⟩⟩
      have heq : Fin.castLE (Nat.succ_le_of_lt (leaf j).isLt)
          (⟨i.val, by omega⟩ : Fin ((leaf j).val + 1)) = i := Fin.ext rfl
      have hne : i.val ≠ (leaf j).val := by omega
      simpa [nondefaultPathAddress, nondefaultPathEdge, nondefaultPathRequired, hne, heq,
        nodeSelectorBits] using hr

/-- Terminal coordinates integrate out of events determined by selectors. -/
theorem tableProbability_selectorEvent {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (E : (S → Bool) → Prop) :
    tableProbability (T := T) p (fun ω => E ω.selectors) =
      ∑ σ : S → Bool, bitTableWeight (1 / 2) σ * if E σ then 1 else 0 := by
  unfold tableProbability
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : E σ
  · simp only [h, ite_true, mul_one]
    rw [← Finset.mul_sum, bitTableWeight_sum, mul_one]
  · simp [h]

/-- Exact probability of one prescribed actual nondefault leaf. -/
theorem actual_nondefault_leaf_probability {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p z : ℝ) (leaf : NondefaultLeaf M d) :
    tableProbability p (fun ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd) =>
      routeLeaf c hM ω.selectors z = embedNondefaultLeaf leaf) =
      ∏ j : Fin d, (1 / 2 : ℝ) ^ ((leaf j).val + 1) := by
  let : DecidableEq (SelectorAddress c) := Classical.decEq _
  rw [tableProbability_selectorEvent (T := TerminalAddress c hd) p
    (fun σ => routeLeaf c hM σ z = embedNondefaultLeaf leaf)]
  have hind (σ : SelectorAddress c → Bool) :
      (if routeLeaf c hM σ z = embedNondefaultLeaf leaf then (1 : ℝ) else 0) =
        ∏ r : NondefaultPathRead leaf,
          if σ (nondefaultPathAddress c leaf z r) = nondefaultPathRequired r then 1 else 0 := by
    calc
      _ = (if ∀ r : NondefaultPathRead leaf,
          σ (nondefaultPathAddress c leaf z r) = nondefaultPathRequired r then 1 else 0) :=
        ite_cond_congr (propext (routeLeaf_eq_nondefault_iff_reads c hM σ z leaf))
      _ = _ := indicator_forall_eq_product _
  have hsum : (∑ σ : SelectorAddress c → Bool, bitTableWeight (1 / 2) σ *
      if (fun σ => routeLeaf c hM σ z = embedNondefaultLeaf leaf) σ then 1 else 0) =
      ∑ σ : SelectorAddress c → Bool, bitTableWeight (1 / 2) σ *
        ∏ r : NondefaultPathRead leaf,
          if σ (nondefaultPathAddress c leaf z r) = nondefaultPathRequired r then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    apply congrArg (fun x : ℝ => bitTableWeight (1 / 2) σ * x)
    exact (ite_cond_congr rfl).trans (hind σ)
  rw [hsum]
  unfold bitTableWeight
  rw [weighted_distinct_reads (nondefaultPathAddress c leaf z)
    (nondefaultPathAddress_injective c leaf z)
    (fun _ b => bernoulliWeight (1 / 2) b) (fun _ => bernoulliWeight_sum _)
    (fun r b => if b = nondefaultPathRequired r then 1 else 0)]
  have havg (r : NondefaultPathRead leaf) :
      (∑ b : Bool, bernoulliWeight (1 / 2) b *
        if b = nondefaultPathRequired r then (1 : ℝ) else 0) = 1 / 2 := by
    cases h : nondefaultPathRequired r <;> norm_num [bernoulliWeight, h]
  simp_rw [havg]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin]
  exact (Finset.prod_pow_eq_pow_sum Finset.univ
    (fun j : Fin d => (leaf j).val + 1) (1 / 2 : ℝ)).symm

theorem routeHasNoDefault_iff_nondefault_leaf {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ) :
    routeHasNoDefault c hM σ z ↔
      ∃ leaf : NondefaultLeaf M d, routeLeaf c hM σ z = embedNondefaultLeaf leaf := by
  constructor
  · intro h
    have hlt (j : Fin d) : (routeLeaf c hM σ z j).val < M - 1 := by
      have hr := (routeLeaf c hM σ z j).isLt
      have hne : (routeLeaf c hM σ z j).val ≠ M - 1 := by
        intro he
        exact h j (Fin.ext he)
      omega
    refine ⟨fun j => ⟨(routeLeaf c hM σ z j).val, hlt j⟩, ?_⟩
    funext j
    exact Fin.ext rfl
  · rintro ⟨leaf, heq⟩ j hdefault
    rw [heq] at hdefault
    have hv := congrArg Fin.val hdefault
    have hi := (leaf j).isLt
    simp only [embedNondefaultLeaf, nondefaultChild, Fin.val_castLE, defaultChild] at hv
    omega

theorem noDefault_indicator_eq_leaf_sum {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (z : ℝ) :
    (if routeHasNoDefault c hM σ z then (1 : ℝ) else 0) =
      ∑ leaf : NondefaultLeaf M d,
        if routeLeaf c hM σ z = embedNondefaultLeaf leaf then 1 else 0 := by
  by_cases h : routeHasNoDefault c hM σ z
  · obtain ⟨leaf, heq⟩ := (routeHasNoDefault_iff_nondefault_leaf c hM σ z).1 h
    simp only [h, ite_true, heq, (embedNondefaultLeaf_injective M d).eq_iff]
    simp
  · have hne (leaf : NondefaultLeaf M d) : routeLeaf c hM σ z ≠ embedNondefaultLeaf leaf := by
      intro heq
      exact h ((routeHasNoDefault_iff_nondefault_leaf c hM σ z).2 ⟨leaf, heq⟩)
    simp [h, hne]

theorem half_geometric_child_sum (n : ℕ) :
    (∑ i : Fin n, (1 / 2 : ℝ) ^ (i.val + 1)) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    ring

/-- Exact actual no-default law at every real point, independent of terminal p.
Only finite selector-table product averaging is used.
-/
theorem actual_routeHasNoDefault_probability {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p z : ℝ) :
    tableProbability p (fun ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd) =>
      routeHasNoDefault c hM ω.selectors z) =
      (1 - (1 / 2 : ℝ) ^ (M - 1)) ^ d := by
  calc
    _ = ∑ leaf : NondefaultLeaf M d,
        tableProbability p (fun ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd) =>
          routeLeaf c hM ω.selectors z = embedNondefaultLeaf leaf) := by
      rw [tableProbability_eq_weight_sum]
      simp_rw [noDefault_indicator_eq_leaf_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro leaf _
      exact (tableProbability_eq_weight_sum (S := SelectorAddress c)
        (T := TerminalAddress c hd) p
        (fun ω => routeLeaf c hM ω.selectors z = embedNondefaultLeaf leaf)).symm
    _ = ∑ leaf : NondefaultLeaf M d,
        ∏ j : Fin d, (1 / 2 : ℝ) ^ ((leaf j).val + 1) := by
      apply Finset.sum_congr rfl
      intro leaf _
      exact actual_nondefault_leaf_probability c hM hd p z leaf
    _ = ∏ _j : Fin d, ∑ i : Fin (M - 1), (1 / 2 : ℝ) ^ (i.val + 1) :=
      (Fintype.prod_sum (fun (_j : Fin d) (i : Fin (M - 1)) =>
        (1 / 2 : ℝ) ^ (i.val + 1))).symm
    _ = _ := by
      rw [half_geometric_child_sum]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The tree law uses the scalar proved by the noncircular default-depth schedule. -/
theorem actual_routeHasNoDefault_probability_rpow {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (p z : ℝ) :
    tableProbability p (fun ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd) =>
      routeHasNoDefault c hM ω.selectors z) =
      (1 - (2 : ℝ) ^ (1 - (M : ℝ))) ^ d := by
  rw [actual_routeHasNoDefault_probability, half_selector_default_probability_eq M (by omega)]

end ErdosSimilarityGrowingGaps
