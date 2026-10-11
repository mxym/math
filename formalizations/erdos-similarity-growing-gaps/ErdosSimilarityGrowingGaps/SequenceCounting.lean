import ErdosSimilarityGrowingGaps.GreedySampling
import ErdosSimilarityGrowingGaps.SequenceRoutingProbability
import Mathlib.Order.Interval.Finset.Nat

namespace ErdosSimilarityGrowingGaps

open Set
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite prefix stays below its cumulative annular overshoot budget. -/
theorem greedyIndex_log_upper_of_filling_prefix
    {Z : LogScale} {U R D v δ : ℝ} (hfill : FillsAnnulus Z U R D)
    (hδ : 0 < δ) (hlo : U / R ≤ v) (B : ℕ)
    (hbudget : v + D + (B : ℝ) * (δ + D) ≤ R * U) :
    ∀ i : ℕ, i ≤ B → Z.z (greedyIndex Z v δ i) ≤
      v + D + (i : ℝ) * (δ + D) := by
  have hD : 0 ≤ D := by linarith [hfill.2.2.1]
  intro i hi
  induction i with
  | zero =>
      have hanchor : v + D ≤ R * U := by
        nlinarith [mul_nonneg (Nat.cast_nonneg B) (by linarith : 0 ≤ δ + D)]
      simpa only [Nat.cast_zero, zero_mul, add_zero] using
        (greedyIndex_anchor_of_filling hfill hδ hlo hanchor).2
  | succ i ih =>
      have hiB : i ≤ B := by omega
      have hprev := ih hiB
      have hib : (i + 1 : ℝ) ≤ B := by exact_mod_cast hi
      have hprev_budget : Z.z (greedyIndex Z v δ i) + δ + D ≤ R * U := by
        nlinarith [mul_le_mul_of_nonneg_right hib (by linarith : 0 ≤ δ + D)]
      have hprev_lo : U / R ≤ Z.z (greedyIndex Z v δ i) :=
        hlo.trans (greedyIndex_first_log_ge Z v δ hδ i)
      have hstep := greedyIndex_log_gap_le_of_filling hfill hδ i hprev_lo hprev_budget
      push_cast
      nlinarith

/-- The global lower separation controls all selected coordinates, including
those chosen after the filled annulus. -/
theorem greedyIndex_log_lower (Z : LogScale) (v δ : ℝ) (hδ : 0 < δ) :
    ∀ i : ℕ, v + (i : ℝ) * δ ≤ Z.z (greedyIndex Z v δ i) := by
  intro i
  induction i with
  | zero =>
      rw [greedyIndex_zero]
      simpa using (firstGeIndex_spec Z v).1
  | succ i ih =>
      have hstep := greedyIndex_log_gap_ge Z v δ hδ i
      push_cast
      nlinarith

theorem exists_greedyIndex_crossing (Z : LogScale) (v T δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, T ≤ Z.z (greedyIndex Z v δ B) := by
  obtain ⟨B, hB⟩ := exists_nat_gt ((T - v) / δ)
  refine ⟨B, ?_⟩
  have hlow := greedyIndex_log_lower Z v δ hδ B
  have hBr : (T - v) / δ < (B : ℝ) := by exact_mod_cast hB
  have hmul : T - v < (B : ℝ) * δ := (div_lt_iff₀ hδ).1 hBr
  nlinarith

/-- Telescoping bounded consecutive gaps over a finite index interval. -/
theorem sequence_span_le_of_gap_le (w : ℕ → ℝ) (D : ℝ) (a n : ℕ)
    (hgap : ∀ i : ℕ, a ≤ i → i < a + n → w (i + 1) ≤ w i + D) :
    w (a + n) ≤ w a + (n : ℝ) * D := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : ∀ i : ℕ, a ≤ i → i < a + n → w (i + 1) ≤ w i + D := by
        intro i hi hi'
        exact hgap i hi (by omega)
      have hlast := hgap (a + n) (by omega) (by omega)
      have hspan := ih hprev
      push_cast
      rw [show a + (n + 1) = a + n + 1 by omega]
      nlinarith

/-- Every open window crossed by a monotone finite prefix contains at least
`ell / (2*D)` members when the crossing gaps are at most `D` and `ell ≥ 2D`.
The first crossing of the upper endpoint is excluded even when it is equal to
that endpoint; the predecessor of the first strict lower crossing is included
in the enclosing span even when equal to the lower endpoint. -/
theorem open_window_card_lower_of_gap_le
    (w : ℕ → ℝ) (hw : StrictMono w) (u ell D : ℝ)
    (hD : 0 < D) (hell : 2 * D ≤ ell) (hstart : w 0 ≤ u)
    (B : ℕ) (hcross : u + ell ≤ w B)
    (hgap : ∀ i : ℕ, i < B → w i < u + ell → w (i + 1) ≤ w i + D) :
    ell / (2 * D) ≤
      (((Finset.range (B + 1)).filter fun i => u < w i ∧ w i < u + ell).card : ℝ) := by
  classical
  have hellpos : 0 < ell := by linarith
  have hexR : ∃ n : ℕ, u + ell ≤ w n := ⟨B, hcross⟩
  let b := Nat.find hexR
  have hb : u + ell ≤ w b := Nat.find_spec hexR
  have hbB : b ≤ B := Nat.find_min' hexR hcross
  have hexL : ∃ n : ℕ, u < w n := ⟨b, by linarith⟩
  let a := Nat.find hexL
  have ha : u < w a := Nat.find_spec hexL
  have hab : a ≤ b := Nat.find_min' hexL (by linarith)
  have ha0 : 0 < a := by
    by_contra h
    have heq : a = 0 := by omega
    rw [heq] at ha
    linarith
  have haprev : w (a - 1) ≤ u := by
    exact le_of_not_gt (Nat.find_min hexL (by omega : a - 1 < a))
  have hbcross : ∀ i : ℕ, i < b → w i < u + ell := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hexR hi)
  have hspan : w b ≤ w (a - 1) + ((b - (a - 1) : ℕ) : ℝ) * D := by
    have htel := sequence_span_le_of_gap_le w D (a - 1) (b - (a - 1)) (by
      intro i hi hi'
      have hib : i < b := by omega
      exact hgap i (lt_of_lt_of_le hib hbB) (hbcross i hib))
    simpa only [Nat.add_sub_of_le (by omega : a - 1 ≤ b)] using htel
  have hcount : ((b - a : ℕ) : ℝ) ≤
      (((Finset.range (B + 1)).filter fun i => u < w i ∧ w i < u + ell).card : ℝ) := by
    have hsub : Finset.Ico a b ⊆
        (Finset.range (B + 1)).filter fun i => u < w i ∧ w i < u + ell := by
      intro i hi
      obtain ⟨hai, hib⟩ := Finset.mem_Ico.1 hi
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_, hbcross i hib⟩
      exact ha.trans_le (hw.monotone hai)
    exact_mod_cast (by simpa only [Nat.card_Ico] using Finset.card_le_card hsub)
  have hlen : ell ≤ (((b - a : ℕ) : ℝ) + 1) * D := by
    have heq : b - (a - 1) = (b - a) + 1 := by omega
    rw [heq, Nat.cast_add, Nat.cast_one] at hspan
    linarith
  have hbound : ell / (2 * D) ≤ ((b - a : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    nlinarith
  exact hbound.trans hcount

/-- Paper (8), lower bound, for the actual greedy logarithms.  Only the gaps
needed to cross this window are constrained by the annulus. -/
theorem greedy_open_window_card_lower
    {Z : LogScale} {U R D v δ : ℝ} (hfill : FillsAnnulus Z U R D)
    (hδ : 0 < δ) (hlo : U / R ≤ v)
    (s u ell : ℝ) (k : ℤ) (hs : 0 < s)
    (hell : 2 * (s * (δ + D)) ≤ ell)
    (hstart : s * Z.z (greedyIndex Z v δ 0) - (k : ℝ) ≤ u)
    (hannulus : (u + ell + (k : ℝ)) / s + δ + D ≤ R * U)
    (B : ℕ) (hcross : u + ell ≤
      s * Z.z (greedyIndex Z v δ B) - (k : ℝ)) :
    ell / (2 * (s * (δ + D))) ≤
      (((Finset.range (B + 1)).filter fun i =>
        u < s * Z.z (greedyIndex Z v δ i) - (k : ℝ) ∧
          s * Z.z (greedyIndex Z v δ i) - (k : ℝ) < u + ell).card : ℝ) := by
  have hD : 0 ≤ D := by linarith [hfill.2.2.1]
  let w : ℕ → ℝ := fun i => s * Z.z (greedyIndex Z v δ i) - (k : ℝ)
  have hw : StrictMono w := by
    intro i j hij
    exact sub_lt_sub_right (mul_lt_mul_of_pos_left
      (Z.strictMono (greedyIndex_strictMono Z v δ hδ hij)) hs) _
  apply open_window_card_lower_of_gap_le w hw u ell (s * (δ + D))
    (by positivity) hell hstart B hcross
  intro i _ hi
  have hzi : Z.z (greedyIndex Z v δ i) < (u + ell + (k : ℝ)) / s := by
    apply (lt_div_iff₀ hs).2
    dsimp only [w] at hi
    nlinarith
  have hstep := greedyIndex_log_gap_le_of_filling hfill hδ i
    (hlo.trans (greedyIndex_first_log_ge Z v δ hδ i)) (by linarith)
  dsimp only [w]
  nlinarith

/-! A finite-cardinality bridge for the local routing API.  Once a caller
    supplies one active sample for each pair `(child, local-slot)`, injectivity
    turns the slot count into the exact `sequenceActiveLocalCandidates`
    lower bound.  The geometric work is isolated in the supplied activation
    premise, so this lemma is reusable for either greedy or annular schedules. -/
theorem sequenceActiveLocalCandidates_card_ge_of_injective_active
    {M d P Q : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (slot : Fin (M - 1) → Fin Q → Fin P)
    (hinj : Function.Injective (fun z : Fin (M - 1) × Fin Q =>
      slot z.1 z.2))
    (hchild : ∀ z : Fin (M - 1) × Fin Q,
      children (slot z.1 z.2) = z.1)
    (hactive : ∀ z : Fin (M - 1) × Fin Q,
      sequencePowerActivation Z (indices (slot z.1 z.2)) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot z.1 z.2)⟩))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot z.1 z.2)⟩) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot z.1 z.2)⟩)) p) :
    Q * (M - 1) ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
  classical
  let f : Fin (M - 1) × Fin Q → Fin P := fun z => slot z.1 z.2
  have himage : Finset.image f (Finset.univ : Finset (Fin (M - 1) × Fin Q)) ⊆
      sequenceActiveLocalCandidates Z c v children indices k p := by
    intro i hi
    rcases Finset.mem_image.1 hi with ⟨z, _, hzi⟩
    rw [← hzi]
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [f, hchild z] using hactive z
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ (by simpa [f] using hinj),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hcard
  nlinarith

theorem sequenceActiveLocalCandidates_hmany_of_injective_active
    {M d P Q : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (slot : Fin (M - 1) → Fin Q → Fin P)
    (hinj : Function.Injective (fun z : Fin (M - 1) × Fin Q =>
      slot z.1 z.2))
    (hchild : ∀ z : Fin (M - 1) × Fin Q,
      children (slot z.1 z.2) = z.1)
    (hactive : ∀ z : Fin (M - 1) × Fin Q,
      sequencePowerActivation Z (indices (slot z.1 z.2)) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot z.1 z.2)⟩))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot z.1 z.2)⟩) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot z.1 z.2)⟩)) p)
    (hM : 1 ≤ M) (η ell : ℝ)
    (hQ : η * ell ≤ (Q : ℝ)) :
    η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
  have hcard := sequenceActiveLocalCandidates_card_ge_of_injective_active
    Z c v children indices k p slot hinj hchild hactive
  have hcard' : (Q : ℝ) * ((M - 1 : ℕ) : ℝ) ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
    exact_mod_cast hcard
  rw [Nat.cast_sub (by omega : 1 ≤ M)] at hcard'
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hcard'' : (Q : ℝ) * ((M : ℝ) - 1) ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
    simpa only [Nat.cast_one] using hcard'
  have hmul := mul_le_mul_of_nonneg_right hQ
    (sub_nonneg.mpr hMr)
  calc
    η * ((M : ℝ) - 1) * ell = (η * ell) * ((M : ℝ) - 1) := by ring
    _ ≤ (Q : ℝ) * ((M : ℝ) - 1) := hmul
    _ ≤ (sequenceActiveLocalCandidates Z c v children indices k p).card := hcard''

/-! The greedy count can be read directly as the active-candidate count used
by the actual-log routing law. -/

theorem sequenceActiveLocalCandidates_card_ge_of_greedy_filter
    {M d B : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (child : Fin (M - 1))
    (k : ℤ) (p : PowerParams s₀ s₁)
    {U R : ℝ} (u ell D δ : ℝ) (hfill : FillsAnnulus Z U R D)
    (hs₀ : 0 < s₀) (hδ : 0 < δ) (hlo : U / R ≤ u)
    (hwindow : c.edgeStart (RoutingTemplate.selectorRoutingEdge
      ⟨v, child⟩) = u ∧
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) = u + ell)
    (hell : 2 * (p.1.1 * (δ + D)) ≤ ell)
    (hstart : p.1.1 * Z.z (greedyIndex Z u δ 0) - (k : ℝ) ≤ u)
    (hannulus : (u + ell + (k : ℝ)) / p.1.1 + δ + D ≤ R * U)
    (Bcross : ℕ) (hcross : u + ell ≤
      p.1.1 * Z.z (greedyIndex Z u δ Bcross) - (k : ℝ)) :
    ell / (2 * (p.1.1 * (δ + D))) ≤
      (sequenceActiveLocalCandidates Z c v
        (fun _ : Fin (Bcross + 1) => child)
        (fun i => greedyIndex Z u δ i.1) k p).card := by
  have hs : 0 < p.1.1 := by
    exact hs₀.trans_le p.1.2.1
  have hcount := greedy_open_window_card_lower hfill hδ hlo
    (s := p.1.1) u ell k hs hell hstart hannulus Bcross hcross
  let e : Fin (Bcross + 1) ↪ ℕ :=
    ⟨fun i => i.1, Fin.val_injective⟩
  have hcard :
      (((Finset.univ.filter (fun i : Fin (Bcross + 1) =>
        u < p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) ∧
          p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) < u + ell)).card : ℕ) : ℝ) =
        (((Finset.range (Bcross + 1)).filter (fun i =>
          u < p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) ∧
            p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) < u + ell)).card : ℝ) := by
    let A := Finset.univ.filter (fun i : Fin (Bcross + 1) =>
      u < p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) ∧
        p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) < u + ell)
    let T := Finset.range (Bcross + 1)
    have heq : A.map e = T.filter (fun i =>
        u < p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) ∧
          p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) < u + ell) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.1 hn with ⟨i, hi, rfl⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 i.isLt,
          (Finset.mem_filter.1 hi).2⟩
      · intro hn
        have hnlt := (Finset.mem_filter.1 hn).1
        let i : Fin (Bcross + 1) := ⟨n, Finset.mem_range.1 hnlt⟩
        refine Finset.mem_map.2 ⟨i, Finset.mem_filter.2
          ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · exact (Finset.mem_filter.1 hn).2
        · rfl
    dsimp [A, T] at heq ⊢
    rw [← heq, Finset.card_map]
  calc
    _ ≤ (((Finset.range (Bcross + 1)).filter (fun i =>
      u < p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) ∧
        p.1.1 * Z.z (greedyIndex Z u δ i) - (k : ℝ) < u + ell)).card : ℝ) := hcount
    _ = (((Finset.univ.filter (fun i : Fin (Bcross + 1) =>
      u < p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) ∧
        p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) < u + ell)).card : ℕ) : ℝ) := hcard.symm
    _ = (sequenceActiveLocalCandidates Z c v
      (fun _ : Fin (Bcross + 1) => child)
      (fun i => greedyIndex Z u δ i.1) k p).card := by
      have hA : (Finset.univ.filter (fun i : Fin (Bcross + 1) =>
          u < p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) ∧
            p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) < u + ell)) =
          sequenceActiveLocalCandidates Z c v
            (fun _ : Fin (Bcross + 1) => child)
            (fun i => greedyIndex Z u δ i.1) k p := by
        change (Finset.univ.filter (fun i : Fin (Bcross + 1) =>
          u < p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) ∧
            p.1.1 * Z.z (greedyIndex Z u δ i.1) - (k : ℝ) < u + ell)) =
          Finset.univ.filter (fun i : Fin (Bcross + 1) =>
            sequencePowerActivation Z (greedyIndex Z u δ i.1) k
              (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩))
              ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
                c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩)) p)
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [sequencePowerActivation]
        constructor <;> intro hi
        · exact ⟨by linarith [hwindow.1, hi.1], by
            linarith [hwindow.1, hwindow.2, hi.2]⟩
        · exact ⟨by linarith [hwindow.1, hi.1], by
            linarith [hwindow.1, hwindow.2, hi.2]⟩
      rw [← hA]

end ErdosSimilarityGrowingGaps
