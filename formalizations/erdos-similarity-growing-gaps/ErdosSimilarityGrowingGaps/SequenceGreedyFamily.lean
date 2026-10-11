import ErdosSimilarityGrowingGaps.SequenceGreedyRouting

namespace ErdosSimilarityGrowingGaps

open Set
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sequenceGreedyActive_card_mono
    {M d : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (child : Fin (M - 1))
    (k : ℤ) (p : PowerParams s₀ s₁) (a δ : ℝ)
    {B B' : ℕ} (hB : B ≤ B') :
    (sequenceActiveLocalCandidates Z c v
      (fun _ : Fin (B + 1) => child)
      (fun i => greedyIndex Z a δ i.1) k p).card ≤
    (sequenceActiveLocalCandidates Z c v
      (fun _ : Fin (B' + 1) => child)
      (fun i => greedyIndex Z a δ i.1) k p).card := by
  classical
  let f : Fin (B + 1) → Fin (B' + 1) := fun i =>
    ⟨i.1, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa [f] using congrArg Fin.val hij
  have himage : Finset.image f
      (sequenceActiveLocalCandidates Z c v
        (fun _ : Fin (B + 1) => child)
        (fun i => greedyIndex Z a δ i.1) k p) ⊆
      sequenceActiveLocalCandidates Z c v
        (fun _ : Fin (B' + 1) => child)
        (fun i => greedyIndex Z a δ i.1) k p := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    have hi' := (Finset.mem_filter.1 hi).2
    simpa [f] using hi'
  have hc := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ hf] at hc
  exact hc

/-- Sum the active entries of finitely many child-wise lists into the global
candidate set.  The slot map is injective on `(child,slot)`, so no active
entry is counted twice. -/
theorem sequenceActiveLocalCandidates_card_ge_of_childwise
    {M d P Q : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (hM : 1 ≤ M)
    (slot : Fin (M - 1) → Fin Q → Fin P)
    (hinj : Function.Injective (fun z : Fin (M - 1) × Fin Q =>
      slot z.1 z.2))
    (hchild : ∀ z : Fin (M - 1) × Fin Q,
      children (slot z.1 z.2) = z.1)
    (L : ℝ)
    (hcount : ∀ child : Fin (M - 1), L ≤
      (Finset.univ.filter (fun q : Fin Q =>
        sequencePowerActivation Z (indices (slot child q)) k
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot child q)⟩))
          ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot child q)⟩) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge
              ⟨v, children (slot child q)⟩)) p)).card) :
    L * ((M : ℝ) - 1) ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
  classical
  let A : Fin (M - 1) → Finset (Fin Q) := fun child =>
    Finset.univ.filter (fun q : Fin Q =>
      sequencePowerActivation Z (indices (slot child q)) k
        (c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot child q)⟩))
        ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (slot child q)⟩) : ℝ) +
          c.edgeLength (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot child q)⟩)) p)
  let I : Fin (M - 1) → Finset (Fin P) := fun child =>
    (A child).image (slot child)
  have hI_sub : ∀ child, I child ⊆
      sequenceActiveLocalCandidates Z c v children indices k p := by
    intro child i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    have hqa := (Finset.mem_filter.1 hq).2
    simpa [hchild (child, q)] using hqa
  have hI_disj : (↑(Finset.univ : Finset (Fin (M - 1))) :
      Set (Fin (M - 1))).PairwiseDisjoint I := by
    rw [Finset.pairwiseDisjoint_iff]
    intro a ha b hb hab
    rcases hab with ⟨i, hi⟩
    have hiA : i ∈ I a := (Finset.mem_inter.1 hi).1
    have hiB : i ∈ I b := (Finset.mem_inter.1 hi).2
    obtain ⟨qa, hqa, hia⟩ := Finset.mem_image.1 hiA
    obtain ⟨qb, hqb, hib⟩ := Finset.mem_image.1 hiB
    have hz : (a, qa) = (b, qb) := hinj (hia.trans hib.symm)
    exact congrArg Prod.fst hz
  let U := (Finset.univ : Finset (Fin (M - 1))).biUnion I
  have hU_sub : U ⊆ sequenceActiveLocalCandidates Z c v children indices k p := by
    intro i hi
    obtain ⟨child, hchildU, hiI⟩ := Finset.mem_biUnion.1 hi
    exact hI_sub child hiI
  have hcardU : U.card = ∑ child : Fin (M - 1), (I child).card := by
    simpa [U] using (Finset.card_biUnion hI_disj)
  have hcardI : ∀ child : Fin (M - 1), (I child).card = (A child).card := by
    intro child
    exact Finset.card_image_of_injective _ (by
      intro qa qb hq
      have hz : (child, qa) = (child, qb) := hinj hq
      exact congrArg Prod.snd hz)
  have hcardle := Finset.card_le_card hU_sub
  have hsum : L * (M - 1 : ℝ) ≤
      ∑ child : Fin (M - 1), ((I child).card : ℝ) := by
    calc
      L * (M - 1 : ℝ) = ∑ child : Fin (M - 1), L := by
        calc
          L * (M - 1 : ℝ) = L * ((Fintype.card (Fin (M - 1)) : ℕ) : ℝ) := by
            rw [Fintype.card_fin, Nat.cast_sub hM]
            norm_num
          _ = ∑ child : Fin (M - 1), L := by simp [mul_comm]
      _ ≤ ∑ child : Fin (M - 1), ((A child).card : ℝ) := by
        apply Finset.sum_le_sum
        intro child hchild
        exact hcount child
      _ = ∑ child : Fin (M - 1), ((I child).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro child hmem
        rw [hcardI child]
  calc
    L * ((M : ℝ) - 1) ≤ ∑ child : Fin (M - 1), ((I child).card : ℝ) := hsum
    _ = (U.card : ℝ) := by
      rw [hcardU, Nat.cast_sum]
    _ ≤ (sequenceActiveLocalCandidates Z c v children indices k p).card := by
      have hcardle' : (U.card : ℝ) ≤
          ((sequenceActiveLocalCandidates Z c v children indices k p).card : ℝ) := by
        exact_mod_cast hcardle
      exact hcardle'

/-- The child-wise summation theorem in the exact form used by a greedy
schedule: each child contributes at least `η*ell` active actual samples. -/
theorem sequenceActiveLocalCandidates_hmany_of_childwise
    {M d P Q : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (hM : 1 ≤ M)
    (slot : Fin (M - 1) → Fin Q → Fin P)
    (hinj : Function.Injective (fun z : Fin (M - 1) × Fin Q =>
      slot z.1 z.2))
    (hchild : ∀ z : Fin (M - 1) × Fin Q,
      children (slot z.1 z.2) = z.1)
    (η ell : ℝ) (hcount : ∀ child : Fin (M - 1), η * ell ≤
      (Finset.univ.filter (fun q : Fin Q =>
        sequencePowerActivation Z (indices (slot child q)) k
          (c.edgeStart (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot child q)⟩))
          ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
            ⟨v, children (slot child q)⟩) : ℝ) +
            c.edgeLength (RoutingTemplate.selectorRoutingEdge
              ⟨v, children (slot child q)⟩)) p)).card) :
    η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k p).card := by
  have h := sequenceActiveLocalCandidates_card_ge_of_childwise Z c v children indices k p
    hM slot hinj hchild (η * ell) hcount
  calc
    η * ((M : ℝ) - 1) * ell = (η * ell) * ((M : ℝ) - 1) := by ring
    _ ≤ (sequenceActiveLocalCandidates Z c v children indices k p).card := by
      simpa [mul_comm] using h


/-! A common finite prefix can serve every child of one routing vertex.  The
prefix length is the finite supremum of the child-wise crossing lengths; the
prefix monotonicity lemma transfers each individual lower bound to that common
length. -/
theorem exists_common_greedy_family
    {M d : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (k : ℤ)
    {U R : ℝ} (u : Fin (M - 1) → ℝ) (ell D δ η : ℝ)
    (hfill : FillsAnnulus Z U R D)
    (hM : 2 ≤ M) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hδ : 0 < δ)
    (ha : ∀ child, U / R ≤ (u child + (k : ℝ)) / s₁ - D)
    (ha_hi : ∀ child, (u child + (k : ℝ)) / s₁ ≤ R * U)
    (hnum : ∀ child, 0 ≤ u child + ell + (k : ℝ))
    (huk : ∀ child, 0 ≤ u child + (k : ℝ))
    (hwindow : ∀ child,
      c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) = u child ∧
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) =
        u child + ell)
    (hell : 2 * (s₁ * (δ + D)) ≤ ell)
    (hannulus : ∀ child,
      (u child + ell + (k : ℝ)) / s₀ + δ + D ≤ R * U)
    (hη : η * ell ≤ ell / (2 * (s₁ * (δ + D))))
    (hsep : 3 ≤ s₀ * δ) :
    ∃ B : ℕ, ∃ children : Fin ((M - 1) * (B + 1)) → Fin (M - 1),
      ∃ indices : Fin ((M - 1) * (B + 1)) → ℕ,
      (∀ p : PowerParams s₀ s₁,
        η * ((M : ℝ) - 1) * ell ≤
          (sequenceActiveLocalCandidates Z c v children indices k p).card) ∧
      Function.Injective (fun i => (children i, indices i)) ∧
      (∀ i j, i ≠ j → children i = children j →
        3 ≤ s₀ * |Z.z (indices j) - Z.z (indices i)|) := by
  classical
  have hne : (Finset.univ : Finset (Fin (M - 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hM1 : 1 ≤ M := by omega
  let B₀ : Fin (M - 1) → ℕ := fun child =>
    Classical.choose (exists_uniform_greedy_active_count Z c v child k
      (u child) ell D δ hfill hs₀ hs₁ hδ (ha child) (ha_hi child)
      (hnum child) (huk child) (hwindow child) hell (hannulus child))
  have hB₀ : ∀ child, ∀ p : PowerParams s₀ s₁,
      ell / (2 * (p.1.1 * (δ + D))) ≤
        (sequenceActiveLocalCandidates Z c v
          (fun _ : Fin (B₀ child + 1) => child)
          (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card := by
    intro child p
    exact Classical.choose_spec (exists_uniform_greedy_active_count Z c v child k
      (u child) ell D δ hfill hs₀ hs₁ hδ (ha child) (ha_hi child)
      (hnum child) (huk child) (hwindow child) hell (hannulus child)) p
  let B := (Finset.univ : Finset (Fin (M - 1))).sup' hne B₀
  have hBle : ∀ child, B₀ child ≤ B := by
    intro child
    exact Finset.le_sup' B₀ (Finset.mem_univ child)
  let e : (Fin (M - 1) × Fin (B + 1)) ≃ Fin ((M - 1) * (B + 1)) :=
    Fintype.equivFinOfCardEq (by simp)
  let children : Fin ((M - 1) * (B + 1)) → Fin (M - 1) :=
    fun i => (e.symm i).1
  let indices : Fin ((M - 1) * (B + 1)) → ℕ := fun i =>
    greedyIndex Z ((u (e.symm i).1 + (k : ℝ)) / s₁ - D) δ (e.symm i).2.1
  refine ⟨B, children, indices, ?_, ?_, ?_⟩
  · intro p
    refine sequenceActiveLocalCandidates_hmany_of_childwise Z c v children indices k p
      hM1 (slot := fun child q => e (child, q))
        (hinj := by
          intro z z' hz
          exact e.injective hz)
        (η := η) (ell := ell) ?_ ?_
    · intro z
      simp [children, e]
    · intro child
      have hmono := sequenceGreedyActive_card_mono Z c v child k p
        ((u child + (k : ℝ)) / s₁ - D) δ (hBle child)
      have hlow := hB₀ child p
      have hden : 0 ≤ δ + D := by linarith [hfill.2.2.1]
      have hdenpos : 0 < δ + D := by linarith [hfill.2.2.1]
      have hs : 0 < p.1.1 := hs₀.trans_le p.1.2.1
      have hsp : p.1.1 ≤ s₁ := p.1.2.2
      have hfrac : ell / (2 * (s₁ * (δ + D))) ≤
          ell / (2 * (p.1.1 * (δ + D))) := by
        apply div_le_div_of_nonneg_left
        · have hell_nonneg : 0 ≤ ell := by
            have : 0 < s₁ * (δ + D) := by positivity
            nlinarith [hell]
          exact hell_nonneg
        · have : 0 < 2 * (p.1.1 * (δ + D)) := by positivity
          exact this
        · have hmul := mul_le_mul_of_nonneg_right hsp hden
          nlinarith
      have hmono' :
          ((sequenceActiveLocalCandidates Z c v
            (fun _ : Fin (B₀ child + 1) => child)
            (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card : ℝ) ≤
          ((sequenceActiveLocalCandidates Z c v
            (fun _ : Fin (B + 1) => child)
            (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card : ℝ) := by
        exact_mod_cast hmono
      have hlocal := hη.trans (hfrac.trans (hlow.trans hmono'))
      convert hlocal using 1 <;>
        simp [children, indices, e, sequenceActiveLocalCandidates]
  · intro i j hij
    change (children i, indices i) = (children j, indices j) at hij
    have hchild : children i = children j :=
      congrArg (fun z : Fin (M - 1) × ℕ => z.1) hij
    have hindex : indices i = indices j :=
      congrArg (fun z : Fin (M - 1) × ℕ => z.2) hij
    have hchild' : (e.symm i).1 = (e.symm j).1 := by
      simpa [children] using hchild
    apply e.symm.injective
    apply Prod.ext hchild'
    have hindex' := hindex
    dsimp [indices] at hindex'
    rw [hchild'] at hindex'
    exact Fin.ext ((greedyIndex_injective Z
      ((u (e.symm j).1 + (k : ℝ)) / s₁ - D) δ hδ) hindex')
  · intro i j hij hchild
    have hpair : (e.symm i).1 = (e.symm j).1 := hchild
    have hq : (e.symm i).2 ≠ (e.symm j).2 := by
      intro heq
      apply hij
      exact e.symm.injective (Prod.ext hpair heq)
    simpa [children, indices, hpair] using
      (greedyWindowSamples_gap Z
        ((u (e.symm i).1 + (k : ℝ)) / s₁ - D) δ hδ hs₀ hsep
        (e.symm i).2 (e.symm j).2 hq)

theorem exists_common_greedy_family_bounded
    {M d : ℕ} {s₀ s₁ : ℝ}
    (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (k : ℤ)
    {U R : ℝ} (u : Fin (M - 1) → ℝ) (ell D δ η : ℝ)
    (hfill : FillsAnnulus Z U R D)
    (hM : 2 ≤ M) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hδ : 0 < δ)
    (ha : ∀ child, U / R ≤ (u child + (k : ℝ)) / s₁ - D)
    (ha_hi : ∀ child, (u child + (k : ℝ)) / s₁ ≤ R * U)
    (hnum : ∀ child, 0 ≤ u child + ell + (k : ℝ))
    (huk : ∀ child, 0 ≤ u child + (k : ℝ))
    (hwindow : ∀ child,
      c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) = u child ∧
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, child⟩) =
        u child + ell)
    (hell : 2 * (s₁ * (δ + D)) ≤ ell)
    (hannulus : ∀ child,
      (u child + ell + (k : ℝ)) / s₀ + δ + D ≤ R * U)
    (hη : η * ell ≤ ell / (2 * (s₁ * (δ + D))))
    (hsep : 3 ≤ s₀ * δ)
    (Q : ℕ)
    (hQ : ∀ child, max (((u child + ell + (k : ℝ)) / s₀ -
      ((u child + (k : ℝ)) / s₁ - D)) / δ) 0 + 1 ≤ (Q : ℝ)) :
    ∃ B : ℕ, ∃ children : Fin ((M - 1) * (B + 1)) → Fin (M - 1),
      ∃ indices : Fin ((M - 1) * (B + 1)) → ℕ,
      (∀ p : PowerParams s₀ s₁,
        η * ((M : ℝ) - 1) * ell ≤
          (sequenceActiveLocalCandidates Z c v children indices k p).card) ∧
      Function.Injective (fun i => (children i, indices i)) ∧
      (∀ i j, i ≠ j → children i = children j →
        3 ≤ s₀ * |Z.z (indices j) - Z.z (indices i)|) ∧
      B ≤ Q := by
  classical
  have hne : (Finset.univ : Finset (Fin (M - 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hM1 : 1 ≤ M := by omega
  let B₀ : Fin (M - 1) → ℕ := fun child =>
    Classical.choose (exists_uniform_greedy_active_count_bounded Z c v child k
      (u child) ell D δ hfill hs₀ hs₁ hδ (ha child) (ha_hi child)
      (hnum child) (huk child) (hwindow child) hell (hannulus child))
  have hB₀ : ∀ child, ∀ p : PowerParams s₀ s₁,
      ell / (2 * (p.1.1 * (δ + D))) ≤
        (sequenceActiveLocalCandidates Z c v
          (fun _ : Fin (B₀ child + 1) => child)
          (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card := by
    intro child p
    exact (Classical.choose_spec (exists_uniform_greedy_active_count_bounded Z c v child k
      (u child) ell D δ hfill hs₀ hs₁ hδ (ha child) (ha_hi child)
      (hnum child) (huk child) (hwindow child) hell (hannulus child))).1 p
  have hB₀Q : ∀ child, B₀ child ≤ Q := by
    intro child
    have hreal := (Classical.choose_spec
      (exists_uniform_greedy_active_count_bounded Z c v child k
        (u child) ell D δ hfill hs₀ hs₁ hδ (ha child) (ha_hi child)
        (hnum child) (huk child) (hwindow child) hell (hannulus child))).2
    have hreal' : (B₀ child : ℝ) ≤ (Q : ℝ) := hreal.trans (hQ child)
    exact_mod_cast hreal'
  let B := (Finset.univ : Finset (Fin (M - 1))).sup' hne B₀
  have hBle : ∀ child, B₀ child ≤ B := by
    intro child
    exact Finset.le_sup' B₀ (Finset.mem_univ child)
  let e : (Fin (M - 1) × Fin (B + 1)) ≃ Fin ((M - 1) * (B + 1)) :=
    Fintype.equivFinOfCardEq (by simp)
  let children : Fin ((M - 1) * (B + 1)) → Fin (M - 1) :=
    fun i => (e.symm i).1
  let indices : Fin ((M - 1) * (B + 1)) → ℕ := fun i =>
    greedyIndex Z ((u (e.symm i).1 + (k : ℝ)) / s₁ - D) δ (e.symm i).2.1
  refine ⟨B, children, indices, ?_, ?_, ?_, ?_⟩
  · intro p
    refine sequenceActiveLocalCandidates_hmany_of_childwise Z c v children indices k p
      hM1 (slot := fun child q => e (child, q))
        (hinj := by
          intro z z' hz
          exact e.injective hz)
        (η := η) (ell := ell) ?_ ?_
    · intro z
      simp [children, e]
    · intro child
      have hmono := sequenceGreedyActive_card_mono Z c v child k p
        ((u child + (k : ℝ)) / s₁ - D) δ (hBle child)
      have hlow := hB₀ child p
      have hden : 0 ≤ δ + D := by linarith [hfill.2.2.1]
      have hdenpos : 0 < δ + D := by linarith [hfill.2.2.1]
      have hs : 0 < p.1.1 := hs₀.trans_le p.1.2.1
      have hsp : p.1.1 ≤ s₁ := p.1.2.2
      have hfrac : ell / (2 * (s₁ * (δ + D))) ≤
          ell / (2 * (p.1.1 * (δ + D))) := by
        apply div_le_div_of_nonneg_left
        · have hell_nonneg : 0 ≤ ell := by
            have : 0 < s₁ * (δ + D) := by positivity
            nlinarith [hell]
          exact hell_nonneg
        · have : 0 < 2 * (p.1.1 * (δ + D)) := by positivity
          exact this
        · have hmul := mul_le_mul_of_nonneg_right hsp hden
          nlinarith
      have hmono' :
          ((sequenceActiveLocalCandidates Z c v
            (fun _ : Fin (B₀ child + 1) => child)
            (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card : ℝ) ≤
          ((sequenceActiveLocalCandidates Z c v
            (fun _ : Fin (B + 1) => child)
            (fun i => greedyIndex Z ((u child + (k : ℝ)) / s₁ - D) δ i.1) k p).card : ℝ) := by
        exact_mod_cast hmono
      have hlocal := hη.trans (hfrac.trans (hlow.trans hmono'))
      convert hlocal using 1 <;>
        simp [children, indices, e, sequenceActiveLocalCandidates]
  · intro i j hij
    change (children i, indices i) = (children j, indices j) at hij
    have hchild : children i = children j :=
      congrArg (fun z : Fin (M - 1) × ℕ => z.1) hij
    have hindex : indices i = indices j :=
      congrArg (fun z : Fin (M - 1) × ℕ => z.2) hij
    have hchild' : (e.symm i).1 = (e.symm j).1 := by
      simpa [children] using hchild
    apply e.symm.injective
    apply Prod.ext hchild'
    have hindex' := hindex
    dsimp [indices] at hindex'
    rw [hchild'] at hindex'
    exact Fin.ext ((greedyIndex_injective Z
      ((u (e.symm j).1 + (k : ℝ)) / s₁ - D) δ hδ) hindex')
  · intro i j hij hchild
    have hpair : (e.symm i).1 = (e.symm j).1 := hchild
    have hq : (e.symm i).2 ≠ (e.symm j).2 := by
      intro heq
      apply hij
      exact e.symm.injective (Prod.ext hpair heq)
    simpa [children, indices, hpair] using
      (greedyWindowSamples_gap Z
        ((u (e.symm i).1 + (k : ℝ)) / s₁ - D) δ hδ hs₀ hsep
        (e.symm i).2 (e.symm j).2 hq)
  · exact Finset.sup'_le hne B₀ (fun child _ => hB₀Q child)


end ErdosSimilarityGrowingGaps
