import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ErdosSimilarityGrowingGaps.ParameterStrata
import ErdosSimilarityGrowingGaps.SignFiberQuadratic
import ErdosSimilarityGrowingGaps.LineSignQuadratic

namespace ErdosSimilarityGrowingGaps

/-- Quadratic arrangement representative property for affine sign cuts on a
closed rectangle.  Zero-sign strata and degenerate cuts are retained. -/
def QuadraticArrangementRepresentativeBound : Prop :=
  ∀ (m : ℕ) (cuts : Fin m → AffineCut) (lo hi : ℝ × ℝ),
    lo.1 ≤ hi.1 → lo.2 ≤ hi.2 →
    ∃ reps : Finset (ℝ × ℝ),
      (∀ r ∈ reps, inRectangle lo hi r) ∧
      reps.card ≤ 20 * (m + 5) ^ 2 ∧
      ∀ p : ℝ × ℝ, inRectangle lo hi p →
        ∃ r ∈ reps, ∀ i : Fin m,
          cutSign (evalCut (cuts i) r) = cutSign (evalCut (cuts i) p)

@[simp] theorem cutSign_eq_negative (x : ℝ) : cutSign x = .negative ↔ x < 0 := by
  unfold cutSign
  split_ifs <;> simp_all

@[simp] theorem cutSign_eq_zero (x : ℝ) : cutSign x = .zero ↔ x = 0 := by
  unfold cutSign
  split_ifs <;> simp_all
  linarith

@[simp] theorem cutSign_eq_positive (x : ℝ) : cutSign x = .positive ↔ 0 < x := by
  unfold cutSign
  by_cases hx : x < 0
  · simp [hx]
    linarith
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    by_cases hz : x = 0
    · simp [hz]
    · simp only [hx, hz, ↓reduceIte, true_iff]
      exact lt_of_le_of_ne hx0 (Ne.symm hz)

noncomputable def realizedPlanePatterns {n : ℕ} (cuts : Fin n → AffineCut) :
    Finset (Fin n → CutSign) := by
  classical
  exact Finset.univ.filter (fun s => ∃ p : ℝ × ℝ, ∀ i, cutSign (evalCut (cuts i) p) = s i)

@[simp] theorem mem_realizedPlanePatterns {n : ℕ} (cuts : Fin n → AffineCut)
    (s : Fin n → CutSign) :
    s ∈ realizedPlanePatterns cuts ↔
    ∃ p : ℝ × ℝ, ∀ i, cutSign (evalCut (cuts i) p) = s i := by
  classical
  simp [realizedPlanePatterns]

def blendPoint (p q : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1-t)*p.1+t*q.1, (1-t)*p.2+t*q.2)

theorem eval_blend (c : AffineCut) (p q : ℝ × ℝ) (t : ℝ) :
    evalCut c (blendPoint p q t) = (1-t)*evalCut c p+t*evalCut c q := by
  simp only [evalCut, blendPoint]
  ring

theorem cutSign_blend {u v t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (h : cutSign u = cutSign v) :
    cutSign ((1-t)*u+t*v) = cutSign u := by
  have h1 : 0 < 1-t := by linarith
  generalize hs : cutSign u = s at *
  cases s with
  | negative =>
      have hu : u < 0 := (cutSign_eq_negative u).mp hs
      have hv : v < 0 := (cutSign_eq_negative v).mp h.symm
      apply (cutSign_eq_negative _).mpr
      have := mul_neg_of_pos_of_neg h1 hu
      have := mul_neg_of_pos_of_neg ht hv
      linarith
  | zero =>
      have hu : u = 0 := (cutSign_eq_zero u).mp hs
      have hv : v = 0 := (cutSign_eq_zero v).mp h.symm
      simp [hu, hv]
  | positive =>
      have hu : 0 < u := (cutSign_eq_positive u).mp hs
      have hv : 0 < v := (cutSign_eq_positive v).mp h.symm
      apply (cutSign_eq_positive _).mpr
      have := mul_pos h1 hu
      have := mul_pos ht hv
      linarith

theorem exists_blend_zero {u v : ℝ} (hu : u < 0) (hv : 0 < v) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1-t)*u+t*v = 0 := by
  have hd : 0 < v-u := by linarith
  refine ⟨-u/(v-u), div_pos (by linarith) hd, ?_, ?_⟩
  · apply (div_lt_one hd).mpr
    linarith
  · field_simp
    ring

theorem plane_zero_between {n : ℕ} (cuts : Fin n → AffineCut) (c : AffineCut)
    (s : Fin n → CutSign) (p q : ℝ × ℝ)
    (hp : ∀ i, cutSign (evalCut (cuts i) p) = s i)
    (hq : ∀ i, cutSign (evalCut (cuts i) q) = s i)
    (hn : cutSign (evalCut c p) = .negative)
    (hv : cutSign (evalCut c q) = .positive) :
    ∃ r : ℝ × ℝ, (∀ i, cutSign (evalCut (cuts i) r) = s i) ∧
      cutSign (evalCut c r) = .zero := by
  obtain ⟨t, ht, ht1, hz⟩ := exists_blend_zero
    ((cutSign_eq_negative _).mp hn) ((cutSign_eq_positive _).mp hv)
  refine ⟨blendPoint p q t, ?_, ?_⟩
  · intro i
    rw [eval_blend, cutSign_blend ht ht1 ((hp i).trans (hq i).symm), hp]
  · rw [eval_blend, hz]
    exact (cutSign_eq_zero _).mpr rfl


noncomputable def realizedPairs {n : ℕ} (cuts : Fin n → AffineCut)
    (c : AffineCut) : Finset ((Fin n → CutSign) × CutSign) := by
  classical
  exact Finset.univ.filter (fun s => ∃ p : ℝ × ℝ,
    (∀ i, cutSign (evalCut (cuts i) p) = s.1 i) ∧ cutSign (evalCut c p) = s.2)

@[simp] theorem mem_realizedPairs {n : ℕ} (cuts : Fin n → AffineCut)
    (c : AffineCut) (s : (Fin n → CutSign) × CutSign) :
    s ∈ realizedPairs cuts c ↔ ∃ p : ℝ × ℝ,
    (∀ i, cutSign (evalCut (cuts i) p) = s.1 i) ∧ cutSign (evalCut c p) = s.2 := by
  classical
  simp [realizedPairs]

theorem oldPatterns_realizedPairs {n : ℕ} (cuts : Fin n → AffineCut)
    (c : AffineCut) : oldPatterns (realizedPairs cuts c) = realizedPlanePatterns cuts := by
  classical
  ext s
  simp only [oldPatterns, Finset.mem_image, mem_realizedPlanePatterns]
  constructor
  · rintro ⟨⟨s', v⟩, hs', rfl⟩
    obtain ⟨p, hp, _⟩ := (mem_realizedPairs cuts c _).mp hs'
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨(s, cutSign (evalCut c p)), (mem_realizedPairs cuts c _).mpr
      ⟨p, hp, rfl⟩, rfl⟩

theorem realizedPairs_cross {n : ℕ} (cuts : Fin n → AffineCut) (c : AffineCut)
    (s : Fin n → CutSign) (hn : (s, CutSign.negative) ∈ realizedPairs cuts c)
    (hp : (s, CutSign.positive) ∈ realizedPairs cuts c) :
    (s, CutSign.zero) ∈ realizedPairs cuts c := by
  obtain ⟨p, hps, hpn⟩ := (mem_realizedPairs cuts c _).mp hn
  obtain ⟨q, hqs, hqp⟩ := (mem_realizedPairs cuts c _).mp hp
  exact (mem_realizedPairs cuts c _).mpr (plane_zero_between cuts c s p q hps hqs hpn hqp)

def splitPattern {n : ℕ} (s : Fin (n+1) → CutSign) :
    (Fin n → CutSign) × CutSign := (fun i => s i.succ, s 0)

theorem splitPattern_injective {n : ℕ} : Function.Injective (@splitPattern n) := by
  intro s t h
  have h0 := congrArg Prod.snd h
  have hs := congrArg Prod.fst h
  funext i
  refine Fin.cases h0 (fun j => congrFun hs j) i

theorem realizedPairs_split {n : ℕ} (cuts : Fin (n+1) → AffineCut) :
    realizedPairs (fun i => cuts i.succ) (cuts 0) =
      (realizedPlanePatterns cuts).image splitPattern := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨p, hp, hp0⟩ := (mem_realizedPairs _ _ s).mp hs
    refine Finset.mem_image.mpr ⟨fun i => cutSign (evalCut (cuts i) p), ?_, ?_⟩
    · exact (mem_realizedPlanePatterns _ _).mpr ⟨p, fun _ => rfl⟩
    · apply Prod.ext
      · funext i
        exact hp i
      · exact hp0
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨p, hp⟩ := (mem_realizedPlanePatterns _ _).mp ht
    exact (mem_realizedPairs _ _ _).mpr ⟨p, fun i => hp i.succ, hp 0⟩

theorem card_realizedPairs_split {n : ℕ} (cuts : Fin (n+1) → AffineCut) :
    (realizedPairs (fun i => cuts i.succ) (cuts 0)).card =
      (realizedPlanePatterns cuts).card := by
  classical
  rw [realizedPairs_split, Finset.card_image_of_injective _ splitPattern_injective]

theorem card_realizedPairs_constant {n : ℕ} (cuts : Fin n → AffineCut)
    (c : AffineCut) (ha : c.1 = 0) (hb : c.2.1 = 0) :
    (realizedPairs cuts c).card = (realizedPlanePatterns cuts).card := by
  classical
  rw [← oldPatterns_realizedPairs cuts c]
  symm
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  obtain ⟨p, hp, hpc⟩ := (mem_realizedPairs cuts c _).mp hx
  obtain ⟨q, hq, hqc⟩ := (mem_realizedPairs cuts c _).mp hy
  apply Prod.ext hxy
  simp only [evalCut, ha, hb, zero_mul, zero_add] at hpc hqc
  exact hpc.symm.trans hqc

noncomputable def cutLineX (c : AffineCut) (t : ℝ) : ℝ × ℝ :=
  (-(c.2.1*t+c.2.2)/c.1, t)

noncomputable def cutLineY (c : AffineCut) (t : ℝ) : ℝ × ℝ :=
  (t, -(c.1*t+c.2.2)/c.2.1)

theorem zero_parameter_x {c : AffineCut} {p : ℝ × ℝ}
    (hc : c.1 ≠ 0) (hp : evalCut c p = 0) : p = cutLineX c p.2 := by
  apply Prod.ext
  · apply (eq_div_iff hc).mpr
    dsimp [evalCut] at hp
    linarith
  · rfl

theorem zero_parameter_y {c : AffineCut} {p : ℝ × ℝ}
    (hc : c.2.1 ≠ 0) (hp : evalCut c p = 0) : p = cutLineY c p.1 := by
  apply Prod.ext
  · rfl
  · apply (eq_div_iff hc).mpr
    dsimp [evalCut] at hp
    linarith

theorem eval_cutLineX (c d : AffineCut) (t : ℝ) :
    evalCut d (cutLineX c t) =
      (d.2.1-d.1*c.2.1/c.1)*t+(d.2.2-d.1*c.2.2/c.1) := by
  dsimp [evalCut, cutLineX]
  ring

theorem eval_cutLineY (c d : AffineCut) (t : ℝ) :
    evalCut d (cutLineY c t) =
      (d.1-d.2.1*c.1/c.2.1)*t+(d.2.2-d.2.1*c.2.2/c.2.1) := by
  dsimp [evalCut, cutLineY]
  ring


theorem zeroPatterns_card_le {n : ℕ} (cuts : Fin n → AffineCut) (c : AffineCut)
    (hc : c.1 ≠ 0 ∨ c.2.1 ≠ 0) :
    (zeroPatterns (realizedPairs cuts c)).card ≤ 2*n+1 := by
  classical
  rcases hc with ha | hb
  · let a : Fin n → ℝ := fun i => (cuts i).2.1-(cuts i).1*c.2.1/c.1
    let b : Fin n → ℝ := fun i => (cuts i).2.2-(cuts i).1*c.2.2/c.1
    have hsub : zeroPatterns (realizedPairs cuts c) ⊆ realizedLinePatterns n a b := by
      intro s hs
      obtain ⟨p, hp, hpz⟩ := (mem_realizedPairs cuts c _).mp (mem_zeroPatterns.mp hs)
      have hz : evalCut c p = 0 := (cutSign_eq_zero _).mp hpz
      have heq := zero_parameter_x ha hz
      simp only [realizedLinePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨p.2, fun i => ?_⟩
      have := hp i
      rw [heq, eval_cutLineX] at this
      exact this
    exact (Finset.card_le_card hsub).trans (realizedLinePatterns_card_le n a b)
  · let a : Fin n → ℝ := fun i => (cuts i).1-(cuts i).2.1*c.1/c.2.1
    let b : Fin n → ℝ := fun i => (cuts i).2.2-(cuts i).2.1*c.2.2/c.2.1
    have hsub : zeroPatterns (realizedPairs cuts c) ⊆ realizedLinePatterns n a b := by
      intro s hs
      obtain ⟨p, hp, hpz⟩ := (mem_realizedPairs cuts c _).mp (mem_zeroPatterns.mp hs)
      have hz : evalCut c p = 0 := (cutSign_eq_zero _).mp hpz
      have heq := zero_parameter_y hb hz
      simp only [realizedLinePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨p.1, fun i => ?_⟩
      have := hp i
      rw [heq, eval_cutLineY] at this
      exact this
    exact (Finset.card_le_card hsub).trans (realizedLinePatterns_card_le n a b)

/-- The full three-sign arrangement count, including every degenerate affine cut. -/
theorem realizedPlanePatterns_card_le (n : ℕ) (cuts : Fin n → AffineCut) :
    (realizedPlanePatterns cuts).card ≤ 2*n^2+1 := by
  classical
  induction n with
  | zero =>
      have h := Finset.card_le_univ (realizedPlanePatterns cuts)
      simpa using h
  | succ n ih =>
      let old : Fin n → AffineCut := fun i => cuts i.succ
      let c : AffineCut := cuts 0
      have hold : (realizedPlanePatterns old).card ≤ 2*n^2+1 := ih old
      rw [← card_realizedPairs_split cuts]
      change (realizedPairs old c).card ≤ 2*(n+1)^2+1
      by_cases ha : c.1 = 0
      · by_cases hb : c.2.1 = 0
        · rw [card_realizedPairs_constant old c ha hb]
          have hn : n^2 ≤ (n+1)^2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
          omega
        · have hz := zeroPatterns_card_le old c (Or.inr hb)
          have hf := card_le_oldPatterns_add_two_zeroPatterns (realizedPairs old c)
            (realizedPairs_cross old c)
          rw [oldPatterns_realizedPairs] at hf
          nlinarith
      · have hz := zeroPatterns_card_le old c (Or.inl ha)
        have hf := card_le_oldPatterns_add_two_zeroPatterns (realizedPairs old c)
          (realizedPairs_cross old c)
        rw [oldPatterns_realizedPairs] at hf
        nlinarith


/-- Exact owner-interface theorem: finite representatives inside the closed rectangle,
with all negative, zero and positive signs preserved and the requested quadratic budget. -/
theorem quadratic_arrangement_representative_bound : QuadraticArrangementRepresentativeBound := by
  classical
  intro m cuts lo hi _ _
  let patterns : Finset (Fin m → CutSign) := Finset.univ.filter (fun s =>
    ∃ p : ℝ × ℝ, inRectangle lo hi p ∧ ∀ i, cutSign (evalCut (cuts i) p) = s i)
  have hpatterns : ∀ s ∈ patterns, ∃ p : ℝ × ℝ,
      inRectangle lo hi p ∧ ∀ i, cutSign (evalCut (cuts i) p) = s i := by
    intro s hs
    simpa only [patterns, Finset.mem_filter, Finset.mem_univ, true_and] using hs
  let pick : {s // s ∈ patterns} → ℝ × ℝ := fun s =>
    Classical.choose (hpatterns s.1 s.2)
  have hpick : ∀ s : {s // s ∈ patterns}, inRectangle lo hi (pick s) ∧
      ∀ i, cutSign (evalCut (cuts i) (pick s)) = s.1 i := fun s =>
    Classical.choose_spec (hpatterns s.1 s.2)
  let reps : Finset (ℝ × ℝ) := patterns.attach.image pick
  have hsub : patterns ⊆ realizedPlanePatterns cuts := by
    intro s hs
    obtain ⟨p, _, hp⟩ := hpatterns s hs
    exact (mem_realizedPlanePatterns _ _).mpr ⟨p, hp⟩
  refine ⟨reps, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hpick s).1
  · calc
      reps.card ≤ patterns.attach.card := Finset.card_image_le
      _ = patterns.card := Finset.card_attach
      _ ≤ (realizedPlanePatterns cuts).card := Finset.card_le_card hsub
      _ ≤ 2*m^2+1 := realizedPlanePatterns_card_le m cuts
      _ ≤ 20*(m+5)^2 := by
        have hm : m^2 ≤ (m+5)^2 := Nat.pow_le_pow_left (by omega) 2
        have h5 : 25 ≤ (m+5)^2 := by
          calc
            25 = 5^2 := by norm_num
            _ ≤ (m+5)^2 := Nat.pow_le_pow_left (by omega) 2
        omega
  · intro p hp
    let s : Fin m → CutSign := fun i => cutSign (evalCut (cuts i) p)
    have hs : s ∈ patterns := by
      simp only [patterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, fun _ => rfl⟩
    refine ⟨pick ⟨s, hs⟩, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    intro i
    exact (hpick ⟨s, hs⟩).2 i


#print axioms realizedPlanePatterns_card_le

end ErdosSimilarityGrowingGaps
