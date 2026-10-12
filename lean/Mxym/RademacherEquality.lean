import Mxym.Rademacher
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.EquivFin

namespace Mxym.Rademacher
open scoped BigOperators Classical
open Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

 theorem mean_reindex (e : ι ≃ κ) (c : κ → ℝ) :
    mean (fun i => c (e i)) = mean c := by
  let E : (ι → Bool) ≃ (κ → Bool) := e.arrowCongr (Equiv.refl Bool)
  have hs (ε : ι → Bool) :
      signedSum (fun i => c (e i)) ε = signedSum c (E ε) := by
    exact Fintype.sum_equiv e _ _ (fun i => by simp [E])
  have hn : Fintype.card (ι → Bool) = Fintype.card (κ → Bool) := Fintype.card_congr E
  unfold mean
  rw [hn]
  congr 1
  exact Fintype.sum_equiv E _ _ (fun ε => congrArg abs (hs ε))

 theorem mean_sum_zero (c : ι → ℝ) :
    mean (Sum.elim c (fun _ : κ => 0)) = mean c := by
  let E : ((ι ⊕ κ) → Bool) ≃ (ι → Bool) × (κ → Bool) :=
    Equiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => Bool)
  have hs (ε : (ι ⊕ κ) → Bool) :
      signedSum (Sum.elim c (fun _ : κ => 0)) ε = signedSum c (E ε).1 := by
    simp [signedSum, E, Fintype.sum_sum_type]
  have hn : Fintype.card ((ι ⊕ κ) → Bool) =
      Fintype.card (ι → Bool) * Fintype.card (κ → Bool) := by
    rw [Fintype.card_congr E, Fintype.card_prod]
  have he : (∑ ε : (ι ⊕ κ) → Bool, |signedSum (Sum.elim c (fun _ : κ => 0)) ε|) =
      (Fintype.card (κ → Bool) : ℝ) * (∑ ε : ι → Bool, |signedSum c ε|) := by
    calc
      _ = ∑ p : (ι → Bool) × (κ → Bool), |signedSum c p.1| :=
        Fintype.sum_equiv E _ _ (fun ε => congrArg abs (hs ε))
      _ = _ := by simp [Fintype.sum_prod_type, ← Finset.mul_sum]
  unfold mean
  rw [he, hn, Nat.cast_mul]
  have hk : (Fintype.card (κ → Bool) : ℝ) ≠ 0 := by positivity
  field_simp

 theorem mean_restrict (c : ι → ℝ) (p : ι → Prop) [DecidablePred p]
    (hc : ∀ i, ¬p i → c i = 0) : mean c = mean (fun i : {i // p i} => c i) := by
  let e := Equiv.sumCompl p
  have he : (fun i => c (e i)) =
      Sum.elim (fun i : {i // p i} => c i) (fun _ : {i // ¬p i} => 0) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact hc i i.2
  have h := mean_reindex e c
  rw [he, mean_sum_zero] at h
  exact h.symm

 theorem sum_signs_succ {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ ε : Fin (n + 1) → Bool, f ε) =
      (∑ ε : Fin n → Bool, f (Fin.cons true ε)) +
      (∑ ε : Fin n → Bool, f (Fin.cons false ε)) := by
  calc
    _ = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_bool]

private theorem cons_two {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 2) → α) :
    Fin.cons (α := fun _ : Fin (n + 3) => α) a f 2 = f 1 := rfl

private theorem cons_three {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 3) → α) :
    Fin.cons (α := fun _ : Fin (n + 4) => α) a f 3 = f 2 := rfl

 theorem mean_three_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha' : a ≤ b + c) (hb' : b ≤ a + c) (hc' : c ≤ a + b) :
    mean ![a, b, c] = (a + b + c) / 2 := by
  simp [mean, signedSum, sum_signs_succ, Fin.sum_univ_succ, sign,
    cons_two, Fin.default_eq_zero]
  rw [abs_of_nonneg (by linarith : 0 ≤ a + (b + c)),
    abs_of_nonneg (by linarith : 0 ≤ a + (b + -c)),
    abs_of_nonneg (by linarith : 0 ≤ a + (-b + c)),
    abs_of_nonpos (by linarith : a + (-b + -c) ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ -a + (b + c)),
    abs_of_nonpos (by linarith : -a + (b + -c) ≤ 0),
    abs_of_nonpos (by linarith : -a + (-b + c) ≤ 0),
    abs_of_nonpos (by linarith : -a + (-b + -c) ≤ 0)]
  norm_num
  ring

 theorem mean_four_quarters : mean (fun _ : Fin 4 => (1 / 4 : ℝ)) = 3 / 8 := by
  norm_num [mean, signedSum, sum_signs_succ, Fin.sum_univ_succ, sign, cons_two, cons_three, Fin.default_eq_zero]

/-- With four or more positive coefficients and no saturated cap, the bound is strict. -/
 theorem normalized_strict_positive (t : ι → ℝ)
    (ht : t ∈ balancedPolytope (ι := ι))
    (hpos : ∀ i, 0 < t i) (hlt : ∀ i, t i < 1 / 2)
    (hcard : 4 ≤ Fintype.card ι) : mean t < 1 / 2 := by
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ ι) :=
    Function.Embedding.nonempty_iff_card_le.mpr (by simpa using hcard)
  let : Nonempty ι := ⟨e 0⟩
  let y : ι → ℝ := fun i => if i ∈ Set.range e then 1 / 4 else 0
  have hy0 (i : ι) : 0 ≤ y i := by dsimp [y]; split_ifs <;> norm_num
  have hy1 (i : ι) : y i ≤ 1 / 4 := by dsimp [y]; split_ifs <;> norm_num
  let : Fintype (Set.range e) := Subtype.fintype _
  have hyin (i : Set.range e) : y i = 1 / 4 := ite_eq_left i.2
  have hyout (i : {i // i ∉ Set.range e}) : y i = 0 := ite_eq_right i.2
  have hys : (∑ i, y i) = 1 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range e) y]
    have he : Fintype.card (Set.range e) = 4 := by simpa using Fintype.card_range e
    simp only [hyin, hyout, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, he]
    norm_num
  have hym : mean y = 3 / 8 := by
    rw [mean_restrict y (fun i => i ∈ Set.range e) (by intro i hi; exact ite_eq_right hi)]
    let E := Equiv.ofInjective e e.injective
    have hf : (fun j => y (E j)) = (fun _ : Fin 4 => (1 / 4 : ℝ)) := by
      funext j
      exact ite_eq_left (E j).2
    have h := mean_reindex E (fun i : Set.range e => y i)
    rw [hf, mean_four_quarters] at h
    exact h.symm
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => min (t i) (1 / 2 - t i))
  have hd : 0 < δ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    exact lt_min (hpos i) (sub_pos.mpr (hlt i))
  have hd1 (i : ι) : δ ≤ t i :=
    (Finset.inf'_le (fun i => min (t i) (1 / 2 - t i)) (Finset.mem_univ i)).trans (min_le_left _ _)
  have hd2 (i : ι) : δ ≤ 1 / 2 - t i :=
    (Finset.inf'_le (fun i => min (t i) (1 / 2 - t i)) (Finset.mem_univ i)).trans (min_le_right _ _)
  let α : ℝ := min δ (1 / 2)
  have ha : 0 < α := lt_min hd (by norm_num)
  have haδ : α ≤ δ := min_le_left _ _
  have ha1 : α ≤ 1 / 2 := min_le_right _ _
  have hb : 0 < 1 - α := by linarith
  let z : ι → ℝ := fun i => (t i - α * y i) / (1 - α)
  have hz : z ∈ balancedPolytope (ι := ι) := by
    constructor
    · intro i
      constructor
      · apply div_nonneg _ hb.le
        nlinarith [hd1 i, hy1 i]
      · apply (div_le_iff₀ hb).2
        nlinarith [hd2 i, mul_nonneg ha.le (hy0 i)]
    · simp only [z, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ht.2, hys, mul_one]
      exact mul_inv_cancel₀ (ne_of_gt hb)
  have he : α • y + (1 - α) • z = t := by
    funext i
    change α * y i + (1 - α) * ((t i - α * y i) / (1 - α)) = t i
    field_simp
    ring
  have hconv := (convex_mean (ι := ι)).2 (mem_univ y) (mem_univ z) ha.le hb.le
    (show α + (1 - α) = 1 by ring)
  rw [he] at hconv
  change mean t ≤ α * mean y + (1 - α) * mean z at hconv
  rw [hym] at hconv
  have hbound := normalized_bound z hz
  have hh := mul_le_mul_of_nonneg_left hbound hb.le
  nlinarith

omit [DecidableEq ι] in
 theorem restrict_balanced (t : ι → ℝ) (ht : t ∈ balancedPolytope (ι := ι)) :
    (fun i : {i // t i ≠ 0} => t i) ∈ balancedPolytope := by
  constructor
  · intro i; exact ht.1 i
  · have hs := Fintype.sum_subtype_add_sum_subtype (fun i => t i ≠ 0) t
    have hz : (∑ i : {i // ¬ t i ≠ 0}, t i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact not_ne_iff.mp i.2
    rw [hz, add_zero, ht.2] at hs
    exact hs

 theorem normalized_strict (t : ι → ℝ) (ht : t ∈ balancedPolytope (ι := ι))
    (hlt : ∀ i, t i < 1 / 2) (hcard : 4 ≤ Fintype.card {i // t i ≠ 0}) :
    mean t < 1 / 2 := by
  rw [mean_restrict t (fun i => t i ≠ 0) (by intro i hi; exact not_ne_iff.mp hi)]
  exact normalized_strict_positive (fun i : {i // t i ≠ 0} => t i) (restrict_balanced t ht)
    (fun i => lt_of_le_of_ne (ht.1 i).1 (Ne.symm i.2)) (fun i => hlt i) hcard

 theorem normalized_small_finite {n : ℕ} (v : Fin n → ℝ)
    (hv : v ∈ balancedPolytope) (hn : n ≤ 3) : mean v = 1 / 2 := by
  obtain h | h | h | h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  · subst n
    have hs := hv.2
    simp at hs
  · subst n
    have hs := hv.2
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    have h0 := (hv.1 0).2
    linarith
  · subst n
    have hs := hv.2
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    have h0 := hv.1 0
    have h1 := hv.1 1
    have he : v 0 = 1 / 2 := by change v 0 + v 1 = 1 at hs; linarith
    have habs : (∑ i, |v i|) = 1 := by
      simp only [abs_of_nonneg (hv.1 _).1, hv.2]
    have h := mean_eq_half_of_half_mass v 0 (by rw [habs, abs_of_nonneg h0.1, he])
    simpa [habs] using h
  · subst n
    have hs := hv.2
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change v 0 + (v 1 + v 2) = 1 at hs
    have he : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    have h := mean_three_nonneg (v 0) (v 1) (v 2)
      (hv.1 0).1 (hv.1 1).1 (hv.1 2).1
      (by linarith [(hv.1 0).2]) (by linarith [(hv.1 1).2]) (by linarith [(hv.1 2).2])
    rw [← he] at h
    linarith

 theorem normalized_small_support (t : ι → ℝ) (ht : t ∈ balancedPolytope)
    (hcard : Fintype.card {i // t i ≠ 0} ≤ 3) : mean t = 1 / 2 := by
  let I := {i // t i ≠ 0}
  let E := (Fintype.equivFin I).symm
  let v : Fin (Fintype.card I) → ℝ := fun i => t (E i)
  have hv : v ∈ balancedPolytope := by
    constructor
    · intro i; exact ht.1 (E i)
    · have hs := (restrict_balanced t ht).2
      have he := Fintype.sum_equiv E (fun i => v i) (fun i : I => t i) (fun _ => rfl)
      exact he.trans hs
  have hm : mean v = mean t := by
    have he := mean_reindex E (fun i : I => t i)
    rw [← mean_restrict t (fun i => t i ≠ 0) (by intro i hi; exact not_ne_iff.mp hi)] at he
    exact he
  rw [← hm]
  exact normalized_small_finite v hv hcard

/-- Entry005 v4 Lemma 2.1 in its normalized form, with both equality mechanisms. -/
 theorem normalized_equality_iff (t : ι → ℝ) (ht : t ∈ balancedPolytope) :
    mean t = 1 / 2 ↔
      Fintype.card {i // t i ≠ 0} ≤ 3 ∨ ∃ i, t i = 1 / 2 := by
  constructor
  · intro he
    by_contra hn
    push Not at hn
    have hlt (i : ι) : t i < 1 / 2 := lt_of_le_of_ne (ht.1 i).2 (hn.2 i)
    have hstrict := normalized_strict t ht hlt (by omega)
    linarith
  · rintro (hc | ⟨i, hi⟩)
    · exact normalized_small_support t ht hc
    · have habs : (∑ j, |t j|) = 1 := by
        simp only [abs_of_nonneg (ht.1 _).1, ht.2]
      have he := mean_eq_half_of_half_mass t i (by rw [habs, abs_of_nonneg (ht.1 i).1, hi])
      simpa [habs] using he

/-- Full entry005 v4 Lemma 2.1, including the zero case and arbitrary finite real coefficients. -/
 theorem balanced_equality_iff (c : ι → ℝ)
    (hbal : ∀ i, |c i| ≤ (∑ j, |c j|) / 2) :
    mean c = (∑ j, |c j|) / 2 ↔
      Fintype.card {i // c i ≠ 0} ≤ 3 ∨ ∃ i, |c i| = (∑ j, |c j|) / 2 := by
  let M : ℝ := ∑ j, |c j|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  by_cases hzero : M = 0
  · have hc : c = 0 := by
      funext i
      have h := hbal i
      change |c i| ≤ M / 2 at h
      rw [hzero] at h
      have habs : |c i| = 0 := by linarith [abs_nonneg (c i)]
      exact abs_eq_zero.mp habs
    rw [hc]
    simp [mean_zero]
  · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let t : ι → ℝ := fun i => |c i| / M
    have ht : t ∈ balancedPolytope := by
      constructor
      · intro i
        constructor
        · exact div_nonneg (abs_nonneg _) hM
        · apply (div_le_iff₀ hpos).2
          have h := hbal i
          change |c i| ≤ M / 2 at h
          linarith
      · simp only [t, div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ hzero
    have hscale : M • t = fun i => |c i| := by
      funext i
      change M * (|c i| / M) = |c i|
      field_simp
    have hm := mean_smul M t
    rw [hscale, mean_abs, abs_of_pos hpos] at hm
    have heq : mean c = M / 2 ↔ mean t = 1 / 2 := by
      constructor
      · intro h
        apply (mul_left_cancel₀ hzero)
        rw [← hm, h]
        ring
      · intro h
        rw [hm, h]
        ring
    have hsupp (i : ι) : t i ≠ 0 ↔ c i ≠ 0 := by
      simp [t, div_eq_zero_iff, hzero]
    have hcard : Fintype.card {i // t i ≠ 0} = Fintype.card {i // c i ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hsupp)
    have hhalf (i : ι) : t i = 1 / 2 ↔ |c i| = M / 2 := by
      change |c i| / M = 1 / 2 ↔ |c i| = M / 2
      rw [div_eq_iff hzero]
      constructor <;> intro h <;> linarith
    change mean c = M / 2 ↔ _
    rw [heq, normalized_equality_iff t ht, hcard]
    simp_rw [hhalf]
    rfl

end Mxym.Rademacher
