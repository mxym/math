/-
Generic shared-data coverage transfer replayed from OpenAI family028, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, https://github.com/openai/math.
Apache-2.0; see ../../upstream-028/LICENSE.
Exact selected declaration and proof bodies are preserved verbatim. Source spans:
GroupCoverage.lean 13--187, 328--441;
BackwardCoverage.lean 9--149, excluding nothing in this span, and 158--275;
PosteriorSampling.lean 9--275 (conditional block proofs are in GenericCoverage).
Gaussian imports and specialized wrappers are excluded. The namespace/section
contexts are recreated below. Every coverage-floor, exceptional-set, sampling-
error, and information-budget hypothesis remains explicit; the all-order
arithmetic/geometric instantiation is an application obligation.
-/
import Entry002.FiniteProbability

set_option autoImplicit false

namespace OAI
universe uGroup uOmega uAlpha uIota uBeta uCapitalGamma uGamma
namespace GaussianMoat
open scoped BigOperators Classical

section
variable {G : Type uGroup} [Fintype G] [AddGroup G]
noncomputable def overlapCount (K E : Finset G) (x : G) : ℕ :=
  (E.filter (fun y => x+y ∈ K)).card

lemma overlapCount_sum (K E : Finset G) :
    (∑ x : G, overlapCount K E x) = K.card*E.card := by
  simp only [overlapCount,Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (y : G) : (∑ x : G, if x+y ∈ K then (1:ℕ) else 0) = K.card := by
    calc
      _ = ∑ x : G, if x ∈ K then (1:ℕ) else 0 :=
        Equiv.sum_comp (Equiv.addRight y) (fun x => if x ∈ K then (1:ℕ) else 0)
      _ = K.card := by simp
  simp only [hh,Finset.sum_const,smul_eq_mul]
  ring

noncomputable def overlapExceptions (K E : Finset G) (δ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => δ*K.card < overlapCount K E x)

lemma overlapExceptions_card (K E : Finset G) (hK : K.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ((overlapExceptions K E δ).card:ℝ) ≤ E.card/δ := by
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hs : ((overlapExceptions K E δ).card:ℝ)*(δ*K.card) ≤
      ∑ x : G, (overlapCount K E x:ℝ) := by
    have h1 : ∑ x ∈ overlapExceptions K E δ, δ*K.card ≤
        ∑ x ∈ overlapExceptions K E δ, (overlapCount K E x:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (overlapExceptions K E δ))
      (fun x _ _ => (Nat.cast_nonneg (overlapCount K E x): (0:ℝ)≤_))
    simpa only [Finset.sum_const,nsmul_eq_mul] using h1.trans h2
  have he : (∑ x : G, (overlapCount K E x:ℝ)) = (K.card:ℝ)*E.card := by
    exact_mod_cast overlapCount_sum K E
  rw [he] at hs
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hs,hKp]

lemma coverage_hit_lower (q : FinLaw G) (K E : Finset G) {τ δ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y)
    {x : G} (hx : x ∉ overlapExceptions K E δ) :
    (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ q.prob (fun y => x+y ∈ K) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hoc : (overlapCount K E x:ℝ) ≤ δ*K.card := by
    simpa only [overlapExceptions,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hx
  let S := Finset.univ.filter (fun y : G => x+y ∈ K ∧ y ∉ E)
  have hcount : (S.card:ℝ)+(overlapCount K E x:ℝ) = K.card := by
    have ht : S.card+overlapCount K E x=K.card := by
      have hbase : (Finset.univ.filter (fun y : G => x+y ∈ K)).card = K.card := by
        simp only [Finset.card_filter]
        calc
          _ = ∑ y : G, if y ∈ K then (1:ℕ) else 0 :=
            Equiv.sum_comp (Equiv.addLeft x) (fun y => if y ∈ K then (1:ℕ) else 0)
          _ = K.card := by simp
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun y : G => x+y ∈ K)) (p := fun y => y ∈ E)
      have hE : ((Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∈ E)).card =
          overlapCount K E x := by
        unfold overlapCount
        congr 1
        ext y
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      have hS : (Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∉ E) = S := by
        ext y
        simp [S]
      rw [hE,hS,hbase] at hsplit
      omega
    exact_mod_cast ht
  have h1 : (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) ≤ ∑ y ∈ S, q y := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s := S)
      (fun y hy => hq y (Finset.mem_filter.mp hy).2.2)
  have h2 : (∑ y ∈ S, q y) ≤ q.prob (fun y => x+y ∈ K) := by
    have he : q.prob (fun y => x+y ∈ K) =
        ∑ y ∈ Finset.univ.filter (fun y : G => x+y ∈ K), q y := by
      simp only [FinLaw.prob,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : x+y ∈ K <;> simp only [hy,ite_true,ite_false]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,(Finset.mem_filter.mp hy).2.1⟩
    · intro y _ _
      exact q.nonneg y
  have h3 : (τ+2*δ)*K.card ≤ S.card*(τ+4*δ) := by
    have hc : (0:ℝ) ≤ K.card := Nat.cast_nonneg _
    have hd : τ+2*δ ≤ (1-δ)*(τ+4*δ) := by nlinarith only [hτ1,hδ1,hδ]
    have hm := mul_le_mul_of_nonneg_right hd hc
    have hs : (1-δ)*(K.card:ℝ) ≤ S.card := by linarith only [hcount,hoc]
    have ht := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ τ+4*δ)
    nlinarith only [hm,ht]
  calc
    _ ≤ (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) := by
      simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hp).mpr h3
    _ ≤ _ := h1.trans h2

noncomputable def coverageList (K : Finset G) (n : ℕ) (τ δ : ℝ) (h : Fin n → G) : Finset G :=
  Finset.univ.filter (fun x =>
    (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
      n*(τ+δ)*K.card/(Fintype.card G:ℝ))

theorem coverageList_tail (q : FinLaw G) (K E : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y) (n : ℕ) :
    (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  let μ := (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ)
  let d := δ*(K.card:ℝ)/(Fintype.card G:ℝ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hx (x : G) : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
      x ∉ overlapExceptions K E δ) ≤
      Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
    by_cases he : x ∈ overlapExceptions K E δ
    · simp only [he,not_true_eq_false,and_false,FinLaw.prob,ite_false,Finset.sum_const_zero]
      exact (Real.exp_pos _).le
    · have hh := q.iid_lower_tail (fun y => x+y ∈ K) n hμ hd
        (coverage_hit_lower q K E hτ hτ1 hδ hδ1 hq he)
      have hth : (n:ℝ)*(μ-d) = (n:ℝ)*(τ+δ)*K.card/(Fintype.card G:ℝ) := by
        dsimp [μ,d]
        ring
      rw [hth] at hh
      have hm : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
          x ∉ overlapExceptions K E δ) ≤
          (q.iid n).prob (fun h =>
            (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
              n*(τ+δ)*K.card/(Fintype.card G:ℝ)) := by
        apply FinLaw.prob_mono
        intro h hh
        exact (Finset.mem_filter.mp hh.1).2
      apply (hm.trans (by
        convert! hh using 1
        congr 1
        funext v
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x+v i ∈ K <;> simp only [hi,ite_true,ite_false])).trans
      apply Real.exp_le_exp.mpr
      have heq : d^2/μ = δ^2*(K.card:ℝ)/((τ+2*δ)*(Fintype.card G:ℝ)) := by
        dsimp [d,μ]
        field_simp
      have ht : 0 < τ+2*δ := by positivity
      have ht1 : τ+2*δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hratio : δ^2*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ d^2/μ := by
        rw [heq]
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos ht hp)
        exact mul_le_of_le_one_left hp.le ht1
      have hmul := mul_le_mul_of_nonneg_left hratio (show (0:ℝ) ≤ n/2 by positivity)
      calc
        _ = -((n:ℝ)/2*(d^2/μ)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ -((n:ℝ)/2*(δ^2*(K.card:ℝ)/(Fintype.card G:ℝ))) := neg_le_neg hmul
        _ = _ := by ring
  have hu := (q.iid n).prob_exists_le_sum (fun x h => x ∈ coverageList K n τ δ h ∧
    x ∉ overlapExceptions K E δ)
  have hm : (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (q.iid n).prob (fun h => ∃ x, x ∈ coverageList K n τ δ h ∧ x ∉ overlapExceptions K E δ) := by
    apply FinLaw.prob_mono
    intro h hh
    by_contra hn
    apply hh
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  apply (hm.trans hu).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)

end

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype Γ] [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in
lemma prob_mem_finset (p : FinLaw G) (K : Finset G) :
    p.prob (fun x => x ∈ K) = ∑ x ∈ K, p x := by
  unfold prob
  calc
    _ = ∑ x ∈ K, if x ∈ K then p x else 0 := by
      symm
      convert! Finset.sum_subset (Finset.subset_univ K)
        (f := fun x => if x ∈ K then p x else (0:ℝ))
        (fun x _ hx => ite_eq_right hx) using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x∈K <;> simp only [hx,ite_true,ite_false]
    _ = _ := Finset.sum_congr rfl (fun x hx => ite_eq_left hx)

lemma joint_prob_le_bad_add (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Bad : Ω → Prop) (E : Ω × Γ → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ ω, ¬ Bad ω → (q ω).prob (fun a => E (ω,a)) ≤ ε) :
    (p.joint q).prob E ≤ p.prob Bad+ε := by
  rw [prob_joint]
  have h (ω : Ω) : (q ω).prob (fun a => E (ω,a)) ≤ (if Bad ω then 1 else 0)+ε := by
    by_cases hb : Bad ω
    · simpa only [hb,ite_true] using (q ω).prob_le_one (fun a => E (ω,a)) |>.trans (by linarith only [hε])
    · simpa only [hb,ite_false,zero_add] using hg ω hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  convert! hh using 1
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,one_mul,prob]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

omit [Fintype G] in

lemma iid_true_hit_expect (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (n : ℕ) :
    (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) =
      n*(p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) := by
  rw [joint_expect_snd p (fun ω => (q ω).iid n)
    (fun ω v => ∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)]
  have he (i : Fin n) (ω : Ω) :
      (∑ v, (q ω).iid n v*(if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        (q ω).prob (fun a => Y ω+h a ∈ K) := by
    rw [← expect_map ((q ω).iid n) (fun v => v i) (fun a => if Y ω+h a ∈ K then (1:ℝ) else 0),
      iid_map_eval]
    unfold prob
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hh (ω : Ω) :
      (∑ v, (q ω).iid n v*(∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        n*(q ω).prob (fun a => Y ω+h a ∈ K) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [hh,mul_left_comm (p _) (n:ℝ)]
  rw [← Finset.mul_sum,prob_joint p q (fun v => Y v.1+h v.2∈K)]

lemma true_coverageList_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) ≤
      τ*K.card/(Fintype.card G:ℝ)) :
    δ/(τ+δ) ≤ (p.joint (fun ω => (q ω).iid n)).prob
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i))) := by
  have hG : Nonempty G := ⟨Y (Classical.choice p.nonempty)⟩
  have hcard : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hkc : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hnc : (0:ℝ) < n := by exact_mod_cast hn
  have htd : 0 < τ+δ := by linarith
  have hb : (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) ≤
        n*(τ*K.card/(Fintype.card G:ℝ)) := by
    rw [iid_true_hit_expect]
    exact mul_le_mul_of_nonneg_left hp hnc.le
  have hh := (p.joint (fun ω => (q ω).iid n)).prob_le_of_expect
    (fun v => ∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)
    (fun _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (t := n*(τ+δ)*K.card/(Fintype.card G:ℝ)) (by positivity) hb
  have he : 1-(n*(τ*K.card/(Fintype.card G:ℝ)))/(n*(τ+δ)*K.card/(Fintype.card G:ℝ)) =
      δ/(τ+δ) := by field_simp; ring
  rw [he] at hh
  simpa only [coverageList,Finset.mem_filter,Finset.mem_univ,true_and] using hh

lemma coverageList_size_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (h : Γ → G) (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G)
    (Bad : Ω → Prop) {τ δ ε b : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hε : 0 ≤ ε) (n : ℕ)
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω,
      (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ ≤ b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) ≤ ε) :
    (p.joint (fun ω => (q ω).iid n)).prob (fun v =>
      b < ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)) ≤ p.prob Bad+ε := by
  apply joint_prob_le_bad_add p _ Bad _ hε
  intro ω hg
  have ha := (coverageList_tail ((q ω).map h) K (E ω) hK hτ hτ1 hδ hδ1 (hq ω hg) n).trans herr
  rw [← iid_map,prob_map] at ha
  apply (prob_mono _ ?_).trans ha
  intro x hx hs
  have hc := Finset.card_le_card hs
  have hcR : ((coverageList K n τ δ (fun i => h (x i))).card:ℝ) ≤
      ((overlapExceptions K (E ω) δ).card:ℝ) := by exact_mod_cast hc
  have hb := (overlapExceptions_card K (E ω) hK hδ).trans (hE ω hg)
  linarith only [hx,hcR,hb]

end FinLaw

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma short_list_probability_deficit (p : FinLaw Ω) (X : Ω → α) (C : Ω → β)
    (L : β → Finset α) {b : ℝ} (hb : 1 ≤ b) :
    let a := p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)
    a*(Real.log (Fintype.card α)-Real.log b)-Real.binEntropy a ≤
      Real.log (Fintype.card α)-p.cHf X C := by
  dsimp only
  have hh := p.short_list_deficit X C L
    (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)) hb
    (fun ω _ he => of_decide_eq_true he)
  have ha : (p.map (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b))) true =
      p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b) := by
    simp only [map_mass,decide_eq_true_eq,prob]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [ha] at hh
  simpa only [condH,← Hf_eq_H,cHf] using hh

lemma average_deficit_lower {ι : Type uIota} [Fintype ι] (w : FinLaw ι)
    (a d : ι → ℝ) {a₀ v : ℝ} (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (ha₀ : 0 < a₀) (hav : a₀ ≤ ∑ i, w i*a i)
    (hv : 2*(1-Real.log a₀) ≤ v)
    (hdef : ∀ i, a i*v-Real.binEntropy (a i) ≤ d i) :
    a₀*v/2 ≤ ∑ i, w i*d i := by
  let A := ∑ i, w i*a i
  have hA : 0 < A := lt_of_lt_of_le ha₀ hav
  have hA1 : A ≤ 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (ha i).2 (w.nonneg i))
    simpa only [mul_one,w.sum_one] using hh
  have ha₀1 : a₀ ≤ 1 := hav.trans hA1
  have hl : Real.log a₀ ≤ Real.log A := Real.log_le_log ha₀ hav
  have hl0 : Real.log a₀ ≤ 0 := Real.log_nonpos ha₀.le ha₀1
  have hv0 : 0 ≤ v := by linarith only [hv,hl0]
  have hh := w.binEntropy_sum_le a ha
  have hp := binEntropy_le_log_inverse hA hA1
  have hdl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hdef i) (w.nonneg i))
  rw [show (∑ i, w i*(a i*v-Real.binEntropy (a i))) =
      A*v-∑ i, w i*Real.binEntropy (a i) by
        simp only [mul_sub,Finset.sum_sub_distrib,← mul_assoc,← Finset.sum_mul,A]] at hdl
  have hlog := mul_le_mul_of_nonneg_left hl hA.le
  have hmult := mul_le_mul_of_nonneg_left hv hA.le
  have ham := mul_le_mul_of_nonneg_right hav hv0
  change (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy A at hh
  nlinarith only [hdl,hh,hp,hlog,hmult,ham]

theorem shared_coverage_deficit {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Γ] [Fintype G] [AddCommGroup G]
    (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Y : Ω → G) (h : Γ → G)
    (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G) (Bad : Ω → Prop)
    {τ δ ε b : ℝ} {n : ℕ} (hn : 0<n)
    (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hb : 1≤b)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2∈K) ≤ τ*K.card/(Fintype.card G:ℝ))
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω, (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ≤b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ)))≤ε) :
    let P := p.joint (fun ω => (q ω).iid n)
    let L := fun v : Fin n → Γ => coverageList K n τ δ (fun i => h (v i))
    let a := P.prob (fun v => Y v.1 ∈ L v.2 ∧ ((L v.2).card:ℝ)≤b)
    δ/(τ+δ)-p.prob Bad-ε ≤ a ∧
      a*(Real.log (Fintype.card G)-Real.log b)-Real.binEntropy a ≤
        Real.log (Fintype.card G)-P.cHf (fun v => Y v.1) Prod.snd := by
  dsimp only
  constructor
  · have htrue := p.true_coverageList_probability q Y h K hK hτ hδ hn hp
    have hsize := p.coverageList_size_probability q h K hK E Bad hτ hτ1 hδ hδ1 hε n hq hE herr
    have hi := (p.joint (fun ω => (q ω).iid n)).prob_inter_ge
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i)))
      (fun v => ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)≤b)
    simp only [not_le] at hi
    linarith only [htrue,hsize,hi]
  · exact short_list_probability_deficit (p.joint (fun ω => (q ω).iid n))
      (fun v => Y v.1) Prod.snd
      (fun v => coverageList K n τ δ (fun i => h (v i))) hb

end FinLaw

lemma perm_expect_apply {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i)) = 𝔼 j, f j := by
  let : Nonempty ι := ⟨i⟩
  calc
    _ = 𝔼 j : ι, 𝔼 π : Equiv.Perm ι, f (π j) := by
      rw [show (fun j : ι => 𝔼 π : Equiv.Perm ι, f (π j)) =
        (fun _ => 𝔼 π : Equiv.Perm ι, f (π i)) by
          funext j; exact perm_expect_exchange f j i]
      simp only [Fintype.expect_const]
    _ = 𝔼 π : Equiv.Perm ι, 𝔼 j : ι, f (π j) := Finset.expect_comm _ _ _
    _ = _ := by
      have he (π : Equiv.Perm ι) : (𝔼 j, f (π j)) = 𝔼 j, f j :=
        Fintype.expect_equiv π _ _ (fun _ => rfl)
      simp only [he,Fintype.expect_const]

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] {k : ℕ}

lemma Hf_sub_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf X-p.Hf Y ≤ p.cHf X Y := by
  have h := p.Hf_pair_ge_snd Y X
  rw [p.Hf_pair_comm Y X] at h
  exact sub_le_sub_right h _

lemma orderedEntropy_conditioning (p : FinLaw Ω) (X : Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.orderedEntropy X b-p.Hf C ≤
      b*(𝔼 i : Fin k, p.cHf (fun ω => X ω i) C) := by
  have hh (π : Equiv.Perm (Fin k)) :
      p.Hf (prefixVar X π b)-p.Hf C ≤
        ∑ i : Fin b, p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C := by
    apply (p.Hf_sub_le_cHf _ C).trans
    apply (p.cHf_le_of_determined _
      (fun ω (i : Fin b) => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C ?_).trans
      (p.cHf_fintype_subadd _ C)
    intro ω ν hx _
    funext i
    by_cases hi : i.val<b
    · simpa only [prefixVar,hi,ite_eq_left] using congrArg some (congrFun hx ⟨i.val,hi⟩)
    · simp only [prefixVar,hi,ite_false]
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hh π)
  have he (i : Fin b) :
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C) =
        𝔼 j : Fin k, p.cHf (fun ω => X ω j) C :=
    perm_expect_apply (fun j => p.cHf (fun ω => X ω j) C) _
  simpa only [orderedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.expect_sum_comm,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using hav

lemma signedEntropy_conditioning (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.signedEntropy X b-p.Hf C ≤
      b*(𝔼 σ : Fin k → Bool, 𝔼 i : Fin k, p.cHf (fun ω => X σ ω i) C) := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    p.orderedEntropy_conditioning (X σ) C hb)
  simpa only [signedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.mul_expect] using h

end FinLaw


namespace FinLaw

section

theorem backward_coverage_step {Ω : Type uOmega} {Γ : Type uCapitalGamma} {ι : Type uIota} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (Bad₀ : ι → Prop) (Bad₁ : ι → Ω → Prop)
    (K : (i : ι) → Finset (G i)) (E : (i : ι) → Ω → Finset (G i))
    (b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0 < n) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/64) (hε : 0 ≤ ε) (hη : 0 < η)
    (hnext : ∑ i, w i*p.prob (Bad₁ i) ≤ η')
    (hsmall : η'+ε ≤ η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2)) ≤ v)
    (hgap : e < η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd)) ≤ e)
    (hK : ∀ i, Bad₀ i → (K i).Nonempty)
    (hb : ∀ i, Bad₀ i → 1 ≤ b i)
    (hv : ∀ i, Bad₀ i → v ≤ Real.log (Fintype.card (G i))-Real.log (b i))
    (hp : ∀ i, Bad₀ i → (p.joint q).prob (fun x => Y i x.1+h i x.2 ∈ K i) ≤
      τ*(K i).card/(Fintype.card (G i):ℝ))
    (hq : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ∀ y ∉ E i ω,
      (τ+4*δ)/(Fintype.card (G i):ℝ) ≤ (q ω).map (h i) y)
    (hE : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ((E i ω).card:ℝ)/δ ≤ b i)
    (herr : ∀ i, Bad₀ i → (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*(K i).card/(2*(Fintype.card (G i):ℝ))) ≤ ε) :
    w.prob Bad₀ ≤ η := by
  let P := p.joint (fun ω => (q ω).iid n)
  let L := fun i (x : Fin n → Γ) => coverageList (K i) n τ δ (fun j => h i (x j))
  let a := fun i => if Bad₀ i then P.prob
    (fun x => Y i x.1 ∈ L i x.2 ∧ ((L i x.2).card:ℝ) ≤ b i) else 0
  let d := fun i => Real.log (Fintype.card (G i))-P.cHf (fun x => Y i x.1) Prod.snd
  have hd (i : ι) : 0 ≤ d i := by
    exact sub_nonneg.mpr ((P.cHf_le_Hf _ _).trans (P.Hf_le_log_card_type _))
  have ha (i : ι) : a i ∈ Set.Icc (0:ℝ) 1 := by
    dsimp only [a]
    split_ifs
    · exact ⟨P.prob_nonneg _,P.prob_le_one _⟩
    · norm_num
  have hstep (i : ι) (hi : Bad₀ i) :
      δ-p.prob (Bad₁ i)-ε ≤ a i ∧ a i*v-Real.binEntropy (a i) ≤ d i := by
    have hh := shared_coverage_deficit p q (Y i) (h i) (K i) (hK i hi) (E i) (Bad₁ i)
      hn hτ hτ1 hδ hδ1 hε (hb i hi) (hp i hi) (hq i hi) (hE i hi) (herr i hi)
    dsimp only at hh
    have hh' : δ/(τ+δ)-p.prob (Bad₁ i)-ε ≤ a i ∧
        a i*(Real.log (Fintype.card (G i))-Real.log (b i))-Real.binEntropy (a i) ≤ d i := by
      simpa only [a,hi,ite_eq_left,P,L,d] using hh
    constructor
    · have htd : 0 < τ+δ := by linarith only [hτ,hδ]
      have htd1 : τ+δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hfrac : δ ≤ δ/(τ+δ) := (le_div_iff₀ htd).mpr (by nlinarith only [htd1,hδ])
      linarith only [hh'.1,hfrac]
    · have hm := mul_le_mul_of_nonneg_left (hv i hi) (ha i).1
      linarith only [hh'.2,hm]
  have hl (i : ι) : δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε ≤ a i := by
    by_cases hi : Bad₀ i
    · simpa only [hi,ite_true,mul_one] using (hstep i hi).1
    · simp only [hi,ite_false,mul_zero,a]
      linarith only [p.prob_nonneg (Bad₁ i),hε]
  have hdef (i : ι) : a i*v-Real.binEntropy (a i) ≤ d i := by
    by_cases hi : Bad₀ i
    · exact (hstep i hi).2
    · simpa only [a,hi,ite_false,Real.binEntropy_zero,zero_mul,sub_zero] using hd i
  by_contra hc
  have hθη : η < w.prob Bad₀ := lt_of_not_ge hc
  have hlavg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hl i) (w.nonneg i))
  have heq : (∑ i, w i*(δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε)) =
      δ*w.prob Bad₀-(∑ i, w i*p.prob (Bad₁ i))-ε := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,w.sum_one,one_mul,prob,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq] at hlavg
  have hav : η*δ/2 ≤ ∑ i, w i*a i := by
    have hm := mul_le_mul_of_nonneg_left hθη.le hδ.le
    linarith only [hlavg,hm,hnext,hsmall]
  have hbnd := average_deficit_lower w a d ha (by positivity : 0 < η*δ/2) hav hscale hdef
  change (∑ i, w i*d i) ≤ e at hdata
  nlinarith only [hbnd,hdata,hgap]

variable {Ω : Type uOmega} {G : Type uGroup} [Fintype Ω] [Fintype G]

theorem low_mass_average {ι : Type uIota} [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (w : FinLaw ι) (p : (i : ι) → FinLaw (G i))
    (K : (i : ι) → Finset (G i)) (Bad : ι → Prop) {b e : ℝ}
    (hb : 0 < b)
    (hK : ∀ i, ∀ x ∈ K i, p i x ≤ (3/8:ℝ)/(Fintype.card (G i):ℝ))
    (hbad : ∀ i, Bad i → b ≤ ((K i).card:ℝ)/(8*(Fintype.card (G i):ℝ)))
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy)) ≤ e) :
    w.prob Bad ≤ e/b := by
  have h (i : ι) : b*(if Bad i then (1:ℝ) else 0) ≤
      Real.log (Fintype.card (G i))-(p i).entropy := by
    by_cases hi : Bad i
    · simp only [hi,ite_true,mul_one]
      exact (hbad i hi).trans ((p i).low_mass_deficit (K i) (by
        intro x hx
        convert hK i x hx using 1; ring))
    · simp only [hi,ite_false,mul_zero]
      exact sub_nonneg.mpr (p i).entropy_le_log_card
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (h i) (w.nonneg i))
  have he : (∑ i, w i*(b*(if Bad i then (1:ℝ) else 0)))=b*w.prob Bad := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he] at hs
  apply (le_div_iff₀ hb).mpr
  linarith only [hs,hdef]

end

end FinLaw

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

lemma prob_and_split (p : FinLaw Ω) (A B : Ω → Prop) :
    p.prob (fun ω => A ω ∧ B ω)+p.prob (fun ω => A ω ∧ ¬B ω)=p.prob A := by
  simp only [prob,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha,hb]

lemma prob_mix (p : FinLaw Ω) (q : Ω → FinLaw Γ) (E : Γ → Prop) :
    (p.mix q).prob E = ∑ ω, p ω*(q ω).prob E := by
  rw [← joint_map_snd,prob_map,prob_joint]

lemma posterior_unfavorable (p : FinLaw Ω) (C : Ω → α) (Bad : Ω → Prop) :
    (p.map C).prob (fun a => (1/2:ℝ)<(p.conditionOn C a).prob Bad) ≤ 2*p.prob Bad := by
  have h := (p.map C).prob_le_expect_div (fun a => (p.conditionOn C a).prob Bad)
    (fun a => (p.conditionOn C a).prob_nonneg _) (by norm_num : (0:ℝ)<1/2)
  rw [p.conditionOn_prob] at h
  linarith only [h]

lemma mixed_exception_card (p : FinLaw Ω) (Good : Ω → Prop) (E : Ω → Finset G)
    {e : ℝ} (he : 0≤e) (hE : ∀ ω, Good ω → ((E ω).card:ℝ)≤e)
    (hG : (1/2:ℝ)≤p.prob Good) :
    ((Finset.univ.filter (fun x : G =>
      p.prob (fun ω => Good ω ∧ x∉E ω)<1/4)).card:ℝ) ≤ 4*e := by
  let u := fun x => p.prob (fun ω => Good ω ∧ x∉E ω)
  let f := fun x => p.prob (fun ω => Good ω ∧ x∈E ω)
  let K := Finset.univ.filter (fun x : G => u x<1/4)
  have hsum : (∑ x : G, f x) ≤ e := by
    simp only [f,prob]
    rw [Finset.sum_comm]
    have hh (ω : Ω) : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) ≤ p ω*e := by
      by_cases hg : Good ω
      · have hc : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) = p ω*(E ω).card := by
          simp only [hg,true_and]
          calc
            _ = ∑ x : G, p ω*(if x∈E ω then (1:ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              split_ifs <;> simp
            _ = _ := by rw [← Finset.mul_sum]; simp
        rw [hc]
        exact mul_le_mul_of_nonneg_left (hE ω hg) (p.nonneg ω)
      · simp only [hg,false_and,ite_false,Finset.sum_const_zero]
        exact mul_nonneg (p.nonneg ω) he
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hh ω)
    simp only [← Finset.sum_mul,p.sum_one,one_mul] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  have hk (x : G) (hx : x∈K) : (1/4:ℝ)≤f x := by
    have h := p.prob_and_split Good (fun ω => x∈E ω)
    have hu : u x<1/4 := (Finset.mem_filter.mp hx).2
    change f x+u x=p.prob Good at h
    linarith only [hu,h,hG]
  have hl : (K.card:ℝ)/4 ≤ ∑ x∈K, f x := by
    have h := Finset.sum_le_sum (s := K) (fun x hx => hk x hx)
    simpa only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul] using h
  have hr : (∑ x∈K, f x) ≤ ∑ x:G, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
      (fun x _ _ => p.prob_nonneg _)
  change (K.card:ℝ)≤4*e
  linarith only [hl,hr,hsum]

omit [Fintype G] in
lemma mixed_floor (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Good : Ω → Prop)
    (E : Ω → Finset G) (hit : Γ → G → Prop) {τ : ℝ} (hτ : 0≤τ)
    (hq : ∀ ω, Good ω → ∀ x∉E ω, τ≤(q ω).prob (fun v => hit v x))
    (x : G) (hx : (1/4:ℝ)≤p.prob (fun ω => Good ω ∧ x∉E ω)) :
    τ/4 ≤ (p.mix q).prob (fun v => hit v x) := by
  rw [prob_mix]
  have h (ω : Ω) : τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0) ≤ (q ω).prob (fun v => hit v x) := by
    by_cases hg : Good ω ∧ x∉E ω
    · rw [ite_eq_left hg,mul_one]
      exact hq ω hg.1 x hg.2
    · rw [ite_eq_right hg,mul_zero]
      exact (q ω).prob_nonneg _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  have he : (∑ ω, p ω*(τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0))) =
      τ*p.prob (fun ω => Good ω ∧ x∉E ω) := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hx hτ
  linarith only [hh,hm]

lemma prob_exists_eq_sum_disjoint {ι : Type uIota} [Fintype ι]
    (p : FinLaw Ω) (E : ι → Ω → Prop)
    (h : ∀ ω i j, E i ω → E j ω → i=j) :
    p.prob (fun ω => ∃ i, E i ω) = ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := he
    rw [ite_eq_left ⟨i,hi⟩,Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (h ω j i hj hi))
    · simp
  · simp only [ite_eq_right he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => he ⟨i,hi⟩)

end FinLaw

section
namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype ι] [Fintype α] [Fintype β]

lemma Hf_id (p : FinLaw Ω) : p.Hf id = p.entropy := by rw [Hf_eq_H,H,map_id]

lemma cHf_joint_fst (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → γ) :
    (p.joint q).cHf (fun v => X v.1 v.2) Prod.fst = ∑ i, p i*(q i).Hf (X i) := by
  unfold cHf
  rw [Hf_pair_comm,Hf_joint_pair_vary]
  have h := (p.joint q).Hf_map Prod.fst id
  rw [joint_map_fst,Hf_id] at h
  change p.entropy = (p.joint q).Hf Prod.fst at h
  rw [← h]
  ring

lemma joint_iid_eval (p : FinLaw ι) (q : ι → FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.joint (fun a => (q a).iid n)).map (fun v => (v.1,v.2 i)) = p.joint q := by
  calc
    _ = p.joint (fun a => ((q a).iid n).map (fun x : Fin n → Ω => x i)) :=
      joint_map_second p (fun a => (q a).iid n) (fun x : Fin n → Ω => x i)
    _ = _ := by simp only [iid_map_eval]

theorem conditional_iid_information (p : FinLaw (α × β)) (q : α × β → FinLaw Ω) (n : ℕ) :
    (p.joint (fun a => (q a).iid n)).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  let Q := p.joint q
  have hsub := P.cHf_fintype_subadd Prod.snd (fun v => v.1.1)
  have hmarg (i : Fin n) : P.cHf (fun v => v.2 i) (fun v => v.1.1) =
      Q.cHf Prod.snd (fun v => v.1.1) := by
    have h := P.cHf_map (fun v => (v.1,v.2 i)) Prod.snd (fun v => v.1.1)
    rw [joint_iid_eval] at h
    exact h.symm
  simp only [hmarg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsub
  have hcond : P.cHf Prod.snd (fun v => (v.1.1,v.1.2)) =
      (n:ℝ)*Q.cHf Prod.snd (fun v => (v.1.1,v.1.2)) := by
    change P.cHf Prod.snd Prod.fst = (n:ℝ)*Q.cHf Prod.snd Prod.fst
    rw [cHf_joint_fst p (fun a => (q a).iid n) (fun _ x => x),
      cHf_joint_fst p q (fun _ x => x)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    change p a*((q a).iid n).Hf id = (n:ℝ)*(p a*(q a).Hf id)
    rw [Hf_id,Hf_id,entropy_iid]
    ring
  change P.cIf _ _ _ ≤ (n:ℝ)*Q.cIf _ _ _
  rw [P.cIf_comm,Q.cIf_comm]
  unfold cIf
  rw [hcond]
  nlinarith only [hsub]

end FinLaw

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

noncomputable def passingList (hit : Γ → G → Prop) (n : ℕ) (v : Fin n → Γ) : Finset G :=
  Finset.univ.filter (fun x => ∀ i, ¬ hit (v i) x)

lemma expect_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (E : Finset G) {c : ℝ} (hhit : ∀ x ∉ E, c≤q.prob (fun v => hit v x)) (n : ℕ) :
    (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) ≤
      (E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c) := by
  have hprob (x : G) (hx : x ∉ E) :
      (q.iid n).prob (fun v => x∈passingList hit n v) ≤ Real.exp (-(n:ℝ)*c) := by
    have hh := q.iid_survival_exp (fun v => ¬hit v x) n (c := c) (by
      rw [q.prob_compl]; linarith only [hhit x hx])
    simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have he : (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) =
      ∑ x : G, (q.iid n).prob (fun v => x∈passingList hit n v) := by
    have hc (v : Fin n → Γ) : ((passingList hit n v).card:ℝ) =
        ∑ x : G, if x∈passingList hit n v then (1:ℝ) else 0 := by simp
    simp only [hc,Finset.mul_sum,prob]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx : x∈passingList hit n v <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  rw [he]
  have hh (x : G) : (q.iid n).prob (fun v => x∈passingList hit n v) ≤
      (if x∈E then (1:ℝ) else 0)+Real.exp (-(n:ℝ)*c) := by
    by_cases hx : x∈E
    · simp only [hx,ite_true]
      exact ((q.iid n).prob_le_one _).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · simp only [hx,ite_false,zero_add]
      exact hprob x hx
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hh x)
  simpa only [Finset.sum_add_distrib,Finset.sum_boole,Finset.filter_mem_eq_inter,
    Finset.univ_inter,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs

lemma passingList_true (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (h : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    ∀ v, q.iid n v≠0 → x∈passingList hit n v := by
  intro v hv
  simp only [passingList,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  apply h
  intro hz
  apply hv
  change (∏ j : Fin n, q (v j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

lemma expect_log_le_log_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, p ω≠0 → 0<f ω) :
    (∑ ω, p ω*Real.log (f ω)) ≤ Real.log (∑ ω, p ω*f ω) := by
  let f' := fun ω => if p ω=0 then (1:ℝ) else f ω
  have hh := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun ω _ => p.nonneg ω) p.sum_one (fun ω _ => show 0<f' ω from by
      dsimp only [f']; split_ifs with hz; norm_num; exact hf ω hz)
  have he (ω : Ω) : p ω*f' ω=p ω*f ω := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  have hl (ω : Ω) : p ω*Real.log (f' ω)=p ω*Real.log (f ω) := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  simpa only [smul_eq_mul,he,hl] using hh

lemma expected_log_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (x : G) (htrue : ∀ v, q v≠0 → ¬hit v x)
    (E : Finset G) {c : ℝ} (hhit : ∀ y ∉ E, c≤q.prob (fun v => hit v y)) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤
      Real.log ((E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c)) := by
  have hp (v : Fin n → Γ) (hv : q.iid n v≠0) : (0:ℝ)<(passingList hit n v).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
  apply ((q.iid n).expect_log_le_log_expect (fun v => ((passingList hit n v).card:ℝ)) hp).trans
  apply Real.log_le_log ?_ (q.expect_card_passingList hit E hhit n)
  have hex : ∃ v, 0 < q.iid n v := by
    by_contra hh
    push Not at hh
    have hz : ∀ v, q.iid n v=0 := fun v => le_antisymm (hh v) ((q.iid n).nonneg v)
    have hs := (q.iid n).sum_one
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨v,hv⟩ := hex
  exact Finset.sum_pos' (fun v _ => mul_nonneg ((q.iid n).nonneg v) (Nat.cast_nonneg _))
    ⟨v,Finset.mem_univ v,mul_pos hv (hp v hv.ne')⟩

lemma conditional_passing_support (p : FinLaw Ω) (X : Ω → G) (C : Ω → α)
    (hit : α → G → Prop) (hs : ∀ ω, p ω≠0 → ¬hit (C ω) (X ω)) :
    p.cHf X C ≤ ∑ a, p.map C a*Real.log ((Finset.univ.filter (fun x => ¬hit a x)).card) := by
  have h := p.condH_le_support X C (fun a => Finset.univ.filter (fun x => ¬hit a x)) (by
    intro ω hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs ω hw)
  simpa only [condH,← Hf_eq_H,cHf] using h

end FinLaw
end

end GaussianMoat
end OAI

/- Complete exact generic body from PassingInformation.lean, upstream lines
2--259, under the same pinned source and license as above. Its only import is
replaced by the preceding replayed generic dependencies. -/

namespace OAI

universe uOmega uIota uGroup uAlpha uOutput uCapitalGamma uBeta uGamma uDelta

namespace GaussianMoat

namespace FinLaw
open scoped BigOperators Classical

lemma cHf_dpi_subadd {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (G : ι → Type uGroup) (p : FinLaw Ω) (X : (i : ι) → Ω → G i) {α : Type uAlpha} (C : Ω → α) :
    p.cHf (fun ω i => X i ω) C ≤ ∑ i, p.cHf (X i) C := by
  let Y := fun ω i => (⟨i,X i ω⟩ : Σ i, G i)
  have he : p.cHf (fun ω i => X i ω) C = p.cHf Y C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      constructor
      · intro h; funext i; exact congrArg (Sigma.mk i) (congrFun h i)
      · intro h; funext i; exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |> eq_of_heq
    · intro ω ν; rfl
  rw [he]
  apply (p.cHf_fintype_subadd Y C).trans
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  apply p.cHf_congr_fibers _ _ _ _
  · intro ω ν
    exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2,fun h => congrArg (Sigma.mk i) h⟩
  · intro ω ν; rfl

lemma joint_passing_entropy {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i)) :
    (p.joint (fun a => (q a).iid n)).cHf (fun v => v.1.2)
      (fun v => (v.1.1,v.2)) ≤
      ∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) := by
  let P := p.joint (fun a => (q a).iid n)
  let C := fun v : (O × (∀ i, G i)) × (Fin n → Γ) => (v.1.1,v.2)
  have hcoordinate (i : ι) :
      P.cHf (fun v => v.1.2 i) C ≤ ∑ v, P v*Real.log (passingList (hit i) n v.2).card := by
    have hh := P.conditional_passing_support (fun v => v.1.2 i) C
      (fun c x => ∃ j, hit i (c.2 j) x) (by
        intro v hv
        have hm : p v.1≠0 ∧ (q v.1).iid n v.2≠0 := mul_ne_zero_iff.mp hv
        have hx := (q v.1).passingList_true (hit i) (v.1.2 i)
          (fun a ha => htrue v.1 hm.1 a ha i) n v.2 hm.2
        simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using hx)
    have hh' : P.cHf (fun v => v.1.2 i) C ≤
        ∑ c, (P.map C) c * Real.log (passingList (hit i) n c.2).card := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro c _
      simp only [passingList,not_exists]
    rw [expect_map] at hh'
    exact hh'
  have hs := P.cHf_dpi_subadd G (fun i v => v.1.2 i) C
  apply hs.trans
  apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoordinate i)).trans
  apply le_of_eq
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,← mul_assoc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [P,joint_mass]

theorem passing_information_lower {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i))
    (Bad : ι → O × (∀ i, G i) → Prop) {A e η : ℝ} (hA : 0≤A)
    (hH : (∑ i, Real.log (Fintype.card (G i)))-e ≤ p.cHf Prod.snd Prod.fst)
    (hBad : (∑ i, p.prob (Bad i)) ≤ η)
    (hlist : ∀ a, p a≠0 → ∀ i,
      (∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1)) :
    A*((Fintype.card ι:ℝ)-η)-e ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  have hcond := joint_passing_entropy G p q hit n htrue
  have hsum : (∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card)) ≤
      (∑ i, Real.log (Fintype.card (G i)))-A*((Fintype.card ι:ℝ)-∑ i, p.prob (Bad i)) := by
    calc
      _ ≤ ∑ a, p a*(∑ i, (Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1))) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : p a=0
        · simp only [ha,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlist a ha i)) (p.nonneg a)
      _ = _ := by
        simp only [Finset.sum_sub_distrib,mul_sub,
          ← Finset.sum_mul,p.sum_one,one_mul]
        congr 1
        rw [mul_comm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hh (i : ι) : (∑ a, p a*(if Bad i a then (0:ℝ) else 1))=1-p.prob (Bad i) := by
          rw [← p.prob_compl]
          unfold prob
          apply Finset.sum_congr rfl
          intro a _
          by_cases hb : Bad i a <;> simp [hb]
        have hh' (i : ι) : (∑ a, p a*(A*(if Bad i a then (0:ℝ) else 1)))=
            A*(1-p.prob (Bad i)) := by
          rw [← hh i,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        simp only [hh',mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,
          Finset.card_univ,nsmul_eq_mul]
  have hinit : P.cHf (fun v => v.1.2) (fun v => v.1.1)=p.cHf Prod.snd Prod.fst := by
    have hh := P.cHf_map Prod.fst Prod.snd Prod.fst
    rw [joint_map_fst] at hh
    exact hh.symm
  have hlow : A*((Fintype.card ι:ℝ)-η)-e ≤
      P.cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
    unfold cIf
    rw [hinit]
    have hm := mul_le_mul_of_nonneg_left hBad hA
    change P.cHf (fun v => v.1.2) (fun v => (v.1.1,v.2)) ≤ _ at hcond
    linarith only [hH,hcond,hsum,hm]
  exact hlow.trans (conditional_iid_information p q n)

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} [Fintype Ω] [Fintype α] [Fintype Γ]

lemma conditionOn_support (p : FinLaw Ω) (C : Ω → α) (a : α)
    (ha : p.map C a≠0) (ω : Ω) (hω : p.conditionOn C a ω≠0) :
    p ω≠0 ∧ C ω=a := by
  have hh := p.conditionOn_weight C a ω
  have hn := mul_ne_zero ha hω
  rw [hh] at hn
  split_ifs at hn with hc
  · exact ⟨hn,hc⟩
  · exact False.elim (hn rfl)

lemma joint_conditionOn_mix (p : FinLaw Ω) (C : Ω → α) (q : Ω → FinLaw Γ) :
    (p.map C).joint (fun a => (p.conditionOn C a).mix q)=
      (p.joint q).map (fun v => (C v.1,v.2)) := by
  ext ⟨a,v⟩
  rw [joint_mass,mix_mass,Finset.mul_sum]
  conv_rhs => rw [map_mass,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← mul_assoc,conditionOn_weight]
  simp only [joint_mass,Prod.mk.injEq]
  by_cases hc : C ω=a
  · simp only [hc,true_and,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
  · simp only [hc,false_and,ite_false,zero_mul,Finset.sum_const_zero]

lemma mix_support (p : FinLaw Ω) (q : Ω → FinLaw Γ) (v : Γ)
    (hv : p.mix q v≠0) : ∃ ω, p ω≠0 ∧ q ω v≠0 := by
  rw [mix_mass] at hv
  obtain ⟨ω,_,hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨ω,(mul_ne_zero_iff.mp hω)⟩

lemma expected_log_card_passingList_le {G : Type uGroup} [Fintype G]
    (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (htrue : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤ Real.log (Fintype.card G) := by
  have hh (v : Fin n → Γ) : q.iid n v*Real.log (passingList hit n v).card ≤
      q.iid n v*Real.log (Fintype.card G) := by
    by_cases hv : q.iid n v=0
    · simp only [hv,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((q.iid n).nonneg v)
      apply Real.log_le_log
      · exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
      · exact_mod_cast Finset.card_le_univ (passingList hit n v)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hh v)
  simpa only [← Finset.sum_mul,(q.iid n).sum_one,one_mul] using hs

lemma cIf_map {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} (p : FinLaw Ω) (F : Ω → α)
    (X : α → β) (Y : α → γ) (Z : α → δ) :
    (p.map F).cIf X Y Z=p.cIf (X ∘ F) (Y ∘ F) (Z ∘ F) := by
  unfold cIf
  rw [cHf_map,cHf_map]
  rfl

theorem posterior_passing_information_lower {ι : Type uIota} {O : Type uOutput} [Fintype ι] [Fintype O]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw Ω) (old : Ω → O) (X : Ω → ∀ i, G i) (q : Ω → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (Good : ι → Ω → Prop)
    (E : (i : ι) → Ω → Finset (G i)) (e c : ι → ℝ) {A H η : ℝ} (n : ℕ)
    (hA : 0≤A) (he : ∀ i, 0≤e i) (hc : ∀ i, 0≤c i)
    (htrue : ∀ ω, p ω≠0 → ∀ v, q ω v≠0 → ∀ i, ¬hit i v (X ω i))
    (hE : ∀ i ω, Good i ω → ((E i ω).card:ℝ)≤e i)
    (hhit : ∀ i ω, Good i ω → ∀ x∉E i ω, c i≤(q ω).prob (fun v => hit i v x))
    (hH : (∑ i, Real.log (Fintype.card (G i)))-H ≤ p.cHf X old)
    (hBad : (∑ i, p.prob (fun ω => ¬Good i ω))≤η)
    (hnum : ∀ i, Real.log (4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4))) ≤
      Real.log (Fintype.card (G i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤
      (n:ℝ)*(p.joint q).cIf (fun v => X v.1) Prod.snd (fun v => old v.1) := by
  let C := fun ω => (old ω,X ω)
  let μ := p.map C
  let Q := fun a => (p.conditionOn C a).mix q
  let Bad := fun i a => (1/2:ℝ)<(p.conditionOn C a).prob (fun ω => ¬Good i ω)
  have hsurv (a : O × (∀ i, G i)) (ha : μ a≠0) (v : Γ) (hv : Q a v≠0) (i : ι) :
      ¬hit i v (a.2 i) := by
    obtain ⟨ω,hω,hv⟩ := (p.conditionOn C a).mix_support q v hv
    have hw := p.conditionOn_support C a ha ω hω
    have hx : X ω=a.2 := congrArg Prod.snd hw.2
    rw [← hx]
    exact htrue ω hw.1 v hv i
  have hH' : (∑ i, Real.log (Fintype.card (G i)))-H ≤ μ.cHf Prod.snd Prod.fst := by
    rw [cHf_map]
    exact hH
  have hBad' : (∑ i, μ.prob (Bad i))≤2*η := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      p.posterior_unfavorable C (fun ω => ¬Good i ω))
    simp only [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hBad (by norm_num))
  have hlist (a : O × (∀ i, G i)) (ha : μ a≠0) (i : ι) :
      (∑ v, (Q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1) := by
    by_cases hb : Bad i a
    · rw [ite_eq_left hb,mul_zero,sub_zero]
      exact (Q a).expected_log_card_passingList_le (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) n
    · rw [ite_eq_right hb,mul_one]
      have hg : (1/2:ℝ)≤(p.conditionOn C a).prob (Good i) := by
        have hh := (p.conditionOn C a).prob_compl (Good i)
        dsimp only [Bad] at hb
        push Not at hb
        linarith only [hh,hb]
      let F := Finset.univ.filter (fun x : G i =>
        (p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4)
      have hf : (F.card:ℝ)≤4*e i :=
        (p.conditionOn C a).mixed_exception_card (Good i) (E i) (he i) (hE i) hg
      have hm (x : G i) (hx : x∉F) : c i/4≤(Q a).prob (fun v => hit i v x) := by
        apply (p.conditionOn C a).mixed_floor q (Good i) (E i) (hit i) (hc i) (hhit i) x
        have hh : ¬(p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4 := by
          simpa only [F,Finset.mem_filter,Finset.mem_univ,true_and] using hx
        exact le_of_not_gt hh
      have ht := (Q a).expected_log_card_passingList (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) F hm n
      have hpos : (0:ℝ)<(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)) := by
        have hcard : 0<Fintype.card (G i) := Fintype.card_pos_iff.mpr ⟨a.2 i⟩
        exact mul_pos (by exact_mod_cast hcard) (Real.exp_pos _)
      have hl := Real.log_le_log (by positivity : (0:ℝ)<(F.card:ℝ)+
        (Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))
        (add_le_add hf (le_refl ((Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))))
      exact ht.trans (hl.trans (hnum i))
  have hh := passing_information_lower G μ Q hit n hsurv Bad hA hH' hBad' hlist
  have hdist : μ.joint Q=(p.joint q).map (fun v => (C v.1,v.2)) :=
    p.joint_conditionOn_mix C q
  rw [hdist,cIf_map] at hh
  exact hh

end FinLaw
end GaussianMoat

end OAI
