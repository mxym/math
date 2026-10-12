import Entry002.GenericCoverage
import Mathlib.Tactic

/-! Genuine generic finite probability, conditioning, Chernoff, joint-law and
smoothing infrastructure replayed from pinned OpenAI028. No Gaussian endpoint
or unproved geometric rate is imported. -/
set_option autoImplicit false
namespace OAI
universe uOmega uIota uKappa uCapitalKappa uAlpha uBeta uGamma uCapitalGamma
namespace GaussianMoat
open scoped BigOperators Classical

namespace FinLaw
open scoped BigOperators Classical
variable {ι : Type uIota} {Ω : Type uOmega} {κ : Type uKappa} {α : Type uAlpha} {β : Type uBeta} [Fintype ι] [Fintype Ω] [Fintype κ]

noncomputable def joint (p : FinLaw ι) (q : ι → FinLaw Ω) : FinLaw (ι × Ω) where
  mass := fun v => p v.1*q v.1 v.2
  nonneg := fun v => mul_nonneg (p.nonneg _) ((q _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,FinLaw.sum_one,mul_one]

@[simp] theorem joint_mass (p : FinLaw ι) (q : ι → FinLaw Ω) (i : ι) (ω : Ω) :
    p.joint q (i,ω) = p i*q i ω := rfl

@[simp] theorem joint_map_fst (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).map Prod.fst = p := by
  ext i
  simp only [map_mass,Fintype.sum_prod_type,joint_mass]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,← Finset.mul_sum,
    sum_one,mul_one]

@[simp] theorem joint_map_snd (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).map Prod.snd = p.mix q := by
  ext ω
  simp [map_mass,Fintype.sum_prod_type,joint_mass,mix_mass]

@[simp] theorem joint_map_second (p : FinLaw ι) (q : ι → FinLaw Ω) (f : Ω → κ) :
    (p.joint q).map (fun v => (v.1,f v.2)) = p.joint (fun i => (q i).map f) := by
  ext ⟨i,x⟩
  simp only [map_mass,Fintype.sum_prod_type,joint_mass,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem entropy_joint (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).entropy = p.entropy+∑ i, p i*(q i).entropy := by
  simp only [entropy,entropySum,Fintype.sum_prod_type,joint_mass,Real.negMulLog_mul,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,FinLaw.sum_one,one_mul]

theorem Hf_map (p : FinLaw Ω) (f : Ω → κ) (X : κ → α) :
    (p.map f).Hf X = p.Hf (X ∘ f) := by
  rw [Hf_code,H,map_comp]
  rw [← H,← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  intro ω ν
  exact outputCode_eq_iff X (f ω) (f ν)

theorem cHf_map (p : FinLaw Ω) (f : Ω → κ) (X : κ → α) (Y : κ → β) :
    (p.map f).cHf X Y = p.cHf (X ∘ f) (Y ∘ f) := by
  simp only [cHf,Hf_map,Function.comp_def]

theorem Hf_joint_pair (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → α) :
    (p.joint q).Hf (fun v => (v.1,X v.2)) = p.entropy+∑ i, p i*(q i).Hf X := by
  let C := outputCode X
  have he (r : FinLaw Ω) : r.Hf X = r.Hf C :=
    r.Hf_eq_of_fibers X C (fun ω ν => (outputCode_eq_iff X ω ν).symm)
  have he' : (p.joint q).Hf (fun v => (v.1,X v.2)) =
      (p.joint q).Hf (fun v => (v.1,C v.2)) := by
    apply Hf_eq_of_fibers
    intro v w
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  rw [he',Hf_eq_H,H,joint_map_second,entropy_joint]
  simp_rw [he,Hf_eq_H,H]

theorem cHf_mix_ge (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    (∑ i, p i*(q i).cHf X Y) ≤ (p.mix q).cHf X Y := by
  have hm := (p.joint q).cHf_mono (fun v => X v.2) (fun v => Y v.2) Prod.fst
  have hid : (p.joint q).cHf (fun v => X v.2) (fun v => (Y v.2,v.1)) =
      ∑ i, p i*(q i).cHf X Y := by
    unfold cHf
    have h1 : (p.joint q).Hf (fun v => (X v.2,(Y v.2,v.1))) =
        (p.joint q).Hf (fun v => (v.1,(X v.2,Y v.2))) := by
      apply Hf_eq_of_fibers
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,Hf_joint_pair p q (fun ω => (X ω,Y ω)),
      Hf_pair_comm (p.joint q) (fun v => Y v.2) Prod.fst, Hf_joint_pair]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [hid] at hm
  have he := (p.joint q).cHf_map Prod.snd X Y
  rw [joint_map_snd] at he
  exact hm.trans_eq he.symm

theorem joint_map_fiber (p : FinLaw ι) (q : ι → FinLaw Ω) (f : ι → Ω → κ) :
    (p.joint q).map (fun v => (v.1,f v.1 v.2)) = p.joint (fun i => (q i).map (f i)) := by
  ext ⟨i,x⟩
  simp only [map_mass,Fintype.sum_prod_type,joint_mass,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem Hf_joint_pair_vary (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → α) :
    (p.joint q).Hf (fun v => (v.1,X v.1 v.2)) =
      p.entropy+∑ i, p i*(q i).Hf (X i) := by
  let C := outputCode (fun v : ι × Ω => X v.1 v.2)
  have he (i : ι) : (q i).Hf (X i) = (q i).Hf (fun ω => C (i,ω)) := by
    apply Hf_eq_of_fibers
    intro ω ν
    exact (outputCode_eq_iff (fun v : ι × Ω => X v.1 v.2) (i,ω) (i,ν)).symm
  have he' : (p.joint q).Hf (fun v => (v.1,X v.1 v.2)) =
      (p.joint q).Hf (fun v => (v.1,C v)) := by
    apply Hf_eq_of_fibers
    intro v w
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  rw [he',Hf_eq_H,H,joint_map_fiber p q (fun i ω => C (i,ω)),entropy_joint]
  simp_rw [he,Hf_eq_H,H]

theorem cHf_joint_ge (p : FinLaw ι) (q : ι → FinLaw Ω)
    (X : ι → Ω → α) (Y : ι → Ω → β) :
    (∑ i, p i*(q i).cHf (X i) (Y i)) ≤
      (p.joint q).cHf (fun v => X v.1 v.2) (fun v => Y v.1 v.2) := by
  have hm := (p.joint q).cHf_mono (fun v => X v.1 v.2) (fun v => Y v.1 v.2) Prod.fst
  have hid : (p.joint q).cHf (fun v => X v.1 v.2) (fun v => (Y v.1 v.2,v.1)) =
      ∑ i, p i*(q i).cHf (X i) (Y i) := by
    unfold cHf
    have h1 : (p.joint q).Hf (fun v => (X v.1 v.2,(Y v.1 v.2,v.1))) =
        (p.joint q).Hf (fun v => (v.1,(X v.1 v.2,Y v.1 v.2))) := by
      apply Hf_eq_of_fibers
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,Hf_joint_pair_vary p q (fun i ω => (X i ω,Y i ω)),
      Hf_pair_comm (p.joint q) (fun v => Y v.1 v.2) Prod.fst,Hf_joint_pair_vary]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rwa [hid] at hm

theorem Hf_pair_const_right (p : FinLaw Ω) (X : Ω → α) (c : β) :
    p.Hf (fun ω => (X ω,c)) = p.Hf X := by
  apply Hf_eq_of_fibers
  intro ω ν
  simp

theorem Hf_joint_ge (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → α) :
    (∑ i, p i*(q i).Hf (X i)) ≤ (p.joint q).Hf (fun v => X v.1 v.2) := by
  have h := cHf_joint_ge p q X (fun _ _ => (0:ℕ))
  simpa only [cHf,Hf_const,sub_zero,Hf_pair_const_right] using h

end FinLaw

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} [Fintype Ω]

noncomputable def prob (p : FinLaw Ω) (E : Ω → Prop) : ℝ := ∑ ω, if E ω then p ω else 0

lemma prob_nonneg (p : FinLaw Ω) (E : Ω → Prop) : 0 ≤ p.prob E := by
  exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_le_one (p : FinLaw Ω) (E : Ω → Prop) : p.prob E ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_mono (p : FinLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    p.prob E ≤ p.prob F := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he,h ω he]
  · by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

noncomputable def iid (p : FinLaw Ω) (n : ℕ) : FinLaw (Fin n → Ω) where
  mass := fun x => ∏ i, p (x i)
  nonneg := fun x => Finset.prod_nonneg (fun i _ => p.nonneg _)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [p.sum_one,Finset.prod_const_one]

@[simp] lemma iid_mass (p : FinLaw Ω) (n : ℕ) (x : Fin n → Ω) :
    p.iid n x = ∏ i, p (x i) := rfl

lemma iid_product (p : FinLaw Ω) (n : ℕ) (f : Ω → ℝ) :
    (∑ x : Fin n → Ω, p.iid n x * ∏ i, f (x i)) = (∑ ω, p ω*f ω)^n := by
  simp only [iid_mass,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun ω => p ω*f ω) n).symm

lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1-t+t^2/2 := by
  have hm : Monotone (fun x : ℝ => 1-x+x^2/2-Real.exp (-x)) := by
    apply monotone_of_hasDerivAt_nonneg (f' := fun x => -1+x+Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
          (((hasDerivAt_id x).neg).exp) using 1
      simp only [Pi.neg_apply,id_eq]
      ring
    · intro x
      have h := Real.add_one_le_exp (-x)
      change 0 ≤ -1+x+Real.exp (-x)
      linarith
  have h := hm ht
  simpa using h

lemma prob_le_exp_moment (p : FinLaw Ω) (S : Ω → ℝ) {t a : ℝ} (ht : 0 ≤ t) :
    p.prob (fun ω => S ω ≤ a) ≤ Real.exp (t*a) * ∑ ω, p ω*Real.exp (-t*S ω) := by
  have h (ω : Ω) : (if S ω ≤ a then p ω else 0) ≤
      Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by
    by_cases hh : S ω ≤ a
    · rw [ite_eq_left hh]
      have he : 1 ≤ Real.exp (t*a+-t*S ω) := Real.one_le_exp_iff.mpr (by nlinarith)
      calc
        p ω = p ω*1 := by ring
        _ ≤ p ω*Real.exp (t*a+-t*S ω) := mul_le_mul_of_nonneg_left he (p.nonneg ω)
        _ = Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by rw [Real.exp_add]; ring
    · rw [ite_eq_right hh]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  simpa only [prob,Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun ω _ => h ω)

lemma bernoulli_moment (p : FinLaw Ω) (E : Ω → Prop) (t : ℝ) :
    (∑ ω, p ω*Real.exp (-t*(if E ω then 1 else 0))) =
      1+p.prob E*(Real.exp (-t)-1) := by
  have he (ω : Ω) : p ω*Real.exp (-t*(if E ω then 1 else 0)) =
      p ω+(if E ω then p ω else 0)*(Real.exp (-t)-1) := by
    split_ifs <;> simp only [mul_one,mul_zero,Real.exp_zero,zero_mul,add_zero]
    ring
  simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,prob]

theorem iid_lower_tail (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 ≤ δ) (hp : μ ≤ p.prob E) :
    (p.iid n).prob (fun x => (∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ≤ n*(μ-δ)) ≤
      Real.exp (- (n:ℝ)*δ^2/(2*μ)) := by
  let t := δ/μ
  have ht : 0 ≤ t := div_nonneg hδ hμ.le
  have hm := prob_le_exp_moment (p.iid n)
    (fun x => ∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ht (a := n*(μ-δ))
  have hfactor : (∑ x : Fin n → Ω, p.iid n x *
      Real.exp (-t*∑ i : Fin n, if E (x i) then 1 else 0)) =
      (1+p.prob E*(Real.exp (-t)-1))^n := by
    simp_rw [Finset.mul_sum,Real.exp_sum]
    rw [iid_product p n (fun ω => Real.exp (-t*(if E ω then 1 else 0))),bernoulli_moment]
  rw [hfactor] at hm
  have hbase0 : 0 ≤ 1+p.prob E*(Real.exp (-t)-1) := by
    rw [← bernoulli_moment]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  have hbase : 1+p.prob E*(Real.exp (-t)-1) ≤ Real.exp (μ*(Real.exp (-t)-1)) := by
    have hn : Real.exp (-t)-1 ≤ 0 := by
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith
    have h1 := mul_le_mul_of_nonpos_right hp hn
    have h2 := Real.add_one_le_exp (μ*(Real.exp (-t)-1))
    linarith
  have hpw := pow_le_pow_left₀ hbase0 hbase n
  have hmul := mul_le_mul_of_nonneg_left hpw (Real.exp_pos (t*(n*(μ-δ)))).le
  apply hm.trans (hmul.trans ?_)
  rw [← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := exp_neg_le_quadratic ht
  have h := mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg n) hμ.le)
  have hid : t*((n:ℝ)*(μ-δ))+(n:ℝ)*μ*(-t+t^2/2) = -(n:ℝ)*δ^2/(2*μ) := by
    dsimp [t]
    field_simp
    ring
  rw [← hid]
  nlinarith

end

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma le_map_apply (p : FinLaw Ω) (X : Ω → α) (ω : Ω) : p ω ≤ p.map X (X ω) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun ν => if X ν=X ω then p ν else 0)
    (fun ν _ => by split_ifs <;> simp [p.nonneg ν]) (Finset.mem_univ ω)
  simpa only [ite_true,map_mass] using h

noncomputable def conditionOn (p : FinLaw Ω) (X : Ω → α) (a : α) : FinLaw Ω :=
  if h : p.map X a = 0 then p else {
    mass := fun ω => if X ω=a then p ω/(p.map X a) else 0
    nonneg := fun ω => by split_ifs; exact div_nonneg (p.nonneg ω) ((p.map X).nonneg a); rfl
    sum_one := by
      have he : (∑ ω, if X ω=a then p ω/(p.map X a) else 0) =
          (∑ ω, if X ω=a then p ω else 0)/(p.map X a) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp
      rw [he,← map_mass,div_self h] }

lemma conditionOn_weight (p : FinLaw Ω) (X : Ω → α) (a : α) (ω : Ω) :
    p.map X a * p.conditionOn X a ω = if X ω=a then p ω else 0 := by
  by_cases hz : p.map X a=0
  · rw [hz,zero_mul]
    split_ifs with hh
    · have h := p.le_map_apply X ω
      rw [hh,hz] at h
      exact (le_antisymm h (p.nonneg ω)).symm
    · rfl
  · unfold conditionOn
    rw [dite_eq_right hz]
    change p.map X a * (if X ω=a then p ω/(p.map X a) else 0) = _
    by_cases hx : X ω=a
    · rw [ite_eq_left hx,ite_eq_left hx]
      exact mul_div_cancel₀ _ hz
    · rw [ite_eq_right hx,ite_eq_right hx,mul_zero]

lemma disintegration (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).joint (p.conditionOn X) = p.map (fun ω => (X ω,ω)) := by
  ext ⟨a,ω⟩
  rw [joint_mass,conditionOn_weight,map_mass]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single ω]
  · simp
  · intro ν _ hn
    simp [hn]
  · simp

lemma conditionOn_mixture (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).mix (p.conditionOn X) = p := by
  rw [← joint_map_snd,disintegration,map_comp]
  exact p.map_id

lemma conditionOn_observation (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) = p.H X+∑ a, p.map X a*(p.conditionOn X a).H Y := by
  have h := (p.map X).Hf_joint_pair (p.conditionOn X) Y
  rw [disintegration,Hf_map] at h
  simpa only [Hf_eq_H,H,Function.comp_def] using h

lemma condH_eq_conditionOn (p : FinLaw Ω) (Y : Ω → β) (X : Ω → α) :
    p.condH Y X = ∑ a, p.map X a*(p.conditionOn X a).H Y := by
  unfold condH
  rw [p.H_pair_comm Y X,p.conditionOn_observation X Y]
  ring

lemma prob_map (p : FinLaw Ω) (f : Ω → α) (E : α → Prop) :
    (p.map f).prob E = p.prob (fun ω => E (f ω)) := by
  simp only [prob,map_mass]
  have h (a : α) : (if E a then ∑ ω, if f ω=a then p ω else 0 else 0) =
      ∑ ω, if f ω=a then (if E a then p ω else 0) else 0 := by
    by_cases he : E a <;> simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

lemma prob_joint (p : FinLaw Ω) (q : Ω → FinLaw α) (E : Ω × α → Prop) :
    (p.joint q).prob E = ∑ ω, p ω*(q ω).prob (fun a => E (ω,a)) := by
  simp only [prob,Fintype.sum_prod_type,joint_mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma conditionOn_prob (p : FinLaw Ω) (X : Ω → α) (E : Ω → Prop) :
    (∑ a, p.map X a*(p.conditionOn X a).prob E) = p.prob E := by
  rw [← prob_joint (p.map X) (p.conditionOn X) (fun v => E v.2),disintegration,prob_map]

lemma prob_le_expect_div (p : FinLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    p.prob (fun ω => a < f ω) ≤ (∑ ω, p ω*f ω)/a := by
  apply (le_div_iff₀ ha).mpr
  rw [prob,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : a < f ω
  · simp only [ite_eq_left hh]
    exact mul_le_mul_of_nonneg_left hh.le (p.nonneg ω)
  · simp only [ite_eq_right hh,zero_mul]
    exact mul_nonneg (p.nonneg ω) (hf ω)

lemma prob_compl (p : FinLaw Ω) (E : Ω → Prop) :
    p.prob (fun ω => ¬ E ω) = 1-p.prob E := by
  have h : p.prob (fun ω => ¬ E ω)+p.prob E = 1 := by
    rw [prob,prob,← Finset.sum_add_distrib,← p.sum_one]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he : E ω <;> simp [he]
  linarith

lemma prob_inter_ge (p : FinLaw Ω) (E F : Ω → Prop) :
    p.prob E-p.prob (fun ω => ¬ F ω) ≤ p.prob (fun ω => E ω ∧ F ω) := by
  rw [prob,prob,prob,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

lemma prob_exists_le_sum {ι : Type uIota} [Fintype ι] (p : FinLaw Ω) (E : ι → Ω → Prop) :
    p.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := hh
    rw [ite_eq_left ⟨i,hi⟩]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => if E i ω then p ω else 0)
      (fun j _ => by split_ifs <;> simp [p.nonneg ω]) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hh]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [p.nonneg ω])

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {Κ : Type uCapitalKappa} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype Κ] [Fintype ι]

lemma map_equiv_mass (p : FinLaw Ω) (e : Ω ≃ Κ) (x : Κ) :
    p.map e x = p (e.symm x) := by
  rw [map_mass,Finset.sum_eq_single (e.symm x)]
  · simp
  · intro ω _ hn
    have hh : e ω ≠ x := by intro h; exact hn (e.injective (by simpa using h))
    simp [hh]
  · simp

lemma entropy_map_equiv (p : FinLaw Ω) (e : Ω ≃ Κ) :
    (p.map e).entropy = p.entropy := by
  simp only [entropy,entropySum,map_equiv_mass]
  exact e.symm.sum_comp (fun ω => Real.negMulLog (p ω))

lemma iid_succ (p : FinLaw Ω) (n : ℕ) :
    p.iid (n+1) = (p.joint (fun _ => p.iid n)).map
      (Fin.consEquiv (fun _ : Fin (n+1) => Ω)) := by
  ext x
  rw [map_equiv_mass]
  change (∏ i : Fin (n+1), p (x i)) = p (x 0)*(∏ i : Fin n, p (x i.succ))
  exact Fin.prod_univ_succ _

lemma entropy_iid (p : FinLaw Ω) (n : ℕ) :
    (p.iid n).entropy = n*p.entropy := by
  induction n with
  | zero =>
    have he : p.iid 0 = uniform (Fin 0 → Ω) := by ext x; simp [uniform_mass]
    rw [he]
    simp [entropy,entropySum,uniform_mass]
  | succ n ih =>
    rw [iid_succ,entropy_map_equiv,entropy_joint]
    simp only [ih,← Finset.sum_mul,p.sum_one,one_mul,Nat.cast_add,Nat.cast_one]
    ring

lemma iid_split (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    p.iid n = (p.joint (fun _ =>
      ({ mass := fun x : (j : {j : Fin n // j ≠ i}) → Ω => ∏ j, p (x j)
         nonneg := fun x => Finset.prod_nonneg (fun j _ => p.nonneg _)
         sum_one := by rw [← Fintype.prod_sum]; simp only [p.sum_one,Finset.prod_const_one] } :
            FinLaw ((j : {j : Fin n // j ≠ i}) → Ω)))).map
      (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm := by
  ext x
  rw [map_equiv_mass]
  change (∏ j : Fin n, p (x j)) = p (x i)*(∏ j : {j : Fin n // j ≠ i}, p (x j))
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun j : Fin n => j=i)]
  have he : (∏ j : {j : Fin n // j=i}, p (x j)) = p (x i) := by
    have hsub := Finset.prod_subtype (F := inferInstance) (p := fun j : Fin n => j=i) ({i} : Finset (Fin n)) (by simp) (fun j => p (x j))
    simpa using hsub.symm
  convert! congrArg (fun v => v*(∏ j : {j : Fin n // j ≠ i}, p (x j))) he using 1
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_univ]

lemma iid_map_eval (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.iid n).map (fun x => x i) = p := by
  rw [iid_split p n i,map_comp]
  have he : ((fun x : Fin n → Ω => x i) ∘ (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm) = Prod.fst := by
    funext x
    simp [Equiv.piSplitAt]
  rw [he,joint_map_fst]

end FinLaw

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma mix_map_left (p : FinLaw Ω) (f : Ω → α) (q : α → FinLaw β) :
    (p.map f).mix q = p.mix (fun ω => q (f ω)) := by
  ext b
  simp only [mix_mass,map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma mix_assoc (p : FinLaw Ω) (q : Ω → FinLaw α) (r : α → FinLaw β) :
    (p.mix q).mix r = p.mix (fun ω => (q ω).mix r) := by
  ext b
  simp only [mix_mass,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma joint_observation (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω → α → β) :
    (p.joint q).map (fun v => F v.1 v.2) = p.mix (fun ω => (q ω).map (F ω)) := by
  have h := congrArg (fun r : FinLaw (Ω × β) => r.map Prod.snd) (joint_map_fiber p q F)
  simpa only [map_comp,joint_map_snd,Function.comp_def] using h

lemma joint_associate (p : FinLaw Ω) (q : Ω → FinLaw α) (r : Ω → α → FinLaw β) :
    ((p.joint q).joint (fun v => r v.1 v.2)).map (fun v => (v.1.1,(v.1.2,v.2))) =
      p.joint (fun ω => (q ω).joint (r ω)) := by
  ext v
  rcases v with ⟨ω,a,b⟩
  change ((p.joint q).joint (fun v => r v.1 v.2)).map (Equiv.prodAssoc Ω α β) (ω,a,b) = _
  rw [map_equiv_mass]
  simp only [Equiv.prodAssoc_symm_apply,joint_mass,mul_assoc]

end FinLaw

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]

lemma prod_ite_forall {ι : Type uIota} [Fintype ι] (P : ι → Prop) (f : ι → ℝ) :
    (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma iid_map (p : FinLaw Ω) (f : Ω → α) (n : ℕ) :
    (p.iid n).map (fun x i => f (x i)) = (p.map f).iid n := by
  ext y
  simp only [map_mass,iid_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_ite_forall]
  congr 1
  exact propext funext_iff

lemma iid_prob_forall (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) = (p.prob E)^n := by
  simp only [prob,iid_mass]
  calc
    _ = ∑ x : Fin n → Ω, ∏ i, if E (x i) then p (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have h := prod_ite_forall (fun i => E (x i)) (fun i => p (x i))
      by_cases hh : ∀ i, E (x i) <;> simpa only [hh,ite_true,ite_false] using h.symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (_ : Fin n) (ω : Ω) => if E ω then p ω else (0:ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma iid_prob_implies (p : FinLaw Ω) (E F : Ω → Prop) (n : ℕ)
    (h : ∀ x, E x → ¬ F x) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ (1-p.prob F)^n := by
  rw [← p.prob_compl F,← p.iid_prob_forall]
  exact (p.iid n).prob_mono (fun x hx i => h _ (hx i))

lemma iid_survival_exp (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) {c : ℝ}
    (hp : c ≤ 1-p.prob E) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ Real.exp (-(n:ℝ)*c) := by
  have hbase : p.prob E ≤ Real.exp (-c) := by
    have h := Real.add_one_le_exp (-c)
    linarith only [hp,h]
  rw [iid_prob_forall]
  calc
    _ ≤ (Real.exp (-c))^n := pow_le_pow_left₀ (p.prob_nonneg E) hbase n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma expect_map (p : FinLaw Ω) (f : Ω → α) (g : α → ℝ) :
    (∑ a, p.map f a*g a) = ∑ ω, p ω*g (f ω) := by
  simp only [map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp

lemma joint_expect_snd (p : FinLaw Ω) (q : Ω → FinLaw α) (f : Ω → α → ℝ) :
    (∑ v, p.joint q v*f v.1 v.2) = ∑ ω, p ω*(∑ a, q ω a*f ω a) := by
  simp only [Fintype.sum_prod_type,joint_mass,Finset.mul_sum,mul_assoc]

lemma prob_map_true (p : FinLaw Ω) (E : Ω → Prop) :
    p.map (fun ω => decide (E ω)) true = p.prob E := by
  simp only [map_mass,decide_eq_true_eq,prob]

lemma prob_le_of_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {c t : ℝ} (ht : 0 < t)
    (hc : (∑ ω, p ω*f ω) ≤ c) :
    1-c/t ≤ p.prob (fun ω => f ω ≤ t) := by
  have h := (p.prob_le_expect_div f hf ht).trans ((div_le_div_iff_of_pos_right ht).mpr hc)
  have he := p.prob_compl (fun ω => f ω ≤ t)
  simp only [not_le] at he
  linarith only [h,he]

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma H_sub_H_of_agree (p : FinLaw Ω) (X Y : Ω → α) (E : Ω → Bool)
    (hE : ∀ ω, p ω ≠ 0 → E ω = true → X ω=Y ω) :
    p.H X-p.H Y ≤ Real.binEntropy (p.map E true)+
      (1-p.map E true)*Real.log (Fintype.card α) := by
  have h := p.short_list X Y (fun y => {y}) E (b := 1) le_rfl (by
    intro ω hp he
    simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one,le_refl,and_true]
    exact hE ω hp he)
  rw [Real.log_one,mul_zero,add_zero] at h
  have hc := p.H_le_condH_add X Y
  linarith only [h,hc]

lemma condH_sub_condH_of_agree (p : FinLaw Ω) (X X' : Ω → α) (O O' : Ω → β)
    (E : Ω → Bool) (hE : ∀ ω, p ω ≠ 0 → E ω=true → X ω=X' ω ∧ O ω=O' ω) :
    p.condH X O-p.condH X' O' ≤ 2*Real.binEntropy (p.map E true)+
      (1-p.map E true)*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  have h1 := p.H_sub_H_of_agree (fun ω => (X ω,O ω)) (fun ω => (X' ω,O' ω)) E
    (fun ω hp he => Prod.ext (hE ω hp he).1 (hE ω hp he).2)
  have h2 := p.H_sub_H_of_agree O' O E (fun ω hp he => (hE ω hp he).2.symm)
  have hn := p.nonempty
  have ha : Nonempty α := ⟨X (Classical.arbitrary Ω)⟩
  have hb : Nonempty β := ⟨O (Classical.arbitrary Ω)⟩
  have hca : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcb : (Fintype.card β:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod,Nat.cast_mul,Real.log_mul hca hcb] at h1
  unfold condH
  linarith only [h1,h2]

lemma binEntropy_le_log_inverse {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.binEntropy a ≤ a*(1-Real.log a) := by
  have h : Real.negMulLog (1-a) ≤ a := by
    by_cases hz : 1-a=0
    · simp only [hz,Real.negMulLog_zero]
      exact ha.le
    · have hp : 0 < 1-a := lt_of_le_of_ne (by linarith) (Ne.symm hz)
      have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at hh
      have hm := mul_le_mul_of_nonneg_left hh hp.le
      rw [mul_sub,mul_inv_cancel₀ hz,mul_one] at hm
      unfold Real.negMulLog
      nlinarith only [hm]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  dsimp only [Real.negMulLog] at h ⊢
  nlinarith only [h]

lemma binEntropy_sum_le {ι : Type uIota} [Fintype ι] (w : FinLaw ι) (a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy (∑ i, w i*a i) := by
  exact Real.strictConcave_binEntropy.concaveOn.le_map_sum (fun i _ => w.nonneg i) w.sum_one (fun i _ => ha i)

end FinLaw

namespace FinLaw
open scoped BigOperators Classical

variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma uniform_map_perm [Nonempty Ω] (e : Equiv.Perm Ω) : (uniform Ω).map e = uniform Ω := by
  ext x
  rw [map_equiv_mass]
  rfl

lemma prob_uniform (E : Ω → Prop) [Nonempty Ω] :
    (uniform Ω).prob E = ((Finset.univ.filter E).card:ℝ)/(Fintype.card Ω:ℝ) := by
  simp only [prob,uniform_mass,div_eq_mul_inv]
  rw [← Finset.sum_boole]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma uniform_no_wrap (n a : ℕ) (ha : a ≤ n+1) :
    (uniform (Fin (n+1))).prob (fun i => i.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
  rw [prob_uniform]
  have he : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)) =
      Finset.univ.filter (fun i : Fin (n+1) => i.val<n+1-a) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hcard : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)).card = n+1-a := by
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]
  calc
    _ = ((n+1-a:ℕ):ℝ)/(n+1) := by
      congr 1
      · convert! congrArg (fun k : ℕ => (k:ℝ)) hcard using 1
        congr 2
        ext i
        simp
      · simp
    _ = _ := by
      rw [Nat.cast_sub ha,Nat.cast_add,Nat.cast_one]
      field_simp

lemma joint_perm_second (p : FinLaw Ω) {Γ : Type uCapitalGamma} [Fintype Γ] [Nonempty Γ]
    (e : Equiv.Perm Γ) :
    (p.joint (fun _ => uniform Γ)).map (fun v => (v.1,e v.2)) = p.joint (fun _ => uniform Γ) := by
  have h := joint_map_fiber p (fun _ => uniform Γ) (fun _ v => e v)
  simpa only [uniform_map_perm] using h

lemma smoothing_prob (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (E : ℕ → Prop) :
    (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val)) ≤
      (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val+a))+
        (a:ℝ)/(n+1) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  have hprob : P.prob (fun v => E (t v.1+(e v.2).val)) =
      P.prob (fun v => E (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) => Q.prob
      (fun v => E (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [prob_map] using hh
  have hgood : P.prob (fun v => v.2.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
    rw [prob_joint]
    simp only [uniform_no_wrap n a (by omega),← Finset.sum_mul,p.sum_one,one_mul]
  have hE : P.prob (fun v => E (t v.1+(e v.2).val) ∧ v.2.val+a<n+1) ≤
      P.prob (fun v => E (t v.1+v.2.val+a)) := by
    apply P.prob_mono
    intro v hv
    have he : (e v.2).val = v.2.val+a := by
      change (v.2+(⟨a,by omega⟩ : Fin (n+1))).val = _
      exact Fin.val_add_eq_of_add_lt hv.2
    simpa only [he,Nat.add_assoc] using hv.1
  have hh := P.prob_inter_ge (fun v => E (t v.1+(e v.2).val)) (fun v => v.2.val+a<n+1)
  have hc := P.prob_compl (fun v => v.2.val+a<n+1)
  rw [hgood] at hc
  rw [hprob] at hh
  linarith only [hE,hh,hc]

lemma smoothing_condH (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (X : ℕ → α) (C : ℕ → β) :
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val+a)) (fun v => C (t v.1+v.2.val+a)) ≤
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) +
      2*Real.binEntropy ((a:ℝ)/(n+1))+
        ((a:ℝ)/(n+1))*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  let good := fun v : Ω × Fin (n+1) => decide (v.2.val+a<n+1)
  have hm : P.map good true=1-(a:ℝ)/(n+1) := by
    have hh : P.map good true=P.prob (fun v => v.2.val+a<n+1) := by
      simp only [map_mass,good,prob,decide_eq_true_eq]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    rw [hh,prob_joint]
    simp only [uniform_no_wrap n a (by omega),
      ← Finset.sum_mul,p.sum_one,one_mul]
  have he : P.condH (fun v => X (t v.1+(e v.2).val)) (fun v => C (t v.1+(e v.2).val)) =
      P.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) =>
      Q.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [condH,H_map,Function.comp_def] using hh
  have h := P.condH_sub_condH_of_agree
    (fun v => X (t v.1+v.2.val+a)) (fun v => X (t v.1+(e v.2).val))
    (fun v => C (t v.1+v.2.val+a)) (fun v => C (t v.1+(e v.2).val)) good (by
      intro v _ hv
      have hlt : v.2.val+a<n+1 := of_decide_eq_true hv
      have hev : (e v.2).val=v.2.val+a := Fin.val_add_eq_of_add_lt hlt
      simp only [hev,Nat.add_assoc,and_self])
  rw [hm,he,Real.binEntropy_one_sub] at h
  linarith only [h]

end FinLaw

end GaussianMoat
end OAI
