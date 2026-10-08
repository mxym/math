import Entry002.GenericSignedArithmetic
import Entry002.SignConcentration
import Entry002.BooleanCube
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Fair-sign concentration for actual A2/A4 lattice residue maps.
Adapted from OpenAI family 028, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, SignConcentration.lean and
SignedGeometry.lean; the Gaussian factor/norm inputs are replaced by the proved
generic signed-kernel arithmetic and the genuine planar norm. -/

namespace Entry002.SignSeparation

open Module MeasureTheory ProbabilityTheory
open OAI.GaussianMoat
open scoped BigOperators NNReal

variable {L : Type*} [AddCommGroup L]

noncomputable def lineLog (data : SignedResidueData L) (v : L) (p : ℕ) (s : Bool) : ℝ := by
  classical
  exact if data.phi p s v = 0 then Real.log (p : ℝ) else 0

noncomputable def eligibleLogMass (data : SignedResidueData L) (S : Finset ℕ) (v : L) : ℝ := by
  classical
  exact ∑ p ∈ S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0),
    Real.log (p : ℝ)

/-- A4 bounds the actual logarithmic mass of all eligible primes. -/
theorem eligible_log_bound (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticInterface data b e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ v : L, IsPrimitive v → ∀ S : Finset ℕ,
      (∀ p ∈ S, p ∈ data.primes) →
      eligibleLogMass data S v ≤ Real.log (C * ‖planarEmbedding b e v‖ ^ 2) := by
  classical
  obtain ⟨C, hC, hbound⟩ := hA.eligible_product
  refine ⟨C, hC, ?_⟩
  intro v hv S hS
  have hp (p : ℕ) (hp : p ∈ S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)) :
      0 < (p : ℝ) := by
    exact_mod_cast (data.prime_mem p (hS p (Finset.mem_filter.mp hp).1)).pos
  have hlog := Real.log_le_log (Finset.prod_pos hp) (hbound v hv S hS)
  rw [Real.log_prod (fun p hp' => (hp p hp').ne')] at hlog
  exact hlog

/-- A2 gives precisely one fair-sign contribution at each eligible prime. -/
theorem lineLog_mean_eq (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticInterface data b e) {v : L} (hv : IsPrimitive v)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) :
    ∑ p : S, (lineLog data v p.val false + lineLog data v p.val true) / 2 =
      eligibleLogMass data S v / 2 := by
  classical
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_coe_sort S (fun p => lineLog data v p false + lineLog data v p true),
    eligibleLogMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hnot := primitive_not_both_signed_kernels data hA (hS p hp) hv
  by_cases ht : data.phi p true v = 0 <;> by_cases hf : data.phi p false v = 0
  · exact False.elim (hnot ⟨ht, hf⟩)
  all_goals simp [lineLog, ht, hf]

theorem lineLog_mem_Icc (data : SignedResidueData L) (v : L) {p : ℕ}
    (hp : p ∈ data.primes) (s : Bool) : lineLog data v p s ∈ Set.Icc 0 (Real.log (p : ℝ)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
    exact_mod_cast (data.prime_mem p hp).one_le)
  unfold lineLog
  split_ifs
  · exact ⟨hlog, le_rfl⟩
  · exact ⟨le_rfl, hlog⟩

/-- Genuine fair-sign Hoeffding with the A2/A4 upper bound on its mean. -/
theorem lineLog_tail (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticInterface data b e) {v : L} (hv : IsPrimitive v)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) {C ε : ℝ}
    (hlog : eligibleLogMass data S v ≤ Real.log (C * ‖planarEmbedding b e v‖ ^ 2))
    (hε : 0 ≤ ε) :
    (signMeasure S).real {σ |
      Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 + ε ≤
        ∑ p : S, lineLog data v p.val (σ p)} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ p : S,
        (((‖Real.log (p.val : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  have hmean : ∑ p : S, (lineLog data v p.val false + lineLog data v p.val true) / 2 ≤
      Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 := by
    rw [lineLog_mean_eq data hA hv S hS]
    exact div_le_div_of_nonneg_right hlog (by norm_num)
  apply le_trans (measureReal_mono (s₂ := {σ |
    ε + ∑ p : S, (lineLog data v p.val false + lineLog data v p.val true) / 2 ≤
      ∑ p : S, lineLog data v p.val (σ p)}) ?_)
  · exact sign_hoeffding (fun p : S => lineLog data v p.val) (fun p => Real.log (p.val : ℝ))
      (fun p s => lineLog_mem_Icc data v (hS p.val p.property) s) hε
  · intro σ hσ
    change Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 + ε ≤
      ∑ p : S, lineLog data v p.val (σ p) at hσ
    change ε + ∑ p : S, (lineLog data v p.val false + lineLog data v p.val true) / 2 ≤
      ∑ p : S, lineLog data v p.val (σ p)
    linarith

noncomputable def extendSigns (S : Finset ℕ) (σ : S → Bool) (p : ℕ) : Bool := by
  classical
  exact if hp : p ∈ S then σ ⟨p, hp⟩ else false

@[simp] theorem extendSigns_mem (S : Finset ℕ) (σ : S → Bool) (p : ℕ) (hp : p ∈ S) :
    extendSigns S σ p = σ ⟨p, hp⟩ := by simp [extendSigns, hp]

/-- Logarithmic lower bound forced by an actual nonzero common-kernel witness
on a primitive lattice line. -/
theorem line_witness_log_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (σ : S → Bool)
    {v w : L} (hv : IsPrimitive v) (hw : w ≠ 0) (hline : latticeDet b v w = 0)
    (hker : ∀ p : S, data.phi p.val (σ p) w = 0)
    {B : ℝ} (hbound : ‖planarEmbedding b e w‖ ≤ B) :
    Real.log ‖planarEmbedding b e v‖ + (∑ p : S, Real.log (p.val : ℝ)) - Real.log B ≤
      ∑ p : S, lineLog data v p.val (σ p) := by
  classical
  let t := S.filter (fun p => data.phi p (extendSigns S σ p) v ≠ 0)
  have hp (p : ℕ) (hp : p ∈ t) : 0 < (p : ℝ) := by
    exact_mod_cast (data.prime_mem p (hS p (Finset.mem_filter.mp hp).1)).pos
  have hprod : 0 < ∏ p ∈ t, (p : ℝ) := Finset.prod_pos hp
  have hvpos : 0 < ‖planarEmbedding b e v‖ := norm_pos_iff.mpr (by
    intro hz
    exact hv.1 (planarEmbedding_injective b e (hz.trans (planarEmbedding_zero b e).symm)))
  have hlo := line_witness_length_lower data b e S hS (extendSigns S σ) hv hw hline
    (fun p hp => by simpa only [extendSigns_mem S σ p hp] using hker ⟨p, hp⟩)
  have hlow : ‖planarEmbedding b e v‖ * (∏ p ∈ t, (p : ℝ)) ≤ B := hlo.trans hbound
  have hlog := Real.log_le_log (mul_pos hvpos hprod) hlow
  rw [Real.log_mul hvpos.ne' hprod.ne', Real.log_prod (fun p hp' => (hp p hp').ne')] at hlog
  have hsum : (∑ p ∈ t, Real.log (p : ℝ)) =
      (∑ p : S, Real.log (p.val : ℝ)) - ∑ p : S, lineLog data v p.val (σ p) := by
    calc
      _ = ∑ p ∈ S, (Real.log (p : ℝ) - lineLog data v p (extendSigns S σ p)) := by
        unfold t
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        unfold lineLog
        split_ifs <;> simp_all
      _ = _ := by
        rw [← Finset.sum_coe_sort S
          (fun p => Real.log (p : ℝ) - lineLog data v p (extendSigns S σ p))]
        simp [extendSigns, Finset.sum_sub_distrib]
  rw [hsum] at hlog
  linarith

def lineEvent (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) (v : L)
    (σ : S → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ latticeDet b v w = 0 ∧ ∀ p : S, data.phi p.val (σ p) w = 0

theorem line_event_tail (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hA : ArithmeticInterface data b e) {v : L} (hv : IsPrimitive v)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (Q : Set L) {C B ε : ℝ}
    (hC : 0 < C)
    (hlog : eligibleLogMass data S v ≤ Real.log (C * ‖planarEmbedding b e v‖ ^ 2))
    (hQ : ∀ w ∈ Q, ‖planarEmbedding b e w‖ ≤ B) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : S, Real.log (p.val : ℝ)) - Real.log B - Real.log C / 2) :
    (signMeasure S).real {σ | lineEvent data b S Q v σ} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ p : S,
        (((‖Real.log (p.val : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  have hvpos : 0 < ‖planarEmbedding b e v‖ := norm_pos_iff.mpr (by
    intro hz
    exact hv.1 (planarEmbedding_injective b e (hz.trans (planarEmbedding_zero b e).symm)))
  have hmid : Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 =
      Real.log ‖planarEmbedding b e v‖ + Real.log C / 2 := by
    rw [Real.log_mul hC.ne' (pow_ne_zero 2 hvpos.ne'), Real.log_pow]
    norm_num
    ring
  apply le_trans (measureReal_mono (s₂ := {σ |
    Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 + ε ≤
      ∑ p : S, lineLog data v p.val (σ p)}) ?_)
  · exact lineLog_tail data hA hv S hS hlog hε
  · rintro σ ⟨w, hwQ, hw, hline, hker⟩
    have hlo := line_witness_log_lower data b e S hS σ hv hw hline hker (hQ w hwQ)
    change Real.log (C * ‖planarEmbedding b e v‖ ^ 2) / 2 + ε ≤
      ∑ p : S, lineLog data v p.val (σ p)
    rw [hmid]
    linarith

/-- A single constant from genuine A4 gives a uniform primitive-line witness
tail, for every finite prime selection and every norm-bounded region. -/
theorem exists_uniform_line_event_tail (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hA : ArithmeticInterface data b e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ v : L, IsPrimitive v → ∀ S : Finset ℕ,
      (∀ p ∈ S, p ∈ data.primes) → ∀ Q : Set L, ∀ B ε : ℝ,
      (∀ w ∈ Q, ‖planarEmbedding b e w‖ ≤ B) → 0 ≤ ε →
      ε ≤ (∑ p : S, Real.log (p.val : ℝ)) - Real.log B - Real.log C / 2 →
      (signMeasure S).real {σ | lineEvent data b S Q v σ} ≤
        Real.exp (-ε ^ 2 / (2 * ∑ p : S,
          (((‖Real.log (p.val : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  obtain ⟨C, hC, hlog⟩ := eligible_log_bound data hA
  refine ⟨C, hC, ?_⟩
  intro v hv S hS Q B ε hQ hε hexcess
  exact line_event_tail data b e hA hv S hS Q (by linarith) (hlog v hv S hS) hQ hε hexcess


universe uIota

def cubeEquiv : (n : ℕ) → Cube n ≃ (Fin n → Bool)
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (Equiv.refl Bool) (cubeEquiv n)).trans (Fin.consEquiv (fun _ => Bool))

noncomputable def cubeSignEquiv (ι : Type uIota) [Fintype ι] : Cube (Fintype.card ι) ≃ (ι → Bool) :=
  (cubeEquiv (Fintype.card ι)).trans
    (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl Bool))

noncomputable def signDist {ι : Type uIota} [Fintype ι] (σ τ : ι → Bool) : ℕ := by
  classical
  exact ∑ i, if σ i = τ i then 0 else 1

theorem cubeEquiv_dist (n : ℕ) (x y : Cube n) :
    signDist (cubeEquiv n x) (cubeEquiv n y) = cubeDist n x y := by
  classical
  induction n with
  | zero => simp [signDist, cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    simp only [signDist, Fin.sum_univ_succ, cubeEquiv, Equiv.trans_apply,
      Equiv.prodCongr_apply, Fin.consEquiv_apply, Fin.cons_zero,
      Fin.cons_succ, cubeDist]
    congr 1
    exact ih x y

theorem cubeSignEquiv_dist (ι : Type uIota) [Fintype ι] (x y : Cube (Fintype.card ι)) :
    signDist (cubeSignEquiv ι x) (cubeSignEquiv ι y) = cubeDist (Fintype.card ι) x y := by
  classical
  rw [← cubeEquiv_dist]
  unfold signDist cubeSignEquiv
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.symm_symm]
  exact (Fintype.equivFin ι).sum_comp (fun i => if cubeEquiv (Fintype.card ι) x i =
    cubeEquiv (Fintype.card ι) y i then (0 : ℕ) else 1)

theorem signMeasure_real_singleton {ι : Type uIota} [Fintype ι] (σ : ι → Bool) :
    (signMeasure ι).real {σ} = ((2 : ℝ)^Fintype.card ι)⁻¹ := by
  simp [measureReal_def, signMeasure, Measure.pi_singleton, fairCoin,
    PMF.uniformOfFintype_apply]

open scoped Classical in

theorem signMeasure_real_set {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = (∑ σ, if σ ∈ S then (1 : ℝ) else 0) /
      (2 : ℝ)^Fintype.card ι := by
  classical
  have he : S = (↑(Finset.univ.filter (· ∈ S)) : Set (ι → Bool)) := by ext; simp
  conv_lhs => rw [he, ← sum_measureReal_singleton]
  rw [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ ∈ S <;> simp [hσ, signMeasure_real_singleton]

theorem cubeSignEquiv_measure {ι : Type uIota} [Fintype ι] (S : (ι → Bool) → Prop) :
    (signMeasure ι).real {σ | S σ} =
      (cubeSize (fun x => S (cubeSignEquiv ι x)) : ℝ) / (2 : ℝ)^Fintype.card ι := by
  classical
  rw [signMeasure_real_set]
  congr 1
  simp only [Set.mem_ofPred_eq]
  rw [← (cubeSignEquiv ι).sum_comp (fun σ => if S σ then (1 : ℝ) else 0)]
  simp only [cubeSize, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]


theorem selectedSignDistance_extend (S : Finset ℕ) (σ τ : S → Bool) :
    selectedSignDistance S (extendSigns S σ) (extendSigns S τ) = signDist σ τ := by
  classical
  rw [selectedSignDistance, Finset.card_filter]
  unfold signDist
  rw [← Finset.sum_coe_sort S
    (fun p => if extendSigns S σ p ≠ extendSigns S τ p then 1 else 0)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [extendSigns_mem S σ p.val p.property, extendSigns_mem S τ p.val p.property]
  split_ifs <;> simp_all

theorem latticeDet_zero_trans (b : Basis (Fin 2) ℤ L) {u v w : L} (hv : v ≠ 0)
    (huv : latticeDet b u v = 0) (hvw : latticeDet b v w = 0) :
    latticeDet b u w = 0 := by
  have hcoord : b.repr v 0 ≠ 0 ∨ b.repr v 1 ≠ 0 := by
    contrapose! hv
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [hv]
  unfold latticeDet at *
  rcases hcoord with hr | hi
  · apply (mul_eq_zero.mp (show b.repr v 0 *
        (b.repr u 0 * b.repr w 1 - b.repr u 1 * b.repr w 0) = 0 by
      nlinarith [congrArg (fun x : ℤ => x * b.repr w 0) huv,
        congrArg (fun x : ℤ => b.repr u 0 * x) hvw])).resolve_left hr
  · apply (mul_eq_zero.mp (show b.repr v 1 *
        (b.repr u 0 * b.repr w 1 - b.repr u 1 * b.repr w 0) = 0 by
      nlinarith [congrArg (fun x : ℤ => x * b.repr w 1) huv,
        congrArg (fun x : ℤ => b.repr u 1 * x) hvw])).resolve_left hi

@[simp] theorem latticeDet_self (b : Basis (Fin 2) ℤ L) (v : L) :
    latticeDet b v v = 0 := by unfold latticeDet; ring

theorem latticeDet_swap (b : Basis (Fin 2) ℤ L) (u v : L) :
    latticeDet b u v = -latticeDet b v u := by unfold latticeDet; ring

def witnessLine (b : Basis (Fin 2) ℤ L) (v : L) : Set L := {w | latticeDet b v w = 0}

theorem witnessLine_eq (b : Basis (Fin 2) ℤ L) {v w : L} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : latticeDet b v w = 0) : witnessLine b v = witnessLine b w := by
  ext u
  constructor
  · intro hu
    exact latticeDet_zero_trans b hv (by rw [latticeDet_swap, hvw, neg_zero]) hu
  · exact latticeDet_zero_trans b hw hvw

def badSign (data : SignedResidueData L) (S : Finset ℕ) (Q : Set L)
    (σ : S → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ ∀ p : S, data.phi p.val (σ p) w = 0

noncomputable def badWitness (data : SignedResidueData L) (S : Finset ℕ) (Q : Set L)
    (σ : {σ : S → Bool // badSign data S Q σ}) : L := σ.property.choose

theorem badWitness_spec (data : SignedResidueData L) (S : Finset ℕ) (Q : Set L)
    (σ : {σ : S → Bool // badSign data S Q σ}) :
    badWitness data S Q σ ∈ Q ∧ badWitness data S Q σ ≠ 0 ∧
      ∀ p : S, data.phi p.val (σ.val p) (badWitness data S Q σ) = 0 :=
  σ.property.choose_spec

def badLines (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) : Set (Set L) :=
  Set.range (fun σ : {σ : S → Bool // badSign data S Q σ} =>
    witnessLine b (badWitness data S Q σ))

instance badLines_finite (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) : Finite (badLines data b S Q) := by
  unfold badLines
  infer_instance

theorem badLine_primitive (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) (ℓ : badLines data b S Q) :
    ∃ v : L, IsPrimitive v ∧ witnessLine b v = ℓ.val := by
  obtain ⟨σ, hσ⟩ := ℓ.property
  have hw := badWitness_spec data S Q σ
  obtain ⟨v, hv, a, _ha, ha⟩ := exists_primitive_lattice_direction b hw.2.1
  refine ⟨v, hv, ?_⟩
  rw [← hσ]
  apply witnessLine_eq b hv.1 hw.2.1
  rw [ha]
  simp only [latticeDet, map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

def lineClass (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) (ℓ : badLines data b S Q) (σ : S → Bool) : Prop :=
  ∃ hσ : badSign data S Q σ, witnessLine b (badWitness data S Q ⟨σ, hσ⟩) = ℓ.val

theorem badSign_iff_class (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) (σ : S → Bool) :
    badSign data S Q σ ↔ ∃ ℓ : badLines data b S Q, lineClass data b S Q ℓ σ := by
  constructor
  · intro hσ
    exact ⟨⟨witnessLine b (badWitness data S Q ⟨σ,hσ⟩), ⟨⟨σ,hσ⟩,rfl⟩⟩, hσ, rfl⟩
  · rintro ⟨ℓ,hσ,_⟩
    exact hσ

theorem lineClass_subset_event (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (Q : Set L) (ℓ : badLines data b S Q) {v : L}
    (hvℓ : witnessLine b v = ℓ.val) :
    {σ | lineClass data b S Q ℓ σ} ⊆ {σ | lineEvent data b S Q v σ} := by
  rintro σ ⟨hσ,hℓ⟩
  have hw := badWitness_spec data S Q ⟨σ,hσ⟩
  refine ⟨_,hw.1,hw.2.1,?_,hw.2.2⟩
  change badWitness data S Q ⟨σ,hσ⟩ ∈ witnessLine b v
  rw [hvℓ, ← hℓ]
  exact latticeDet_self _ _

theorem lineClasses_separated (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (Q : Set L)
    {U B : ℝ} (hU : 1 ≤ U) (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, |(latticeDet b w w' : ℝ)| ≤ B)
    {h : ℕ} (hsmall : B * U^(2*h) < ∏ p ∈ S, (p : ℝ)) (hB : 0 ≤ B) :
    ∀ ℓ ℓ' : badLines data b S Q, ℓ ≠ ℓ' → ∀ σ, lineClass data b S Q ℓ σ →
      ∀ τ, lineClass data b S Q ℓ' τ → 2*h < signDist σ τ := by
  intro ℓ ℓ' hℓℓ σ ⟨hσ,hσℓ⟩ τ ⟨hτ,hτℓ⟩
  by_contra hn
  have hd : signDist σ τ ≤ 2*h := le_of_not_gt hn
  have hw := badWitness_spec data S Q ⟨σ,hσ⟩
  have hw' := badWitness_spec data S Q ⟨τ,hτ⟩
  have hsm : B * U^(signDist σ τ) < ∏ p ∈ S, (p : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU hd) hB).trans_lt hsmall
  have hcol := near_kernel_witnesses_collinear data b S hS (extendSigns S σ)
    (extendSigns S τ)
    (fun p hp => by simpa only [extendSigns_mem S σ p hp] using hw.2.2 ⟨p,hp⟩)
    (fun p hp => by simpa only [extendSigns_mem S τ p hp] using hw'.2.2 ⟨p,hp⟩)
    (by linarith) hpU (hdet _ hw.1 _ hw'.1)
    (by simpa only [selectedSignDistance_extend] using hsm)
  apply hℓℓ
  apply Subtype.ext
  rw [← hσℓ, ← hτℓ]
  exact witnessLine_eq b hw.2.1 hw'.2.1 hcol

theorem cubeSize_exists_le_sum {n : ℕ} {ι : Type uIota} [Fintype ι]
    (S : ι → Cube n → Prop) : cubeSize (fun x => ∃ i, S i x) ≤ ∑ i, cubeSize (S i) := by
  classical
  unfold cubeSize
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, S i x
  · obtain ⟨i, hi⟩ := hx
    rw [ite_eq_left ⟨i,hi⟩]
    have h : (if S i x then 1 else 0) ≤ ∑ j : ι, if S j x then 1 else 0 :=
      Finset.single_le_sum (f := fun j => if S j x then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hx]
    exact Nat.zero_le _


/-- The fixed A4 constant used throughout the signed separation engine. -/
noncomputable def separationConstant (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticInterface data b e) : ℝ := (eligible_log_bound data hA).choose

theorem separationConstant_spec (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticInterface data b e) :
    1 ≤ separationConstant data hA ∧ ∀ v : L, IsPrimitive v → ∀ S : Finset ℕ,
      (∀ p ∈ S, p ∈ data.primes) →
      eligibleLogMass data S v ≤
        Real.log (separationConstant data hA * ‖planarEmbedding b e v‖ ^ 2) :=
  (eligible_log_bound data hA).choose_spec

/-- Actual signed-kernel witnesses in any bounded determinant window have
small probability. The seed probabilities are proved from A2/A4 and Hoeffding;
the packing step is the genuine Boolean-cube separation theorem. -/
theorem signed_region_bound (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (Q : Set L)
    (hr : 0 < S.card) {U B N ε a E A : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, |(latticeDet b w w' : ℝ)| ≤ B)
    (hsmall : B * U^(2*h) < ∏ p ∈ S, (p : ℝ))
    (hQ : ∀ w ∈ Q, ‖planarEmbedding b e w‖ ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : S, Real.log (p.val : ℝ)) - Real.log N -
      Real.log (separationConstant data hArith) / 2)
    (ha : 0 ≤ a) (hE : 0 < E) (hA : 0 < A)
    (hlogE : Real.log E ≤ (S.card : ℝ) * Real.log 2 - a)
    (hseed : A * Real.exp (-ε^2 / (2 * ∑ p : S,
      (((‖Real.log (p.val : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^S.card ≤ E)
    (hfactor : A ≤ (1 + a / ((S.card : ℝ)*Real.log 2))^h) :
    (signMeasure S).real {σ | badSign data S Q σ} ≤ A⁻¹ := by
  classical
  let : Fintype (badLines data b S Q) := Fintype.ofFinite _
  let F : badLines data b S Q → Cube (Fintype.card S) → Prop :=
    fun ℓ x => lineClass data b S Q ℓ (cubeSignEquiv S x)
  have hcard : Fintype.card S = S.card := Fintype.card_coe _
  have hpow : 0 < (2 : ℝ)^Fintype.card S := pow_pos (by norm_num) _
  have hseed' (ℓ : badLines data b S Q) : A * cubeSize (F ℓ) ≤ E := by
    obtain ⟨v,hv,hvℓ⟩ := badLine_primitive data b S Q ℓ
    have hC := separationConstant_spec data hArith
    have hm := (measureReal_mono (lineClass_subset_event data b S Q ℓ hvℓ)).trans
      (line_event_tail data b e hArith hv S hS Q (by linarith [hC.1])
        (hC.2 v hv S hS) hQ hε hexcess)
    rw [cubeSignEquiv_measure] at hm
    have hc : (cubeSize (F ℓ) : ℝ) ≤ Real.exp (-ε^2 / (2 * ∑ p : S,
        (((‖Real.log (p.val : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^Fintype.card S :=
      (div_le_iff₀ hpow).mp hm
    have hh := mul_le_mul_of_nonneg_left hc hA.le
    exact hh.trans (by simpa only [hcard, mul_assoc] using hseed)
  have hsep : ∀ ℓ ℓ' : badLines data b S Q, ℓ ≠ ℓ' → ∀ x, F ℓ x → ∀ y, F ℓ' y →
      2*h < cubeDist (Fintype.card S) x y := by
    intro ℓ ℓ' hℓℓ x hx y hy
    have hh := lineClasses_separated data b S hS Q hU hpU hdet hsmall hB ℓ ℓ' hℓℓ
      (cubeSignEquiv S x) hx (cubeSignEquiv S y) hy
    simpa only [cubeSignEquiv_dist] using hh
  have hpack := cube_separated_bound (n := Fintype.card S) (h := h)
    (by simpa only [hcard] using hr) F ha hE (by simpa only [hcard] using hlogE)
    hseed' (by simpa only [hcard] using hfactor) hsep
  have hunion : (cubeSize (fun x => badSign data S Q (cubeSignEquiv S x)) : ℝ) ≤
      ∑ ℓ, (cubeSize (F ℓ) : ℝ) := by
    have he : (fun x => badSign data S Q (cubeSignEquiv S x)) =
        (fun x => ∃ ℓ, F ℓ x) := by
      funext x
      exact propext (badSign_iff_class data b S Q _)
    rw [he]
    exact_mod_cast cubeSize_exists_le_sum F
  rw [cubeSignEquiv_measure, div_le_iff₀ hpow]
  have hh := (mul_le_mul_of_nonneg_left hunion hA.le).trans hpack
  calc
    _ ≤ (2 : ℝ)^Fintype.card S / A :=
      (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem signed_region_exp_bound (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (Q : Set L)
    (hr : 0 < S.card) {U B N ε a β : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, |(latticeDet b w w' : ℝ)| ≤ B)
    (hsmall : B * U^(2*h) < (∏ p ∈ S, (p : ℝ)))
    (hQ : ∀ w ∈ Q, ‖planarEmbedding b e w‖ ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : S, Real.log (p.val : ℝ)) - Real.log N - Real.log (separationConstant data hArith) / 2)
    (ha : 0 ≤ a) (hb : β ≤ a)
    (htail : 2*a ≤ ε^2 / (2 * ∑ p : S,
      (((‖Real.log (p.val : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)))
    (hgrowth : β ≤ (h : ℝ) * Real.log (1 + a / ((S.card : ℝ)*Real.log 2))) :
    (signMeasure S).real {σ | badSign data S Q σ} ≤ Real.exp (-β) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr' : 0 < (S.card : ℝ) := by exact_mod_cast hr
  have hbase : 0 < 1 + a / ((S.card : ℝ)*Real.log 2) := by
    have := div_nonneg ha (mul_pos hr' htwo).le
    linarith
  have hbexp : Real.exp β ≤ (1 + a / ((S.card : ℝ)*Real.log 2))^h := by
    rw [← Real.exp_log (pow_pos hbase h)]
    apply Real.exp_le_exp.mpr
    simpa only [Real.log_pow] using hgrowth
  have hh := signed_region_bound data b e hArith S hS Q hr hU hpU hB hdet hsmall hQ hε hexcess ha
    (E := (2 : ℝ)^S.card * Real.exp (-a))
    (A := Real.exp β) (h := h) (mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _))
    (Real.exp_pos _) (by
      rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' (Real.exp_pos _).ne',
        Real.log_pow, Real.log_exp]
      linarith) (by
      rw [← Real.exp_add]
      have he : β + -ε^2 / (2 * ∑ p : S,
          (((‖Real.log (p.val : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)) ≤ -a := by
        rw [neg_div]
        linarith
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (by norm_num) _)).trans_eq (mul_comm _ _)) hbexp
  simpa only [Real.exp_neg] using hh


/-- The actual Euclidean length bound in a thin oriented lattice rectangle. -/
theorem rectangle_length_bound (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) {R W : ℝ}
    (hW : 0 ≤ W) (hWR : W ≤ R) {w : L} (hw : w ∈ latticeRectangle b e o R W) :
    ‖planarEmbedding b e w‖ ≤ Real.sqrt 2 * R := by
  have hR : 0 ≤ R := hW.trans hWR
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hh := latticeRectangle_norm_bound b e o hW hWR hw
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt hR)).mp
  nlinarith

/-- Genuine A2/A4 signed-kernel probability for any thin rectangle in the
actual planar lattice. Cell area and the eligible-product constant are explicit;
the determinant and norm hypotheses are proved here, not assumed by the caller. -/
theorem signed_rectangle_exp_bound (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (o : Plane ≃ₗᵢ[ℝ] Plane)
    {R W U ε a β : ℝ} {h : ℕ} (hr : 0 < S.card)
    (hW : 0 ≤ W) (hWR : W ≤ R) (hU : 1 ≤ U)
    (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hsmall : (2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)|) *
      U ^ (2 * h) < ∏ p ∈ S, (p : ℝ))
    (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : S, Real.log (p.val : ℝ)) - Real.log (Real.sqrt 2 * R) -
      Real.log (separationConstant data hArith) / 2)
    (ha : 0 ≤ a) (hb : β ≤ a)
    (htail : 2 * a ≤ ε ^ 2 / (2 * ∑ p : S,
      (((‖Real.log (p.val : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))
    (hgrowth : β ≤ (h : ℝ) * Real.log (1 + a / ((S.card : ℝ) * Real.log 2))) :
    (signMeasure S).real {σ | badSign data S (latticeRectangle b e o R W) σ} ≤
      Real.exp (-β) := by
  have hR : 0 ≤ R := hW.trans hWR
  apply signed_region_exp_bound data b e hArith S hS (latticeRectangle b e o R W)
    hr hU hpU (div_nonneg (by positivity) (abs_nonneg _))
    (fun _ hw _ hw' => latticeRectangle_determinant_bound b e o (hW.trans hWR) hW hw hw')
    hsmall (fun _ hw => rectangle_length_bound b e o hW hWR hw) hε hexcess ha hb htail hgrowth

theorem rectangle_cube_growth {r : ℕ} {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (hlarge : 1000 ≤ d^3 * r) :
    let h := ⌊d * r / 10⌋₊
    d^3 * r / 5120 ≤ (h : ℝ) * Real.log (1 + (d^2 * r / 64) / ((r : ℝ) * Real.log 2)) := by
  dsimp only
  have hr : 0 < (r : ℝ) := by
    by_contra h
    have hr0 : (r : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hr0, mul_zero] at hlarge
    norm_num at hlarge
  have loglo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have loghi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) loglo
  have hdle : d ≤ 1 := by linarith
  have hsq : d^2 ≤ 1 := by nlinarith
  have hdr : d^3 * r ≤ d * r := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hsq)]) hr.le
  have hfloor : d * r / 20 ≤ (⌊d * r / 10⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (d * r / 10)
    have hdrl : 1000 ≤ d * r := hlarge.trans hdr
    linarith
  have heq : (d^2 * r / 64) / ((r : ℝ) * Real.log 2) = d^2 / (64 * Real.log 2) := by
    field_simp
  let δ := d^2 / (64 * Real.log 2)
  have hδ : 0 ≤ δ := div_nonneg (sq_nonneg _) (by positivity)
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith
  have hδlo : d^2 / 64 ≤ δ := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr loghi)]
  have hlogδ : δ/2 ≤ Real.log (1+δ) := by
    apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ)
    apply (le_div_iff₀ (by linarith : 0 < δ+2)).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  rw [heq]
  change _ ≤ (⌊d * r / 10⌋₊ : ℝ) * Real.log (1+δ)
  have hm := mul_le_mul hfloor hlogδ (by linarith) (Nat.cast_nonneg _)
  have hm' : d^3 * r / 2560 ≤ (d*r/20) * (δ/2) := by
    have := mul_le_mul_of_nonneg_left hδlo (by positivity : 0 ≤ d*r/40)
    nlinarith
  have hnon : 0 ≤ d^3 * r := by positivity
  nlinarith

theorem rectangle_linear_large {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hlarge : 1000 ≤ d^3 * r) : 1000 ≤ d*r := by
  have hs : d^2 ≤ 1 := by nlinarith
  have hc : d^3 ≤ d := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hs)]
  exact hlarge.trans (mul_le_mul_of_nonneg_right hc hr)

theorem rectangle_log_small {r : ℕ} {d t u l : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1/4) (ht : 1/2 ≤ t) (hu : 0 ≤ u) (hutu : u ≤ 2*t)
    (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    Real.log 2 + (1-d)*l + (2*⌊d*r/10⌋₊ : ℕ)*u < l := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have hf : (⌊d*r/10⌋₊ : ℝ) ≤ d*r/10 := Nat.floor_le (by positivity)
  have hm : (2*⌊d*r/10⌋₊ : ℕ)*u ≤ (d*r/5)*(2*t) := by
    push_cast
    apply mul_le_mul (by linarith) hutu hu
    positivity
  have hdl := mul_le_mul_of_nonneg_left hl hd.le
  have hdt : 500 ≤ d*r*t := by
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
    nlinarith
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith

theorem rectangle_log_excess {r : ℕ} {d t l : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (ht : 1/2 ≤ t) (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    d*l/2 ≤ l - ((1-d)*l + Real.log 2/2) := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have h1 := mul_le_mul_of_nonneg_left hl hd.le
  have h2 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith

theorem rectangle_hoeffding_exponent {r d t l V : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (ht : 0 < t) (hl : r*t ≤ l) (hV : 0 < V) (hVup : V ≤ r*t^2) :
    2*(d^2*r/64) ≤ (d*l/2)^2 / (2*V) := by
  have hdl : 0 ≤ d*r*t/2 := by positivity
  have hdl' : d*r*t/2 ≤ d*l/2 := by nlinarith [mul_le_mul_of_nonneg_left hl hd]
  have hs : (d*r*t/2)^2 ≤ (d*l/2)^2 := (sq_le_sq₀ hdl (hdl.trans hdl')).mpr hdl'
  have hden : 0 < 2*r*t^2 := by positivity
  calc
    2*(d^2*r/64) ≤ d^2*r/8 := by nlinarith [mul_nonneg (sq_nonneg d) hr.le]
    _ = (d*r*t/2)^2 / (2*r*t^2) := by field_simp; ring
    _ ≤ (d*l/2)^2 / (2*r*t^2) := div_le_div_of_nonneg_right hs hden.le
    _ ≤ (d*l/2)^2 / (2*V) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)


noncomputable def logVariance (S : Finset ℕ) : ℝ :=
  ∑ p : S, (((‖Real.log (p.val : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)

theorem log_period (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) :
    Real.log (∏ p ∈ S, (p : ℝ)) = ∑ p : S, Real.log (p.val : ℝ) := by
  classical
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (data.prime_mem p (hS p hp)).ne_zero)]
  exact (Finset.sum_coe_sort S (fun p => Real.log (p : ℝ))).symm

theorem logVariance_pos (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (hr : 0 < S.card) :
    0 < logVariance S := by
  classical
  unfold logVariance
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hr
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (data.prime_mem p (hS p hp)).one_lt)
  apply Finset.sum_pos' (fun _ _ => by positivity)
  refine ⟨⟨p,hp⟩, Finset.mem_univ _, ?_⟩
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos hlog]
  positivity

theorem logVariance_le (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) {U : ℝ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ S, (p : ℝ) ≤ U) :
    logVariance S ≤ (S.card : ℝ) * (Real.log U / 2)^2 := by
  classical
  unfold logVariance
  calc
    _ ≤ ∑ _p : S, (Real.log U / 2)^2 := by
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 < (p : ℝ) := by exact_mod_cast (data.prime_mem p (hS p p.property)).pos
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (data.prime_mem p (hS p p.property)).one_le)
      have hle := Real.log_le_log hp (hpU p p.property)
      simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg hlog]
      exact (sq_le_sq₀ (by positivity) (div_nonneg (Real.log_nonneg hU) (by norm_num))).mpr (by linarith)
    _ = _ := by simp [nsmul_eq_mul]



/-- The quantitative thin-rectangle bound for arbitrary actual lattices.
Its geometric scales expose the cell area and the fixed A4 constant. -/
theorem signed_rectangle_scaled (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (o : Plane ≃ₗᵢ[ℝ] Plane)
    {T R W d : ℝ} (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 0 < W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : 2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)| ≤
      (∏ p ∈ S, (p : ℝ)) ^ (1-d))
    (hlength : (Real.sqrt 2 * R) * Real.sqrt (separationConstant data hArith) ≤
      (∏ p ∈ S, (p : ℝ)) ^ (1-d))
    (hlarge : 1000 ≤ d^3*S.card) :
    (signMeasure S).real {σ | badSign data S (latticeRectangle b e o R W) σ} ≤
      Real.exp (-(d^3*S.card/5120)) := by
  have hr : 0 < S.card := by
    by_contra h
    have hz : S.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hr' : 0 < (S.card : ℝ) := by exact_mod_cast hr
  have hP : 0 < ∏ p ∈ S, (p : ℝ) := Finset.prod_pos (fun p hp => by
    exact_mod_cast (data.prime_mem p (hS p hp)).pos)
  have hTpos : 0 < T := by linarith
  have hU : 1 ≤ 2*T := by linarith
  have hUpos : 0 < 2*T := by linarith
  have hRpos : 0 < R := hW.trans_le hWR
  have hcov : 0 < |planarCellDet (e.trans o.toLinearEquiv)| :=
    abs_pos.mpr (planarCellDet_ne_zero _)
  have hBpos : 0 < 2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)| := by positivity
  have hCpos : 0 < separationConstant data hArith := by
    linarith [(separationConstant_spec data hArith).1]
  have hNpos : 0 < Real.sqrt 2 * R := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hRpos
  have hlogT : 1/2 ≤ Real.log T := by
    have hlog2T := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith [Real.log_two_gt_d9]
  have hlogU : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith
  have hlogP : (S.card : ℝ)*Real.log T ≤ Real.log (∏ p ∈ S, (p : ℝ)) := by
    rw [log_period data S hS]
    calc
      _ = ∑ _p : S, Real.log T := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun p _ => Real.log_le_log hTpos (hpT p p.property).1)
  have hlogPpos : 0 < Real.log (∏ p ∈ S, (p : ℝ)) :=
    (mul_pos hr' (by linarith : 0 < Real.log T)).trans_le hlogP
  have hlogB : Real.log (2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)|) ≤
      Real.log 2 + (1-d)*Real.log (∏ p ∈ S, (p : ℝ)) := by
    have hh := Real.log_le_log hBpos harea
    rw [Real.log_rpow hP] at hh
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlogN : Real.log (Real.sqrt 2 * R) +
      Real.log (separationConstant data hArith) / 2 ≤
      (1-d)*Real.log (∏ p ∈ S, (p : ℝ)) := by
    have hh := Real.log_le_log (mul_pos hNpos (Real.sqrt_pos.mpr hCpos)) hlength
    rw [Real.log_rpow hP, Real.log_mul hNpos.ne' (Real.sqrt_pos.mpr hCpos).ne',
      Real.log_sqrt hCpos.le] at hh
    exact hh
  let h : ℕ := ⌊d*S.card/10⌋₊
  have hsmall : (2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)|) *
      (2*T)^(2*h) < ∏ p ∈ S, (p : ℝ) := by
    apply (Real.log_lt_log_iff (mul_pos hBpos (pow_pos hUpos _)) hP).mp
    rw [Real.log_mul hBpos.ne' (pow_pos hUpos _).ne', Real.log_pow]
    have hh := rectangle_log_small hd hd1.le hlogT (Real.log_nonneg hU) hlogU hlogP hlarge
    exact (add_le_add_left hlogB _).trans_lt hh
  have hV := logVariance_pos data S hS hr
  have hVup : logVariance S ≤ (S.card : ℝ)*(Real.log T)^2 := by
    apply (logVariance_le data S hS hU (fun p hp => (hpT p hp).2)).trans
    apply mul_le_mul_of_nonneg_left ?_ hr'.le
    apply (sq_le_sq₀ (div_nonneg (Real.log_nonneg hU) (by norm_num))
      (by linarith : 0 ≤ Real.log T)).mpr
    linarith
  apply signed_rectangle_exp_bound data b e hArith S hS o hr hW.le hWR hU
    (fun p hp => (hpT p hp).2) hsmall
    (ε := d*Real.log (∏ p ∈ S, (p : ℝ))/2) (a := d^2*S.card/64) (h := h)
  · positivity
  · rw [← log_period data S hS]
    have hh := rectangle_log_excess hd hd1.le hlogT hlogP hlarge
    linarith only [hh, hlogN, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · positivity
  · have hc : d^3 ≤ d^2 := by
      nlinarith [sq_nonneg d, mul_nonneg (sq_nonneg d) (by linarith : 0 ≤ 1-d)]
    have hh := mul_le_mul_of_nonneg_right hc hr'.le
    nlinarith [mul_nonneg (sq_nonneg d) hr'.le]
  · exact rectangle_hoeffding_exponent hr' hd.le (by linarith) hlogP hV hVup
  · exact rectangle_cube_growth hd hd1.le hlarge

theorem signedPlaneDet_sq (x y : Plane) :
    signedPlaneDet x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]
  unfold signedPlaneDet
  ring

theorem signedPlaneDet_isometry (o : Plane ≃ₗᵢ[ℝ] Plane) (x y : Plane) :
    |signedPlaneDet (o x) (o y)| = |signedPlaneDet x y| := by
  apply (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, sq_abs, signedPlaneDet_sq, signedPlaneDet_sq,
    o.norm_map, o.norm_map, o.inner_map_map]

/-- Fundamental-cell area is invariant under the chosen orientation. -/
theorem planarCellDet_orientation (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (o : Plane ≃ₗᵢ[ℝ] Plane) :
    |planarCellDet (e.trans o.toLinearEquiv)| = |planarCellDet e| := by
  exact signedPlaneDet_isometry o (e (Pi.single 0 1)) (e (Pi.single 1 1))

/-- A single explicit area scale suffices when the rectangle width is at least
one. The scale records exactly the actual lattice covolume and A4 constant. -/
theorem signed_rectangle (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (o : Plane ≃ₗᵢ[ℝ] Plane)
    {T R W d : ℝ} (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : max (2 / |planarCellDet e|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) * R * W ≤
      (∏ p ∈ S, (p : ℝ)) ^ (1-d))
    (hlarge : 1000 ≤ d^3*S.card) :
    (signMeasure S).real {σ | badSign data S (latticeRectangle b e o R W) σ} ≤
      Real.exp (-(d^3*S.card/5120)) := by
  have hWpos : 0 < W := by linarith
  have hRpos : 0 < R := hWpos.trans_le hWR
  have harea' : max (2 / |planarCellDet (e.trans o.toLinearEquiv)|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) * R * W ≤
      (∏ p ∈ S, (p : ℝ)) ^ (1-d) := by
    simpa only [planarCellDet_orientation] using harea
  let D := max (2 / |planarCellDet (e.trans o.toLinearEquiv)|)
    (Real.sqrt 2 * Real.sqrt (separationConstant data hArith))
  have hD : 0 ≤ D := (div_nonneg (by norm_num) (abs_nonneg _)).trans (le_max_left _ _)
  apply signed_rectangle_scaled data b e hArith S hS o hT hpT hWpos hWR hd hd1
  · calc
      _ = (2 / |planarCellDet (e.trans o.toLinearEquiv)|) * R * W := by ring
      _ ≤ D * R * W := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hRpos.le) hWpos.le
      _ ≤ _ := harea'
  · calc
      _ = (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) * R := by ring
      _ ≤ D * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hRpos.le
      _ ≤ D * R * W := le_mul_of_one_le_right (mul_nonneg hD hRpos.le) hW
      _ ≤ _ := harea'
  · exact hlarge

end Entry002.SignSeparation
