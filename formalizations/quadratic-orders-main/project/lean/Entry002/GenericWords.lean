import Entry002.FiniteProbability
import Entry002.Embedding

/-! Actual finite-alphabet walk words and uniform common-law smoothing.
The proofs generalize the pinned OpenAI WalkWords/InformationTelescope argument
from Gaussian integers to arbitrary additive groups and genuine additive
residue observations. No geometric shift/rate theorem is assumed here. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.GaussianMoat
namespace Entry002

variable {L R : Type*} [AddCommGroup L] [AddCommGroup R]

noncomputable def incrementWord (z : ℕ → L) (len t : ℕ) : Fin len → L :=
  fun i => z (t+i.val+1)-z (t+i.val)

lemma incrementWord_sum (z : ℕ → L) (len t : ℕ) :
    ∑ i, incrementWord z len t i = z (t+len)-z t := by
  simp only [incrementWord]
  rw [Fin.sum_univ_eq_sum_range (fun i => z (t+i+1)-z (t+i))]
  simpa only [Nat.add_assoc,Nat.add_zero] using
    Finset.sum_range_sub (fun i => z (t+i)) len

lemma block_displacement (z : ℕ → L) (len k t u : ℕ)
    (h : ∀ j<k, incrementWord z len (t+j*len)=incrementWord z len (u+j*len)) :
    z (t+k*len)-z t=z (u+k*len)-z u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun j hj => h j (by omega))
    have hk := congrArg (fun w : Fin len → L => ∑ i, w i) (h k (by omega))
    rw [incrementWord_sum,incrementWord_sum] at hk
    have ht : t+k*len+len=t+(k+1)*len := by ring
    have hu : u+k*len+len=u+(k+1)*len := by ring
    rw [ht,hu] at hk
    calc
      z (t+(k+1)*len)-z t =
          (z (t+(k+1)*len)-z (t+k*len))+(z (t+k*len)-z t) := by abel
      _ = (z (u+(k+1)*len)-z (u+k*len))+(z (u+k*len)-z u) := by rw [hk,hh]
      _ = z (u+(k+1)*len)-z u := by abel

lemma residue_block_update (ρ : L →+ R) (z : ℕ → L) (len k t u : ℕ)
    (hQ : ρ (z t)=ρ (z u))
    (hW : ∀ j<k, incrementWord z len (t+j*len)=incrementWord z len (u+j*len)) :
    ρ (z (t+k*len))=ρ (z (u+k*len)) := by
  have hd := congrArg ρ (block_displacement z len k t u hW)
  simpa only [map_sub,hQ,sub_left_inj] using hd

theorem incrementWord_blocks_entropy {Ω : Type*} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → L) (ρ : L →+ R)
    (len n : ℕ) (hL : 0<len) :
    p.cHf (fun ω => incrementWord z (n*len) (t ω)) (fun ω => ρ (z (t ω))) ≤
      ∑ j : Fin n, p.cHf (fun ω => incrementWord z len (t ω+j.val*len))
        (fun ω => ρ (z (t ω+j.val*len))) := by
  let W := fun ω (j : Fin n) => incrementWord z len (t ω+j.val*len)
  let Q := fun ω => ρ (z (t ω))
  have hvec : p.cHf (fun ω => incrementWord z (n*len) (t ω)) Q ≤ p.cHf W Q := by
    apply p.cHf_le_of_determined
    intro ω ν h _
    funext i
    let j : Fin n := ⟨i.val/len,(Nat.div_lt_iff_lt_mul hL).mpr i.isLt⟩
    let a : Fin len := ⟨i.val%len,Nat.mod_lt _ hL⟩
    have hh := congrFun (congrFun h j) a
    have he : j.val*len+a.val=i.val := by
      dsimp only [j,a]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val len
    simpa only [W,incrementWord,Nat.add_assoc,he] using hh
  apply hvec.trans
  apply p.cHf_blocks_le W Q
  intro j ω ν hW hQ
  apply residue_block_update ρ z len j.val (t ω) (t ν) hQ
  intro k hk
  have hh := congrFun hW ⟨k,lt_trans hk j.isLt⟩
  simpa only [FinLaw.prefixVar,Equiv.refl_apply,hk,ite_eq_left,Option.some.injEq,W] using hh

noncomputable def boundedWord (z : ℕ → L) (A : Finset L)
    (hs : ∀ t, z (t+1)-z t ∈ A) (len t : ℕ) : Fin len → A :=
  fun i => ⟨incrementWord z len t i,hs (t+i.val)⟩

lemma boundedWord_fibers (z : ℕ → L) (A : Finset L)
    (hs : ∀ t, z (t+1)-z t ∈ A) (len t u : ℕ) :
    boundedWord z A hs len t=boundedWord z A hs len u ↔
      incrementWord z len t=incrementWord z len u := by
  constructor
  · intro h; funext i; exact congrArg Subtype.val (congrFun h i)
  · intro h; funext i; exact Subtype.ext (congrFun h i)

theorem boundedWord_entropy_le {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (t : Ω → ℕ) (z : ℕ → L) (A : Finset L) (hs : ∀ t, z (t+1)-z t ∈ A) (len : ℕ) :
    p.Hf (fun ω => incrementWord z len (t ω)) ≤ (len:ℝ)*Real.log A.card := by
  classical
  have he : p.Hf (fun ω => incrementWord z len (t ω))=
      p.Hf (fun ω => boundedWord z A hs len (t ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact (boundedWord_fibers z A hs len (t ω) (t ν)).symm
  rw [he]
  have h := p.Hf_le_log_card_type (fun ω => boundedWord z A hs len (t ω))
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] using h

theorem word_residue_smoothing {Ω : Type*} [Fintype Ω] [Fintype R]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → L) (A : Finset L)
    (hs : ∀ t, z (t+1)-z t ∈ A) (ρ : L →+ R) (len N a : ℕ) (ha : a≤N) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z len (t v.1+v.2.val+a))
      (fun v => ρ (z (t v.1+v.2.val+a))) ≤
    P.cHf (fun v => incrementWord z len (t v.1+v.2.val))
      (fun v => ρ (z (t v.1+v.2.val)))+
      2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((len:ℝ)*Real.log A.card+2*Real.log (Fintype.card R)) := by
  classical
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  have he (u : Ω × Fin (N+1) → ℕ) :
      P.cHf (fun v => incrementWord z len (u v)) (fun v => ρ (z (u v))) =
      P.condH (fun v => boundedWord z A hs len (u v)) (fun v => ρ (z (u v))) := by
    rw [show P.condH (fun v => boundedWord z A hs len (u v)) (fun v => ρ (z (u v))) =
      P.cHf (fun v => boundedWord z A hs len (u v)) (fun v => ρ (z (u v))) by
        simp only [FinLaw.condH,FinLaw.cHf,FinLaw.Hf_eq_H]]
    apply P.cHf_congr_fibers
    · intro v w; exact (boundedWord_fibers z A hs len (u v) (u w)).symm
    · intro v w; rfl
  have h := p.smoothing_condH t N a ha (boundedWord z A hs len) (fun u => ρ (z u))
  change P.cHf _ _ ≤ P.cHf _ _+_+_
  rw [he,he]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] using h

theorem word_entropy_rate_monotone {Ω : Type*} [Fintype Ω] [Fintype R]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → L) (A : Finset L)
    (hs : ∀ t, z (t+1)-z t ∈ A) (ρ : L →+ R) {len K N : ℕ}
    (hL : 0<len) (hK : 0<K) (hdiv : len∣K) (hKN : K≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ a<K, 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((len:ℝ)*Real.log A.card+2*Real.log (Fintype.card R))≤ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z K (t v.1+v.2.val))
      (fun v => ρ (z (t v.1+v.2.val)))/K ≤
    P.cHf (fun v => incrementWord z len (t v.1+v.2.val))
      (fun v => ρ (z (t v.1+v.2.val)))/len+ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun v => ρ (z (u v))
  let H := P.cHf (fun v => incrementWord z len (u v)) Q
  obtain ⟨m,hm⟩ := hdiv
  have hm' : K=m*len := by simpa [Nat.mul_comm] using hm
  have hmp : 0<m := by nlinarith only [hK,hm]
  have hLp : (0:ℝ)<len := by exact_mod_cast hL
  have hmR : (0:ℝ)<m := by exact_mod_cast hmp
  have hblock := incrementWord_blocks_entropy P u z ρ len m hL
  have hsum : (∑ j : Fin m, P.cHf (fun v => incrementWord z len (u v+j.val*len))
      (fun v => ρ (z (u v+j.val*len)))) ≤ (m:ℝ)*(H+ε) := by
    have hh (j : Fin m) : P.cHf (fun v => incrementWord z len (u v+j.val*len))
        (fun v => ρ (z (u v+j.val*len)))≤H+ε := by
      have hj : j.val*len<K := by rw [hm']; exact Nat.mul_lt_mul_of_pos_right j.isLt hL
      have hsm := word_residue_smoothing p t z A hs ρ len N (j.val*len) (by omega)
      dsimp only at hsm
      change P.cHf _ _ ≤ H+_+_ at hsm
      have he := herr (j.val*len) hj
      linarith only [hsm,he]
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh'
  have htotal := hblock.trans hsum
  have hd := div_le_div_of_nonneg_right htotal (show (0:ℝ)≤m*len by positivity)
  have heq : ((m:ℝ)*(H+ε))/((m:ℝ)*len) = H/len+ε/len := by field_simp
  rw [heq] at hd
  have hε' : ε/len≤ε := div_le_self hε (by exact_mod_cast (show 1≤len by omega))
  change P.cHf (fun v => incrementWord z K (u v)) Q / (K:ℝ) ≤ H/len+ε
  rw [hm',Nat.cast_mul]
  exact hd.trans (add_le_add le_rfl hε')

end Entry002
