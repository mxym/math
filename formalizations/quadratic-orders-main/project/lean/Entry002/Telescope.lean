/-
Generic information telescope support adapted from OpenAI family028, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, https://github.com/openai/math.
Apache-2.0; see ../../upstream-028/LICENSE.

Exact declaration and proof bodies copied below:
* Information.lean: cIf through cIf_transport (upstream lines 217--315).
* WalkWords.lean: cHf_congr_fibers (upstream lines 178--187).
* InformationTelescope.lean: finite_entropy_telescope (lines 79--91),
  FinLaw.cIf_refinement (lines 138--149).
The Gaussian imports and surrounding sections are replaced by this generic
import/namespace context. The final Entry002 declarations are new generic
consequences of those results, with their required entropy rate hypotheses
explicit. They do not prove the Gaussian smoothing or block estimates or the
all-order moat target.
-/
import Entry002.Information

set_option autoImplicit false

namespace OAI
universe uOmega uAlpha uBeta uGamma uDelta uEpsilon uZeta
namespace GaussianMoat
open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta}
  {γ : Type uGamma} {δ : Type uDelta} {ε : Type uEpsilon} [Fintype Ω]

noncomputable def cIf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) : ℝ :=
  p.cHf X O-p.cHf X (fun ω => (O ω,Y ω))

lemma cIf_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    0 ≤ p.cIf X Y O := sub_nonneg.mpr (p.cHf_mono X O Y)

lemma cIf_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O = p.cIf Y X O := by
  unfold cIf cHf
  have he : p.Hf (fun ω => (X ω,(O ω,Y ω))) =
      p.Hf (fun ω => (Y ω,(O ω,X ω))) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  rw [he,p.Hf_pair_comm O Y,p.Hf_pair_comm O X]
  ring

lemma cIf_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.cHf X O := by
  have h := p.cHf_nonneg X (fun ω => (O ω,Y ω))
  unfold cIf
  linarith

lemma cIf_le_Hf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.Hf Y := by
  rw [p.cIf_comm]
  exact (p.cIf_le_cHf Y X O).trans (p.cHf_le_Hf Y O)

lemma cIf_chain (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → δ) (O : Ω → γ) :
    p.cIf X (fun ω => (Y ω,Z ω)) O =
      p.cIf X Y O+p.cIf X Z (fun ω => (O ω,Y ω)) := by
  unfold cIf
  have he : p.cHf X (fun ω => (O ω,(Y ω,Z ω))) =
      p.cHf X (fun ω => ((O ω,Y ω),Z ω)) := by
    unfold cHf
    rw [p.Hf_pair_assoc O Y Z]
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq,and_assoc]
  rw [he]
  ring

lemma cIf_conditioning_cost (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (O : Ω → γ) (S : Ω → δ) :
    p.cIf X Y (fun ω => (O ω,S ω)) ≤ p.cIf X Y O+p.Hf S := by
  have h1 := p.cHf_mono X O S
  have h2 := p.cHf_mono S O Y
  have h3 := p.cHf_le_Hf S O
  have h4 := p.cHf_nonneg S (fun ω => (X ω,(O ω,Y ω)))
  have h5 := p.cHf_chain X S (fun ω => (O ω,Y ω))
  have h6 := p.cHf_chain S X (fun ω => (O ω,Y ω))
  have he : p.cHf (fun ω => (X ω,S ω)) (fun ω => (O ω,Y ω)) =
      p.cHf (fun ω => (S ω,X ω)) (fun ω => (O ω,Y ω)) := by
    unfold cHf
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  have he' : p.cHf X (fun ω => ((O ω,S ω),Y ω)) =
      p.cHf X (fun ω => (S ω,(O ω,Y ω))) := by
    unfold cHf
    congr 1 <;> apply p.Hf_eq_of_fibers <;> intro ω ν <;>
      simp only [Prod.mk.injEq] <;> tauto
  unfold cIf
  rw [he']
  linarith only [h1,h2,h3,h4,h5,h6,he]

theorem cIf_transport (p : FinLaw Ω) (X : Ω → α) (O : Ω → β)
    (X' : Ω → γ) (O' : Ω → δ) (W : Ω → ε) {ζ : Type uZeta} (S : Ω → ζ)
    (hO : ∀ ω ν, (O ω,S ω)=(O ν,S ν) ↔ (O' ω,S ω)=(O' ν,S ν))
    (hX : ∀ ω ν, (X ω,O ω,S ω)=(X ν,O ν,S ν) ↔
      (X' ω,O' ω,S ω)=(X' ν,O' ν,S ν)) :
    p.cIf X (fun ω => (S ω,W ω)) O ≤ p.cIf X' W O'+2*p.Hf S := by
  have he : p.cIf X W (fun ω => (O ω,S ω)) =
      p.cIf X' W (fun ω => (O' ω,S ω)) := by
    rw [p.cIf_comm X W,p.cIf_comm X' W]
    unfold cIf cHf
    congr 2
    · apply p.Hf_eq_of_fibers
      intro ω ν
      simp only [Prod.mk.injEq,hO]
    · exact p.Hf_eq_of_fibers _ _ hO
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
  rw [p.cIf_chain X S W O,he]
  have h1 := p.cIf_le_Hf X S O
  have h2 := p.cIf_conditioning_cost X' W O' S
  linarith

lemma cHf_congr_fibers (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (C : Ω → γ) (D : Ω → δ)
    (hX : ∀ ω ν, X ω=X ν ↔ Y ω=Y ν) (hC : ∀ ω ν, C ω=C ν ↔ D ω=D ν) :
    p.cHf X C=p.cHf Y D := by
  unfold cHf
  rw [p.Hf_eq_of_fibers C D hC]
  congr 1
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq,hX,hC]

end FinLaw

lemma finite_entropy_telescope (n : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hnext : ∀ j<n, a (j+1)≤b j+ε) (hb : 0≤b n) :
    (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε := by
  have h : (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε-b n := by
    clear hb
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := ih (fun j hj => hnext j (by omega))
      have hh := hnext n (by omega)
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hh]
  linarith only [h,hb]

lemma FinLaw.cIf_refinement {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ)
    (h : ∀ ω ν, X ω = X ν → O ω = O ν) :
    p.cIf X Y O = p.cHf Y O - p.cHf Y X := by
  rw [p.cIf_comm]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers Y Y (fun ω => (O ω,X ω)) X
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hx => ⟨h ω ν hx,hx⟩⟩

end GaussianMoat
end OAI

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators

/-- Words over a finite alphabet have entropy at most their length times the
logarithm of the alphabet size. -/
theorem finite_word_entropy_le {Ω α : Type*} [Fintype Ω] [Fintype α]
    (p : FinLaw Ω) {L : ℕ} (X : Ω → Fin L → α) :
    p.Hf X ≤ (L : ℝ) * Real.log (Fintype.card α) := by
  rw [p.Hf_eq_H]
  have h := (p.map X).entropy_le_log_card
  simpa only [FinLaw.H, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

/-- A block entropy bound and a uniform shift estimate imply a word rate bound.
The shift estimate is an explicit hypothesis; its geometric proof is separate. -/
theorem entropy_rate_from_blocks {Ω α β γ δ : Type*} [Fintype Ω]
    (p : FinLaw Ω) (W : Ω → α) (V : Ω → β) (O : Ω → γ)
    {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (B : Fin m → Ω → α) (Q : Fin m → Ω → δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hblock : p.cHf W O ≤ ∑ j, p.cHf (B j) (Q j))
    (hshift : ∀ j, p.cHf (B j) (Q j) ≤ p.cHf V O + ε) :
    p.cHf W O / (m * L : ℕ) ≤ p.cHf V O / L + ε := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hshift j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have htotal := hblock.trans hsum
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hd := div_le_div_of_nonneg_right htotal (mul_nonneg hmR.le hLR.le)
  have he : (m : ℝ) * (p.cHf V O + ε) / ((m : ℝ) * L) =
      (p.cHf V O + ε) / L := by field_simp
  rw [he, add_div] at hd
  have hel : ε / (L : ℝ) ≤ ε := div_le_self hε (by exact_mod_cast hL)
  rw [Nat.cast_mul]
  linarith only [hd, hel]

/-- The common-law telescope for arbitrary observations on one finite law.
Successive observations must refine their predecessors. The entropy rate
comparison and initial support bound are explicit inputs; this theorem does
not establish the smoothing estimate that supplies the comparison. -/
theorem commonLawInformationTelescope {Ω : Type*} [Fintype Ω]
    {α β : ℕ → Type*} (p : FinLaw Ω)
    (X : (j : ℕ) → Ω → α j) (Q : (j : ℕ) → Ω → β j)
    (L : ℕ → ℕ) (n : ℕ) {ε C : ℝ}
    (hL : ∀ j ≤ n, 0 < L j)
    (hrefine : ∀ j ω ν, Q (j+1) ω = Q (j+1) ν → Q j ω = Q j ν)
    (hrate : ∀ j < n,
      p.cHf (X (j+1)) (Q (j+1)) / L (j+1) ≤
        p.cHf (X j) (Q (j+1)) / L j + ε)
    (hbound : p.Hf (X 0) ≤ (L 0 : ℝ) * C) :
    (∑ j ∈ Finset.range (n+1), p.cIf (Q (j+1)) (X j) (Q j) / L j) ≤
      C + n * ε := by
  let a := fun j => p.cHf (X j) (Q j) / L j
  let b := fun j => p.cHf (X j) (Q (j+1)) / L j
  have hnext (j : ℕ) (hj : j < n) : a (j+1) ≤ b j + ε := hrate j hj
  have hb : 0 ≤ b n := div_nonneg (p.cHf_nonneg _ _) (Nat.cast_nonneg _)
  have hi (j : ℕ) : p.cIf (Q (j+1)) (X j) (Q j) / L j = a j - b j := by
    rw [p.cIf_refinement, sub_div]
    exact hrefine j
  have ht := finite_entropy_telescope n a b ε hnext hb
  have ha : a 0 ≤ C := by
    apply (div_le_iff₀ (show (0 : ℝ) < L 0 by exact_mod_cast hL 0 (by omega))).mpr
    exact (p.cHf_le_Hf _ _).trans (by simpa only [mul_comm] using hbound)
  simp only [hi]
  linarith only [ht, ha]

/-- Finite-alphabet specialization with a proved initial entropy bound. The
successive conditional entropy rate comparisons remain explicit inputs. -/
theorem commonLawFiniteAlphabetTelescope {Ω α : Type*} [Fintype Ω] [Fintype α]
    {β : ℕ → Type*} (p : FinLaw Ω) (L : ℕ → ℕ)
    (X : (j : ℕ) → Ω → Fin (L j) → α) (Q : (j : ℕ) → Ω → β j)
    (n : ℕ) {ε : ℝ} (hL : ∀ j ≤ n, 0 < L j)
    (hrefine : ∀ j ω ν, Q (j+1) ω = Q (j+1) ν → Q j ω = Q j ν)
    (hrate : ∀ j < n,
      p.cHf (X (j+1)) (Q (j+1)) / L (j+1) ≤
        p.cHf (X j) (Q (j+1)) / L j + ε) :
    (∑ j ∈ Finset.range (n+1), p.cIf (Q (j+1)) (X j) (Q j) / L j) ≤
      Real.log (Fintype.card α) + n * ε :=
  commonLawInformationTelescope p X Q L n hL hrefine hrate (finite_word_entropy_le p (X 0))

end Entry002
