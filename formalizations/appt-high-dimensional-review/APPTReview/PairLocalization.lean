import APPTReview.FinitePairMass
import APPTReview.WeightedLocalization

open scoped BigOperators NNReal
open MeasureTheory Set
namespace APPTReview

/-- An arbitrary middle selection is controlled by its scale-band mass and the
mass of exceptional coordinates. Every pair is counted with the exact factor two. -/
theorem selected_pair_mass_bound {m : ℕ} (p : Fin m → ℝ) (x : Fin m → ScaleInterval)
    (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1)
    (C : Fin m → Fin m → Prop) [DecidableRel C]
    (bad : Fin m → Prop) [DecidablePred bad] (d t : ℝ)
    (hcover : ∀ i j,C i j →
      |((x i).val:ℝ)+((x j).val:ℝ)-d|≤t ∨ bad i ∨ bad j) :
    (∑ q : UpperPair m,if C q.val.1 q.val.2 then p q.val.1*p q.val.2 else 0) ≤
      ((scaleLift (finiteAtomicProbability p x hp hs)).prod
        (scaleLift (finiteAtomicProbability p x hp hs))).toMeasure.real (scaleBand d t)/2+
      (∑ i,if bad i then p i else 0) := by
  classical
  let F : Fin m → Fin m → ℝ := fun i j =>
    if |((x i).val:ℝ)+((x j).val:ℝ)-d|≤t then p i*p j else 0
  let H : Fin m → Fin m → ℝ := fun i j =>
    (if bad i then p i else 0)*p j+p i*(if bad j then p j else 0)
  have hp0 (i) : 0≤(if bad i then p i else 0) := by split_ifs <;> simp_all
  have hF0 (i j) : 0≤F i j := by
    dsimp [F]
    split_ifs
    · exact mul_nonneg (hp i) (hp j)
    · exact le_rfl
  have hH0 (i j) : 0≤H i j := by dsimp [H];exact add_nonneg (mul_nonneg (hp0 i) (hp j)) (mul_nonneg (hp i) (hp0 j))
  have hc (i j) : (if C i j then p i*p j else 0)≤F i j+H i j := by
    by_cases hh : C i j
    · rw [ite_eq_left hh]
      rcases hcover i j hh with hb | hb | hb
      · change p i*p j≤(if _ then p i*p j else 0)+H i j
        rw [ite_eq_left hb]
        linarith [hH0 i j]
      · dsimp only [H]
        rw [ite_eq_left hb]
        linarith [hF0 i j,mul_nonneg (hp i) (hp0 j)]
      · dsimp only [H]
        rw [ite_eq_left hb]
        linarith [hF0 i j,mul_nonneg (hp0 i) (hp j)]
    · rw [ite_eq_right hh]
      exact add_nonneg (hF0 i j) (hH0 i j)
  have hFs : ∀ i j,F i j=F j i := by intro i j; dsimp [F];rw [add_comm ((x i).val:ℝ),mul_comm (p i)]
  have hHs : ∀ i j,H i j=H j i := by intro i j; dsimp [H];ring
  have hFsum := upperPair_mass_le_half F hFs (fun i => hF0 i i)
  have hHsum := upperPair_mass_le_half H hHs (fun i => hH0 i i)
  have hHmass : (∑ i,∑ j,H i j)=2*(∑ i,if bad i then p i else 0) := by
    simp only [H,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,hs,mul_one,one_mul]
    ring
  have hmass := atomic_scaleBand_mass p x hp hs d t
  change _=∑ i,∑ j,F i j at hmass
  have htotal := Finset.sum_le_sum (fun q (_ : q∈(Finset.univ : Finset (UpperPair m))) => hc q.val.1 q.val.2)
  rw [Finset.sum_add_distrib] at htotal
  rw [hHmass] at hHsum
  rw [hmass]
  linarith

end APPTReview
