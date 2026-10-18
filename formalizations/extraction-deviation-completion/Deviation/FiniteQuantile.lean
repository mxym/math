import Deviation.Gaussian

open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- CDF of an actual finite weighted law, including possible zero atoms. -/
def finiteCDF (p f : ι → ℝ) (x : ℝ) : ℝ := ∑ i, if f i ≤ x then p i else 0

theorem finiteCDF_mono (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Monotone (finiteCDF p f) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : f i ≤ x
  · simp only [hx, le_trans hx hxy, ite_true, le_refl]
  · by_cases hy : f i ≤ y
    · simpa only [hx, hy, ite_false, ite_true] using hp i
    · simp only [hx, hy, ite_false, le_refl]

def quantileCandidates (p f : ι → ℝ) (ε : ℝ) : Finset ℝ :=
  (Finset.univ.image f).filter (fun x => ε ≤ finiteCDF p f x)

theorem quantileCandidates_nonempty [Nonempty ι] (p f : ι → ℝ)
    (hs : ∑ i, p i = 1) (ε : ℝ) (hε : ε ≤ 1) :
    (quantileCandidates p f ε).Nonempty := by
  classical
  let x := Finset.univ.sup' Finset.univ_nonempty f
  have hx : x ∈ Finset.univ.image f := by
    obtain ⟨i,hi,hif⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    exact Finset.mem_image.mpr ⟨i,hi,hif.symm⟩
  refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩⟩
  have hc : finiteCDF p f x = 1 := by
    unfold finiteCDF
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.le_sup' f hi)]
  simpa only [hc] using hε

/-- A genuine finite-law quantile, selected among its finitely many atom values. -/
def finiteQuantile [Nonempty ι] (p f : ι → ℝ) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) : ℝ :=
  (quantileCandidates p f ε).min' (quantileCandidates_nonempty p f hs ε hε)

theorem finiteQuantile_cdf [Nonempty ι] (p f : ι → ℝ) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) : ε ≤ finiteCDF p f (finiteQuantile p f hs ε hε) := by
  unfold finiteQuantile
  exact (Finset.mem_filter.mp (Finset.min'_mem (quantileCandidates p f ε) _)).2

theorem finiteQuantile_le_of_cdf [Nonempty ι] (p f : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) (hεpos : 0 < ε) (x : ℝ)
    (hx : ε ≤ finiteCDF p f x) : finiteQuantile p f hs ε hε ≤ x := by
  classical
  let A := Finset.univ.filter (fun i => f i ≤ x)
  have hA : A.Nonempty := by
    by_contra h
    have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hzero : finiteCDF p f x = 0 := by
      have hsum : finiteCDF p f x = ∑ i ∈ A, p i := by
        simp only [finiteCDF, A, Finset.sum_filter]
      rw [hsum, hempty, Finset.sum_empty]
    linarith
  let y := A.sup' hA f
  have hymem : y ∈ Finset.univ.image f := by
    obtain ⟨i, hiA, hif⟩ := Finset.exists_mem_eq_sup' hA f
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hif.symm⟩
  have hyx : y ≤ x := by
    apply Finset.sup'_le
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have heq : finiteCDF p f y = finiteCDF p f x := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiff : f i ≤ y ↔ f i ≤ x := by
      constructor
      · exact fun h => h.trans hyx
      · intro h
        exact Finset.le_sup' f (Finset.mem_filter.mpr ⟨hi,h⟩)
    simp only [hiff]
  have hy : y ∈ quantileCandidates p f ε :=
    Finset.mem_filter.mpr ⟨hymem,by simpa only [heq] using hx⟩
  exact (Finset.min'_le _ y hy).trans hyx

theorem finiteQuantile_le_iff [Nonempty ι] (p f : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) (hεpos : 0 < ε) (x : ℝ) :
    finiteQuantile p f hs ε hε ≤ x ↔ ε ≤ finiteCDF p f x := by
  constructor
  · intro h
    exact (finiteQuantile_cdf p f hs ε hε).trans (finiteCDF_mono p f hp h)
  · exact finiteQuantile_le_of_cdf p f hp hs ε hε hεpos x

end
end ExtractionDeviation
