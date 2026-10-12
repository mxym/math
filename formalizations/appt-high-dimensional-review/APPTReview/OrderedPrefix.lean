import APPTReview.CutReduction
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators
namespace APPTReview

noncomputable def uniformPrefix {D : ℕ} (k : Fin D) : Fin D → ℝ :=
  fun i => if i ≤ k then 1/((k.val+1:ℕ):ℝ) else 0

theorem prefix_sum_constant {D : ℕ} (k : Fin D) (c : ℝ) :
    (∑ i : Fin D, if i ≤ k then c else 0)=((k.val+1:ℕ):ℝ)*c := by
  have hset : (Finset.univ.filter (fun i : Fin D => i ≤ k))=Finset.Iic k := by
    ext i
    simp
  rw [← Finset.sum_filter,hset]
  simp

theorem uniformPrefix_sum {D : ℕ} (k : Fin D) : (∑ i, uniformPrefix k i)=1 := by
  unfold uniformPrefix
  rw [prefix_sum_constant]
  have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
  field_simp

theorem uniformPrefix_inner {D : ℕ} (k l : Fin D) (hkl : k ≤ l) :
    (∑ i, uniformPrefix k i*uniformPrefix l i)=1/((l.val+1:ℕ):ℝ) := by
  have he (i : Fin D) : uniformPrefix k i*uniformPrefix l i=
      if i ≤ k then (1/((k.val+1:ℕ):ℝ))*(1/((l.val+1:ℕ):ℝ)) else 0 := by
    by_cases hi : i ≤ k
    · simp [uniformPrefix,hi,hi.trans hkl]
    · simp [uniformPrefix,hi]
  simp_rw [he]
  rw [prefix_sum_constant]
  have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
  have hl : ((l.val+1:ℕ):ℝ)≠0 := by positivity
  field_simp

theorem uniformPrefix_squares {D : ℕ} (k : Fin D) :
    spectralSquares (uniformPrefix k)=1/((k.val+1:ℕ):ℝ) := by
  simpa only [spectralSquares,pow_two] using uniformPrefix_inner k k le_rfl

def spectrumZeroExtend {D : ℕ} (f : Fin D → ℝ) (i : ℕ) : ℝ :=
  if h : i < D then f ⟨i,h⟩ else 0

noncomputable def spectrumDifference {D : ℕ} (f : Fin D → ℝ) (i : ℕ) : ℝ :=
  spectrumZeroExtend f i-spectrumZeroExtend f (i+1)

noncomputable def orderedSimplexWeight {D : ℕ} (f : Fin D → ℝ) (i : Fin D) : ℝ :=
  ((i.val+1:ℕ):ℝ)*spectrumDifference f i.val

theorem spectrum_difference_tail {D : ℕ} (f : Fin D → ℝ) (j : Fin D) :
    (∑ i : Fin D, if j ≤ i then spectrumDifference f i.val else 0)=f j := by
  change (∑ i : Fin D, if j.val ≤ i.val then spectrumDifference f i.val else 0)=_
  rw [← Finset.sum_range (fun i : ℕ => if j.val ≤ i then spectrumDifference f i else 0)]
  rw [← Finset.sum_filter]
  have hset : ((Finset.range D).filter (fun i => j.val ≤ i))=Finset.Ico j.val D := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    tauto
  rw [hset]
  have ht := Finset.sum_Ico_sub (fun i => -spectrumZeroExtend f i) (show j.val ≤ D by omega)
  calc
    _ = ∑ i ∈ Finset.Ico j.val D, ((-spectrumZeroExtend f (i+1))-(-spectrumZeroExtend f i)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold spectrumDifference
      ring
    _ = (-spectrumZeroExtend f D)-(-spectrumZeroExtend f j.val) := ht
    _ = f j := by simp [spectrumZeroExtend,j.isLt]

/-- Exact gap-coordinate decomposition; no ordering is needed for the identity. -/
theorem ordered_prefix_expansion {D : ℕ} (f : Fin D → ℝ) :
    (∑ k, orderedSimplexWeight f k • uniformPrefix k)=f := by
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have he (k : Fin D) : orderedSimplexWeight f k*uniformPrefix k j=
      if j ≤ k then spectrumDifference f k.val else 0 := by
    unfold orderedSimplexWeight uniformPrefix
    by_cases hj : j ≤ k
    · simp only [if_pos hj]
      have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
      field_simp
    · simp [hj]
  simp_rw [he]
  exact spectrum_difference_tail f j

theorem orderedSimplexWeight_nonneg {D : ℕ} (f : Fin D → ℝ)
    (hf : Antitone f) (hn : ∀ i, 0 ≤ f i) (i : Fin D) :
    0 ≤ orderedSimplexWeight f i := by
  apply mul_nonneg (by positivity)
  unfold spectrumDifference
  have hi : spectrumZeroExtend f i.val=f i := by simp [spectrumZeroExtend,i.isLt]
  rw [hi]
  unfold spectrumZeroExtend
  split_ifs with hnext
  · exact sub_nonneg.mpr (hf (by change i.val ≤ i.val+1; omega))
  · simpa using hn i

/-- The gap weights have exactly the original total mass. -/
theorem orderedSimplexWeight_sum {D : ℕ} (f : Fin D → ℝ) :
    (∑ k, orderedSimplexWeight f k)=∑ j, f j := by
  have he := congrArg (fun g : Fin D → ℝ => ∑ j, g j) (ordered_prefix_expansion f)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  rw [Finset.sum_comm] at he
  simp only [← Finset.mul_sum,uniformPrefix_sum,mul_one] at he
  exact he

/-- Every linear constraint is transported through the exact gap expansion. -/
theorem ordered_prefix_linear {D : ℕ} (f c : Fin D → ℝ) :
    (∑ k, orderedSimplexWeight f k*(∑ j,c j*uniformPrefix k j))=∑ j,c j*f j := by
  have he := congrArg (fun g : Fin D → ℝ => ∑ j,c j*g j) (ordered_prefix_expansion f)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum] at he
  rw [Finset.sum_comm] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A full upper-bound reduction for every decreasing probability vector
satisfying the given linear cut, not just spectra with two or three levels. -/
theorem ordered_spectrum_cut_bound {D : ℕ} (f c : Fin D → ℝ) (C : ℝ)
    (hf : Antitone f) (hn : ∀ i, 0 ≤ f i) (hs : (∑ i,f i)=1)
    (hcut : (∑ i,c i*f i) ≤ 0)
    (hv : ∀ k, (∑ i,c i*uniformPrefix k i) ≤ 0 → spectralSquares (uniformPrefix k) ≤ C)
    (he : ∀ k l, 0 < (∑ i,c i*uniformPrefix k i) →
      (∑ i,c i*uniformPrefix l i) ≤ 0 →
      spectralSquares (cutPair (∑ i,c i*uniformPrefix k i)
        (-(∑ i,c i*uniformPrefix l i)) (uniformPrefix k) (uniformPrefix l)) ≤ C) :
    spectralSquares f ≤ C := by
  have h := spectralSquares_cut_bound (orderedSimplexWeight f)
    (fun k => ∑ i,c i*uniformPrefix k i) uniformPrefix C
    (orderedSimplexWeight_nonneg f hf hn)
    ((orderedSimplexWeight_sum f).trans hs)
    (by rw [ordered_prefix_linear]; exact hcut) hv he
  rwa [ordered_prefix_expansion] at h

end APPTReview
