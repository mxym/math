import APPTReview.OrderedPrefix

open scoped BigOperators
namespace APPTReview

/-- Coefficients +1 on the first r+1 entries, -1 after q, and zero between. -/
noncomputable def prefixCut {D : ℕ} (r q : Fin D) : Fin D → ℝ :=
  fun i => ((r.val+1:ℕ):ℝ)*uniformPrefix r i+
    ((q.val+1:ℕ):ℝ)*uniformPrefix q i-1

noncomputable def prefixCutValue {D : ℕ} (r q k : Fin D) : ℝ :=
  ∑ i, prefixCut r q i*uniformPrefix k i

noncomputable def prefixCutHeight {D : ℕ} (r q k : Fin D) : ℝ :=
  if k ≤ r then ((k.val+1:ℕ):ℝ) else if k ≤ q then ((r.val+1:ℕ):ℝ)
  else ((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ)-((k.val+1:ℕ):ℝ)

theorem uniformPrefix_inner_swap {D : ℕ} (k l : Fin D) :
    (∑ i,uniformPrefix k i*uniformPrefix l i)=∑ i,uniformPrefix l i*uniformPrefix k i := by
  simp only [mul_comm]

theorem prefixCutValue_pairing {D : ℕ} (r q k : Fin D) :
    prefixCutValue r q k=
      ((r.val+1:ℕ):ℝ)*(∑ i,uniformPrefix r i*uniformPrefix k i)+
      ((q.val+1:ℕ):ℝ)*(∑ i,uniformPrefix q i*uniformPrefix k i)-1 := by
  unfold prefixCutValue prefixCut
  have he (i : Fin D) :
      (((r.val+1:ℕ):ℝ)*uniformPrefix r i+((q.val+1:ℕ):ℝ)*uniformPrefix q i-1)*uniformPrefix k i=
      ((r.val+1:ℕ):ℝ)*(uniformPrefix r i*uniformPrefix k i)+
      ((q.val+1:ℕ):ℝ)*(uniformPrefix q i*uniformPrefix k i)-uniformPrefix k i := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [← Finset.mul_sum,uniformPrefix_sum]

theorem prefixCutValue_early {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) (hkr : k ≤ r) :
    prefixCutValue r q k=1 := by
  rw [prefixCutValue_pairing,uniformPrefix_inner_swap r k,uniformPrefix_inner k r hkr,
    uniformPrefix_inner_swap q k,uniformPrefix_inner k q (hkr.trans hrq)]
  have hr : ((r.val+1:ℕ):ℝ)≠0 := by positivity
  have hq : ((q.val+1:ℕ):ℝ)≠0 := by positivity
  field_simp <;> ring

theorem prefixCutValue_middle {D : ℕ} (r q k : Fin D) (hrk : r ≤ k) (hkq : k ≤ q) :
    prefixCutValue r q k=((r.val+1:ℕ):ℝ)/((k.val+1:ℕ):ℝ) := by
  rw [prefixCutValue_pairing,uniformPrefix_inner r k hrk,
    uniformPrefix_inner_swap q k,uniformPrefix_inner k q hkq]
  have hq : ((q.val+1:ℕ):ℝ)≠0 := by positivity
  have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
  field_simp <;> ring

theorem prefixCutValue_late {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) (hqk : q ≤ k) :
    prefixCutValue r q k=
      (((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ)-((k.val+1:ℕ):ℝ))/((k.val+1:ℕ):ℝ) := by
  rw [prefixCutValue_pairing,uniformPrefix_inner r k (hrq.trans hqk),uniformPrefix_inner q k hqk]
  have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
  field_simp <;> ring

theorem prefixCutValue_height {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) :
    prefixCutValue r q k=prefixCutHeight r q k/((k.val+1:ℕ):ℝ) := by
  unfold prefixCutHeight
  split_ifs with hkr hkq
  · rw [prefixCutValue_early r q k hrq hkr]
    have hk : ((k.val+1:ℕ):ℝ)≠0 := by positivity
    exact (div_self hk).symm
  · exact prefixCutValue_middle r q k (le_of_not_ge hkr) hkq
  · exact prefixCutValue_late r q k hrq (le_of_not_ge hkq)

theorem prefixCutValue_pos_iff {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) :
    0 < prefixCutValue r q k ↔ k.val+1 < (r.val+1)+(q.val+1) := by
  have hr : (0:ℝ) < ((r.val+1:ℕ):ℝ) := by positivity
  have hq : (0:ℝ) < ((q.val+1:ℕ):ℝ) := by positivity
  have hk : (0:ℝ) < ((k.val+1:ℕ):ℝ) := by positivity
  by_cases hkr : k ≤ r
  · rw [prefixCutValue_early r q k hrq hkr]
    have hnat : k.val+1 < (r.val+1)+(q.val+1) := by have hv : k.val ≤ r.val := hkr; omega
    simp [hnat]
  · by_cases hkq : k ≤ q
    · rw [prefixCutValue_middle r q k (le_of_not_ge hkr) hkq]
      have hnat : k.val+1 < (r.val+1)+(q.val+1) := by have hv : k.val ≤ q.val := hkq; omega
      simp only [hnat,iff_true]
      exact div_pos hr hk
    · rw [prefixCutValue_late r q k hrq (le_of_not_ge hkq)]
      rw [div_pos_iff_of_pos_right hk]
      constructor
      · intro h
        have he : ((k.val+1:ℕ):ℝ) < ((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ) := by linarith
        exact_mod_cast he
      · intro h
        have he : ((k.val+1:ℕ):ℝ) < ((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ) := by exact_mod_cast h
        linarith

theorem prefixCutValue_nonpos_iff {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) :
    prefixCutValue r q k ≤ 0 ↔ (r.val+1)+(q.val+1) ≤ k.val+1 := by
  rw [← not_lt, prefixCutValue_pos_iff r q k hrq,not_lt]

/-- The positive height has enough room for the quadratic endpoint reduction. -/
theorem prefixCutHeight_room {D : ℕ} (r q k : Fin D) (hrq : r ≤ q) :
    prefixCutHeight r q k+((k.val+1:ℕ):ℝ) ≤ ((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ) := by
  unfold prefixCutHeight
  split_ifs with hkr hkq
  · have h1 : ((k.val+1:ℕ):ℝ) ≤ ((r.val+1:ℕ):ℝ) := by exact_mod_cast (show k.val+1 ≤ r.val+1 by exact Nat.add_le_add_right hkr 1)
    have h2 : ((r.val+1:ℕ):ℝ) ≤ ((q.val+1:ℕ):ℝ) := by exact_mod_cast (show r.val+1 ≤ q.val+1 by exact Nat.add_le_add_right hrq 1)
    linarith
  · have h1 : ((k.val+1:ℕ):ℝ) ≤ ((q.val+1:ℕ):ℝ) := by exact_mod_cast (show k.val+1 ≤ q.val+1 by exact Nat.add_le_add_right hkq 1)
    linarith
  · linarith

end APPTReview
