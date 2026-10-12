import Mathlib.Analysis.Convex.Jensen
import APPTReview.OuterEndpoint

open scoped BigOperators
namespace APPTReview

/-- Boundary barycenter of a positive and a nonpositive constraint vertex. -/
noncomputable def cutPair {ν : Type*} (a b : ℝ) (u v : ν → ℝ) : ν → ℝ :=
  fun z => (b*u z+a*v z)/(a+b)

/-- Explicit mass transport for a simplex intersected with one halfspace.
This uses all crossing edges and surviving vertices, not an assumed vertex
classification or a finite enumeration. Zero constraint coefficients are allowed
on the nonpositive side. -/
theorem convex_mem_of_signed_balance {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    (S : Set (ν → ℝ)) (hS : Convex ℝ S)
    (p a : ι → ℝ) (q b : κ → ℝ) (u : ι → ν → ℝ) (v : κ → ν → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 ≤ b j)
    (hmass : (∑ i, p i)+(∑ j, q j)=1)
    (hbalance : (∑ i, p i*a i) ≤ ∑ j, q j*b j)
    (hv : ∀ j, v j ∈ S)
    (hedge : ∀ i j, cutPair (a i) (b j) (u i) (v j) ∈ S) :
    (∑ i, p i • u i)+(∑ j, q j • v j) ∈ S := by
  classical
  let A := ∑ i, p i*a i
  let B := ∑ j, q j*b j
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => mul_nonneg (hq j) (hb j))
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (ha i).le)
  by_cases hzero : B=0
  · have hpzero (i : ι) : p i=0 := by
      have hterm := Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => mul_nonneg (hp j) (ha j).le) (Finset.mem_univ i)
      have hle : p i*a i ≤ 0 := hterm.trans (hbalance.trans_eq hzero)
      nlinarith [ha i,hp i]
    have hqsum : (∑ j, q j)=1 := by simpa [hpzero] using hmass
    have hmem := hS.sum_mem (t:=Finset.univ) (w:=q) (z:=v)
      (fun j _ => hq j) hqsum (fun j _ => hv j)
    simpa [hpzero] using hmem
  · have hBP : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hzero)
    have hAB : A/B ≤ 1 := (div_le_one hBP).2 hbalance
    let w : (ι × κ) ⊕ κ → ℝ := Sum.elim
      (fun ij => p ij.1*q ij.2*(a ij.1+b ij.2)/B)
      (fun j => (1-A/B)*q j)
    let z : (ι × κ) ⊕ κ → ν → ℝ := Sum.elim
      (fun ij => cutPair (a ij.1) (b ij.2) (u ij.1) (v ij.2)) v
    have hpairSum : (∑ i, ∑ j, p i*q j*(a i+b j)/B) =
        (∑ i, p i)+(A/B)*(∑ j, q j) := by
      have he (i : ι) (j : κ) : p i*q j*(a i+b j)/B =
          (p i*a i/B)*q j+(p i/B)*(q j*b j) := by ring
      simp_rw [he]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      change (∑ i, (p i*a i/B)*(∑ j,q j))+(∑ i, (p i/B)*B)=_
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
      change (A/B)*(∑ j,q j)+((∑ i,p i)/B)*B=_
      rw [div_mul_cancel₀ _ hzero]
      ring
    have hw (x : (ι × κ) ⊕ κ) : 0 ≤ w x := by
      rcases x with ⟨i,j⟩ | j
      · exact div_nonneg (mul_nonneg (mul_nonneg (hp i) (hq j)) (add_nonneg (ha i).le (hb j))) hB0
      · exact mul_nonneg (sub_nonneg.mpr hAB) (hq j)
    have hwSum : (∑ x, w x)=1 := by
      simp only [w,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr]
      rw [hpairSum, ← Finset.mul_sum]
      nlinarith [hmass]
    have hz (x : (ι × κ) ⊕ κ) : z x ∈ S := by
      rcases x with ⟨i,j⟩ | j
      · exact hedge i j
      · exact hv j
    have hpairVector (k : ν) :
        (∑ i, ∑ j, (p i*q j*(a i+b j)/B)*cutPair (a i) (b j) (u i) (v j) k) =
        (∑ i, p i*u i k)+(A/B)*(∑ j, q j*v j k) := by
      have he (i : ι) (j : κ) :
          (p i*q j*(a i+b j)/B)*cutPair (a i) (b j) (u i) (v j) k =
          (p i*u i k/B)*(q j*b j)+(p i*a i/B)*(q j*v j k) := by
        have hd : a i+b j≠0 := ne_of_gt (add_pos_of_pos_of_nonneg (ha i) (hb j))
        unfold cutPair
        field_simp
      simp_rw [he]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      change (∑ i, (p i*u i k/B)*B)+(∑ i, (p i*a i/B)*(∑ j,q j*v j k))=_
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
      change ((∑ i,p i*u i k)/B)*B+(A/B)*(∑ j,q j*v j k)=_
      rw [div_mul_cancel₀ _ hzero]
    have heq : (∑ x, w x • z x)=(∑ i,p i • u i)+(∑ j,q j • v j) := by
      ext k
      simp only [w,z,Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
        Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [hpairVector]
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    rw [← heq]
    exact hS.sum_mem (t:=Finset.univ) (w:=w) (z:=z) (fun x _ => hw x) hwSum (fun x _ => hz x)

end APPTReview
