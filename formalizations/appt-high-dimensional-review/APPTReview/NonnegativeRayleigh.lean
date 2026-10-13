import APPTReview.SparseGraphLimit
import APPTReview.GraphBounds

open scoped BigOperators
open Matrix
namespace APPTReview

noncomputable def realRayleigh {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ z : ι × ι,A z.1 z.2*(x z.1*x z.2)

/-- Homogeneous extension from nonnegative unit tests to every real vector.
The zero vector is treated explicitly, not normalized by a zero denominator. -/
theorem rayleigh_le_of_nonnegative_unit {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j,0≤A i j) (C : ℝ)
    (hunit : ∀ s : ι → ℝ,(∀ i,0≤s i) → (∑ i,(s i)^2)=1 → realRayleigh A s≤C)
    (x : ι → ℝ) : realRayleigh A x≤C*∑ i,(x i)^2 := by
  classical
  let q := ∑ i,(x i)^2
  have hq : 0≤q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hq0 : q=0
  · have hx (i : ι) : x i=0 := by
      have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (x j)) (Finset.mem_univ i)
      change (x i)^2≤q at hh
      rw [hq0] at hh
      nlinarith
    simp [realRayleigh,hx]
  · have hqP : 0<q := lt_of_le_of_ne hq (Ne.symm hq0)
    let a := Real.sqrt q
    let y : ι → ℝ := fun i => |x i|/a
    have ha : 0<a := Real.sqrt_pos.mpr hqP
    have ha2 : a^2=q := Real.sq_sqrt hq
    have hy0 (i : ι) : 0≤y i := div_nonneg (abs_nonneg _) ha.le
    have hy1 : (∑ i,(y i)^2)=1 := by
      simp only [y,div_pow,sq_abs]
      rw [← Finset.sum_div,ha2]
      change q/q=1
      exact div_self hq0
    have hh := mul_le_mul_of_nonneg_left (hunit y hy0 hy1) hq
    have he : q*realRayleigh A y=realRayleigh A (fun i => |x i|) := by
      unfold realRayleigh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      dsimp [y]
      rw [div_mul_div_comm,← pow_two,ha2]
      field_simp
    rw [he] at hh
    have hclip : realRayleigh A x≤realRayleigh A (fun i => |x i|) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (hA _ _)
      simpa only [abs_mul] using le_abs_self (x z.1*x z.2)
    exact hclip.trans (by simpa only [q,mul_comm] using hh)

/-- A genuine finite-matrix PSD conclusion from the fully homogeneous bound. -/
theorem matrix_cap_of_nonnegative_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hH : A.IsHermitian) (hA : ∀ i j,0≤A i j) (C : ℝ)
    (hunit : ∀ s : ι → ℝ,(∀ i,0≤s i) → (∑ i,(s i)^2)=1 → realRayleigh A s≤C) :
    (C • (1 : Matrix ι ι ℝ)-A).PosSemidef := by
  have hHerm := (Matrix.isHermitian_one.smul (show IsSelfAdjoint C by rfl)).sub hH
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro x
  have h := rayleigh_le_of_nonnegative_unit A hA C hunit x
  have he : star x ⬝ᵥ ((C • (1 : Matrix ι ι ℝ)-A)*ᵥx)=
      C*(∑ i,(x i)^2)-realRayleigh A x := by
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul]
    simp only [star_trivial,smul_eq_mul,dotProduct,Matrix.mulVec,realRayleigh,Fintype.sum_prod_type,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [he]
  linarith

end APPTReview
