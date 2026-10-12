import APPTReview.SchmidtRows

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem normalizeRows_reconstruct (R : Matrix a b ℂ) (s : a → ℝ)
    (hR : R*Rᴴ=Matrix.diagonal (fun i => ((s i)^2:ℂ))) :
    Matrix.diagonal (fun i => (s i : ℂ))*normalizeRows R s=R := by
  ext i x
  simp only [Matrix.diagonal_mul, normalizeRows_apply]
  by_cases hi : s i=0
  · have hz : (R*Rᴴ) i i=0 := by rw [hR]; simp [hi]
    simp [hi, gram_zero_row R i hz x]
  · have hc : (s i:ℂ)≠0 := by exact_mod_cast hi
    simp [← mul_assoc, hc]

theorem normalizeRows_gram (R : Matrix a b ℂ) (s : a → ℝ)
    (hR : R*Rᴴ=Matrix.diagonal (fun i => ((s i)^2:ℂ))) :
    normalizeRows R s*(normalizeRows R s)ᴴ=
      Matrix.diagonal (fun i => if s i=0 then (0:ℂ) else 1) := by
  ext i j
  have he : (normalizeRows R s*(normalizeRows R s)ᴴ) i j =
      (s i:ℂ)⁻¹*(s j:ℂ)⁻¹*(R*Rᴴ) i j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, normalizeRows_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [star_mul]
    simp
    ring
  rw [he,hR]
  by_cases hij : i=j
  · subst j
    by_cases hi : s i=0
    · simp [hi]
    · have hc : (s i:ℂ)≠0 := by exact_mod_cast hi
      simp [Matrix.diagonal_apply, hi]
      field_simp
  · simp [Matrix.diagonal_apply,hij]

theorem trace_unitary_left_gram (U : Matrix.unitaryGroup a ℂ) (R : Matrix a b ℂ) :
    (((U:Matrix a a ℂ)*R)*((U:Matrix a a ℂ)*R)ᴴ).trace=(R*Rᴴ).trace := by
  have hu : (U:Matrix a a ℂ)ᴴ*(U:Matrix a a ℂ)=1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  calc
    _ = ((U:Matrix a a ℂ)*(R*Rᴴ)*(U:Matrix a a ℂ)ᴴ).trace := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,hu,Matrix.one_mul]

/-- A full row-form Schmidt factorization; deficient rows have a proved zero indicator. -/
theorem exists_schmidt_rows (T : Matrix a b ℂ) :
    ∃ (U : Matrix.unitaryGroup a ℂ) (s : a → ℝ) (Z : Matrix a b ℂ),
      (∀ i, 0≤s i) ∧
      T=(U:Matrix a a ℂ)*Matrix.diagonal (fun i => (s i:ℂ))*Z ∧
      Z*Zᴴ=Matrix.diagonal (fun i => if s i=0 then (0:ℂ) else 1) ∧
      (∑ i, (s i)^2)=(T*Tᴴ).trace.re := by
  obtain ⟨U,R,d,hd,hT,hR⟩ := exists_unitary_orthogonal_rows T
  let s : a → ℝ := fun i => Real.sqrt (d i)
  have hs (i) : (s i)^2=d i := Real.sq_sqrt (hd i)
  have hR' : R*Rᴴ=Matrix.diagonal (fun i => ((s i)^2:ℂ)) := by
    rw [hR]
    congr 1
    funext i
    exact_mod_cast (hs i).symm
  refine ⟨U,s,normalizeRows R s,fun i => Real.sqrt_nonneg _,?_,normalizeRows_gram R s hR',?_⟩
  · rw [Matrix.mul_assoc,normalizeRows_reconstruct R s hR']
    exact hT
  · rw [hT,trace_unitary_left_gram,hR']
    simp [Matrix.trace_diagonal,Complex.re_sum,← Complex.ofReal_pow]

end APPTReview
