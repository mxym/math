import EqualityFromAbsolute

namespace ComplexPencilEquality

open ComplexPencilCert
open scoped ComplexConjugate

noncomputable section

/-- The determinant-zero, positive-leading-minors Hermitian kernel
is a complex line.  This lemma does *not* assume the desired
rank-one matrix conclusion: it proves the nullspace statement
directly from the division-free Cholesky polynomial certificate. -/
theorem Hermitian_nullspace_is_line
    (d1 d2 d3 : ℝ) (u v w : ℂ)
    (a0 a1 a2 b0 b1 b2 : ℂ)
    (hd1 : 0 < d1) (hminor : 0 < m12 d1 d2 u)
    (hdet : det3 d1 d2 d3 u v w = 0)
    (ha : Q3 d1 d2 d3 u v w a0 a1 a2 = 0)
    (hb : Q3 d1 d2 d3 u v w b0 b1 b2 = 0)
    (ha2 : a2 ≠ 0) :
    ∃ z : ℂ, b0 = z*a0 ∧ b1 = z*a1 ∧ b2 = z*a2 := by
  let m : ℝ := m12 d1 d2 u
  let alpha : ℂ := (d1 : ℂ)*w - (conj u)*v
  have ham : Q3 d1 d2 d3 u v w a0 a1 a2 = 0 := ha
  have hbm : Q3 d1 d2 d3 u v w b0 b1 b2 = 0 := hb
  have hm : 0 < m := hminor
  have hza1 : ComplexPencilCert.sq ((d1 : ℂ)*a0+u*a1+v*a2) = 0 := by
    have hch := cholesky_polynomial d1 d2 d3 u v w a0 a1 a2
    rw [ham, hdet] at hch
    simp only [mul_zero, zero_mul, zero_add] at hch
    have hsq2 : 0 ≤ ComplexPencilCert.sq ((m:ℂ)*a1+alpha*a2) := ComplexPencilCert.sq_nonneg _
    have hs : m*ComplexPencilCert.sq ((d1:ℂ)*a0+u*a1+v*a2) = 0 := by
      have hfirst : 0 ≤ m*ComplexPencilCert.sq
          ((d1:ℂ)*a0+u*a1+v*a2) :=
        mul_nonneg (le_of_lt hm) (ComplexPencilCert.sq_nonneg _)
      dsimp [m, alpha] at hsq2 hfirst ⊢
      linarith
    have hn : m ≠ 0 := ne_of_gt hm
    exact (mul_eq_zero.mp hs).resolve_left hn
  have hza2 : ComplexPencilCert.sq ((m : ℂ)*a1+alpha*a2) = 0 := by
    have hch := cholesky_polynomial d1 d2 d3 u v w a0 a1 a2
    rw [ham, hdet] at hch
    simp only [mul_zero, zero_mul, zero_add] at hch
    have hp1 : 0 ≤ m*ComplexPencilCert.sq ((d1:ℂ)*a0+u*a1+v*a2) :=
      mul_nonneg (le_of_lt hm) (ComplexPencilCert.sq_nonneg _)
    dsimp [m, alpha] at hp1 ⊢
    nlinarith
  have hzb1 : ComplexPencilCert.sq ((d1 : ℂ)*b0+u*b1+v*b2) = 0 := by
    have hch := cholesky_polynomial d1 d2 d3 u v w b0 b1 b2
    rw [hbm, hdet] at hch
    simp only [mul_zero, zero_mul, zero_add] at hch
    have hsq2 : 0 ≤ ComplexPencilCert.sq ((m:ℂ)*b1+alpha*b2) := ComplexPencilCert.sq_nonneg _
    have hs : m*ComplexPencilCert.sq ((d1:ℂ)*b0+u*b1+v*b2) = 0 := by
      have hfirst : 0 ≤ m*ComplexPencilCert.sq
          ((d1:ℂ)*b0+u*b1+v*b2) :=
        mul_nonneg (le_of_lt hm) (ComplexPencilCert.sq_nonneg _)
      dsimp [m, alpha] at hsq2 hfirst ⊢
      linarith
    exact (mul_eq_zero.mp hs).resolve_left (ne_of_gt hm)
  have hzb2 : ComplexPencilCert.sq ((m : ℂ)*b1+alpha*b2) = 0 := by
    have hch := cholesky_polynomial d1 d2 d3 u v w b0 b1 b2
    rw [hbm, hdet] at hch
    simp only [mul_zero, zero_mul, zero_add] at hch
    have hp1 : 0 ≤ m*ComplexPencilCert.sq ((d1:ℂ)*b0+u*b1+v*b2) :=
      mul_nonneg (le_of_lt hm) (ComplexPencilCert.sq_nonneg _)
    dsimp [m, alpha] at hp1 ⊢
    nlinarith
  have ha1eq : (d1 : ℂ)*a0+u*a1+v*a2=0 := sq_zero _ hza1
  have ha2eq : (m:ℂ)*a1+alpha*a2=0 := sq_zero _ hza2
  have hb1eq : (d1 : ℂ)*b0+u*b1+v*b2=0 := sq_zero _ hzb1
  have hb2eq : (m:ℂ)*b1+alpha*b2=0 := sq_zero _ hzb2
  let z : ℂ := b2/a2
  have hz : b2=z*a2 := by
    dsimp [z]
    field_simp
  have hb1eq' : b1=z*a1 := by
    have hz0 : (m:ℂ)*(b1-z*a1)=0 := by
      calc
        _ = ((m:ℂ)*b1+alpha*b2) -
              z*((m:ℂ)*a1+alpha*a2) := by rw [hz]; ring
        _ = 0 := by rw [hb2eq,ha2eq]; ring
    have hmcomplex : (m:ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hm)
    have hx := (mul_eq_zero.mp hz0).resolve_left hmcomplex
    exact sub_eq_zero.mp hx
  have hb0eq' : b0=z*a0 := by
    have hz0 : (d1:ℂ)*(b0-z*a0)=0 := by
      calc
        _ = ((d1:ℂ)*b0+u*b1+v*b2) -
              z*((d1:ℂ)*a0+u*a1+v*a2) := by
                rw [hz,hb1eq']; ring
        _ = 0 := by rw [hb1eq,ha1eq]; ring
    have hdcomplex : (d1:ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hd1)
    have hx := (mul_eq_zero.mp hz0).resolve_left hdcomplex
    exact sub_eq_zero.mp hx
  exact ⟨z,hb0eq',hb1eq',hz⟩

#print axioms ComplexPencilEquality.Hermitian_nullspace_is_line

end
end ComplexPencilEquality
