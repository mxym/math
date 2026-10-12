import EqualityCubic

open scoped ComplexConjugate

namespace ComplexPencilEquality
open ComplexPencilCert

noncomputable section

/-! The fully formalized strong version of the Hermitian
principal-minor criterion: strictly positive determinant
forces strict positive quadratic form away from zero.
The singular-pivot cases are included. -/
theorem hermitian3_zero_quadratic_det_zero
    (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ)
    (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (h3 : 0 ≤ d3)
    (h12 : 0 ≤ m12 d1 d2 u)
    (h13 : 0 ≤ m13 d1 d3 v)
    (h23 : 0 ≤ m23 d2 d3 w)
    (hd : 0 ≤ det3 d1 d2 d3 u v w)
    (hQ : Q3 d1 d2 d3 u v w b1 b2 b3 = 0)
    (hnonzero : b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0) :
    det3 d1 d2 d3 u v w = 0 := by
  by_contra hdetne
  have hdet : 0 < det3 d1 d2 d3 u v w :=
    lt_of_le_of_ne hd (Ne.symm hdetne)
  have hd1 : 0 < d1 := by
    by_contra hnot
    have hd1z : d1=0 :=
      le_antisymm (le_of_not_gt hnot) h1
    have hsqU : ComplexPencilCert.sq u=0 := by
      have hh:=h12
      simp [m12, hd1z] at hh
      nlinarith [ComplexPencilCert.sq_nonneg u]
    have hsqV : ComplexPencilCert.sq v=0 := by
      have hh:=h13
      simp [m13, hd1z] at hh
      nlinarith [ComplexPencilCert.sq_nonneg v]
    have hu : u=0 := sq_zero u hsqU
    have hv : v=0 := sq_zero v hsqV
    have hdet0 : det3 d1 d2 d3 u v w=0 := by
      simp [det3, hd1z, hu, hv, ComplexPencilCert.sq]
    exact (ne_of_gt hdet) hdet0
  have hm : 0 < m12 d1 d2 u := by
    by_contra hnot
    have hmz : m12 d1 d2 u=0 :=
      le_antisymm (le_of_not_gt hnot) h12
    have hrel := minor_det3 d1 d2 d3 u v w
    rw [hmz] at hrel
    have hsq : 0 ≤ ComplexPencilCert.sq ((d1 : ℂ)*w-(conj u)*v) :=
      ComplexPencilCert.sq_nonneg _
    have hP : 0 < d1 * det3 d1 d2 d3 u v w :=
      mul_pos hd1 hdet
    nlinarith
  have hchol := cholesky_polynomial
      d1 d2 d3 u v w b1 b2 b3
  rw [hQ] at hchol
  have hA : 0 ≤ m12 d1 d2 u *
    ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3) :=
      mul_nonneg h12 (ComplexPencilCert.sq_nonneg _)
  have hB : 0 ≤ ComplexPencilCert.sq (((m12 d1 d2 u : ℝ):ℂ)*b2+
       ((d1 : ℂ)*w-(conj u)*v)*b3) :=
       ComplexPencilCert.sq_nonneg _
  have hC : 0 ≤ d1*det3 d1 d2 d3 u v w*ComplexPencilCert.sq b3 :=
      mul_nonneg (mul_nonneg h1 hd) (ComplexPencilCert.sq_nonneg _)
  have hA0 : m12 d1 d2 u *
    ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3)=0 := by
    linarith
  have hB0 : ComplexPencilCert.sq (((m12 d1 d2 u : ℝ):ℂ)*b2+
       ((d1 : ℂ)*w-(conj u)*v)*b3)=0 := by
    linarith
  have hC0 : d1*det3 d1 d2 d3 u v w*ComplexPencilCert.sq b3=0 := by
    linarith
  have hb3sq : ComplexPencilCert.sq b3=0 :=
    (mul_eq_zero.mp hC0).resolve_left
      (ne_of_gt (mul_pos hd1 hdet))
  have hb3 : b3=0 := sq_zero b3 hb3sq
  have he1 : ((m12 d1 d2 u : ℝ):ℂ)*b2+
        ((d1 : ℂ)*w-(conj u)*v)*b3=0 :=
    sq_zero _ hB0
  have he0 : (d1 : ℂ)*b1+u*b2+v*b3=0 := by
    have hSq : ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3)=0 :=
       (mul_eq_zero.mp hA0).resolve_left (ne_of_gt hm)
    exact sq_zero _ hSq
  have hb2 : b2=0 := by
    have htmp : ((m12 d1 d2 u : ℝ):ℂ)*b2=0 := by
      simpa [hb3] using he1
    exact (mul_eq_zero.mp htmp).resolve_left (by
      exact_mod_cast (ne_of_gt hm))
  have hb1 : b1=0 := by
    have htmp : (d1 : ℂ)*b1=0 := by
      simpa [hb2, hb3] using he0
    exact (mul_eq_zero.mp htmp).resolve_left (by
      exact_mod_cast (ne_of_gt hd1))
  rcases hnonzero with h | h | h
  · exact h hb1
  · exact h hb2
  · exact h hb3

#print axioms ComplexPencilEquality.hermitian3_zero_quadratic_det_zero

end
end ComplexPencilEquality
