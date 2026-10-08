import EqualityFromAbsolute

namespace ComplexPencilEquality

open ComplexPencilLink
open ComplexPencilCert
open scoped ComplexConjugate

noncomputable section

private theorem sq_link_zero (z : ℂ)
    (hz : ComplexPencilLink.sq z = 0) : z = 0 := by
  exact ComplexPencilCert.sq_zero z
    ((ComplexPencilMain.sq_agree z).trans hz)

/-- Equality in the full complex three-coordinate Cauchy--Schwarz
inequality forces proportionality to the conjugate vector, provided
one coordinate of the second vector is nonzero. This is proved by
the exact Lagrange square identity, not by assuming a Hilbert-space
equality characterization. -/
theorem cauchy_three_equality_proportional
    (c0 c1 c2 t0 t1 t2 : ℂ)
    (ht0 : t0 ≠ 0)
    (heq : ComplexPencilLink.sq
        (c0*t0+c1*t1+c2*t2) =
      (ComplexPencilLink.sq c0+ComplexPencilLink.sq c1+
       ComplexPencilLink.sq c2) *
      (ComplexPencilLink.sq t0+ComplexPencilLink.sq t1+
       ComplexPencilLink.sq t2)) :
    ∃ z : ℂ, c0 = z*(conj t0) ∧
             c1 = z*(conj t1) ∧
             c2 = z*(conj t2) := by
  let p : ℂ := c0 * conj t1 - c1 * conj t0
  let q : ℂ := c0 * conj t2 - c2 * conj t0
  let r : ℂ := c1 * conj t2 - c2 * conj t1
  have hlag := ComplexPencilLink.complex_three_lagrange
    c0 c1 c2 t0 t1 t2
  have hsum :
      ComplexPencilLink.sq p +
      ComplexPencilLink.sq q +
      ComplexPencilLink.sq r = 0 := by
    dsimp [p,q,r]
    linarith
  have hp : 0 ≤ ComplexPencilLink.sq p :=
    ComplexPencilLink.sq_nonneg p
  have hq : 0 ≤ ComplexPencilLink.sq q :=
    ComplexPencilLink.sq_nonneg q
  have hr : 0 ≤ ComplexPencilLink.sq r :=
    ComplexPencilLink.sq_nonneg r
  have hp0 : p = 0 := sq_link_zero p (by linarith)
  have hq0 : q = 0 := sq_link_zero q (by linarith)
  have h01 : c0*(conj t1) = c1*(conj t0) :=
    sub_eq_zero.mp hp0
  have h02 : c0*(conj t2) = c2*(conj t0) :=
    sub_eq_zero.mp hq0
  have hconj : conj t0 ≠ 0 := by simpa using ht0
  let z : ℂ := c0 / conj t0
  have he0 : c0 = z*conj t0 := by
    dsimp [z]
    field_simp
  have he1 : c1 = z*conj t1 := by
    dsimp [z]
    calc
      _ = c1*conj t0 / conj t0 := by
            field_simp
      _ = c0*conj t1 / conj t0 := by rw [h01]
      _ = (c0/conj t0)*(conj t1) := by ring
  have he2 : c2 = z*conj t2 := by
    dsimp [z]
    calc
      _ = c2*conj t0 / conj t0 := by
            field_simp
      _ = c0*conj t2 / conj t0 := by rw [h02]
      _ = (c0/conj t0)*(conj t2) := by ring
  exact ⟨z,he0,he1,he2⟩

#print axioms ComplexPencilEquality.cauchy_three_equality_proportional

end
end ComplexPencilEquality
