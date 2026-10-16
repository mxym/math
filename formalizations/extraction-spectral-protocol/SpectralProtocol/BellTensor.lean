import SpectralProtocol.PureBell

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
  [Nonempty d] [Nonempty e]

theorem bellProjector_entry (i j k l : d) :
    Extraction.bellProjector (d := d) (i,j) (k,l) =
      if i=j ∧ k=l then (1:ℂ)/(Fintype.card d) else 0 := by
  change Extraction.bellVector (Extraction.bellCoeff d) (i,j) *
    star (Extraction.bellVector (Extraction.bellCoeff d) (k,l)) = _
  by_cases hij : i=j <;> by_cases hkl : k=l <;>
    simp [Extraction.bellVector,hij,hkl]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast,Complex.ofReal_inv,one_div,starRingEnd_apply] using Extraction.bellCoeff_mul_star (d := d)

/-- Maximally entangled projectors are preserved by any fixed common local
computational-basis relabelling. -/
theorem bellProjector_reindex (f : d ≃ e) :
    Matrix.reindexAlgEquiv ℂ ℂ (f.prodCongr f) (Extraction.bellProjector (d := d)) =
      Extraction.bellProjector (d := e) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  change Extraction.bellProjector (f.symm i,f.symm j) (f.symm k,f.symm l) = _
  rw [bellProjector_entry,bellProjector_entry,Fintype.card_congr f]
  simp only [f.symm.injective.eq_iff]

/-- The literal entrywise tensor power of h elementary two-qubit Bell densities. -/
noncomputable def bellPairTensor (h : ℕ) :
    Matrix ((Fin h → Fin 2) × (Fin h → Fin 2))
      ((Fin h → Fin 2) × (Fin h → Fin 2)) ℂ :=
  fun p q => ∏ t : Fin h,Extraction.bellProjector (d := Fin 2) (p.1 t,p.2 t) (q.1 t,q.2 t)

/-- A Bell target of local dimension 2^h is exactly h ordinary Bell pairs after
a fixed local basis identification; this is a matrix identity, not a gate-cost
assumption or a fidelity approximation. -/
theorem bellPairTensor_eq_bellProjector (h : ℕ) :
    bellPairTensor h = Extraction.bellProjector (d := Fin h → Fin 2) := by
  ext ⟨x,y⟩ ⟨z,w⟩
  rw [bellProjector_entry]
  unfold bellPairTensor
  by_cases hxy : x=y
  · subst y
    by_cases hzw : z=w
    · subst w
      simp only [bellProjector_entry,eq_self_iff_true,and_self,ite_true,
        Fintype.card_fin,Finset.prod_const,Finset.card_univ,Fintype.card_fun]
      rw [_root_.one_div_pow]
      simp
    · have hi : ∃ i,z i ≠ w i := by
        by_contra hno
        push_neg at hno
        exact hzw (funext hno)
      obtain ⟨i,hi⟩ := hi
      rw [if_neg (by simpa using hzw)]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [bellProjector_entry]
      simp [hi]
  · have hi : ∃ i,x i ≠ y i := by
      by_contra hno
      push_neg at hno
      exact hxy (funext hno)
    obtain ⟨i,hi⟩ := hi
    rw [if_neg (by simp [hxy])]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [bellProjector_entry]
    simp [hi]

noncomputable def bellQubitCoordinates (h : ℕ) : Fin (2^h) ≃ (Fin h → Fin 2) :=
  Fintype.equivOfCardEq (by simp)

/-- The finite-dimensional Bell target in the protocol theorem is the literal
h-pair tensor density in qubit coordinates. -/
theorem bellTarget_twoPow_reindex (h : ℕ) :
    Matrix.reindexAlgEquiv ℂ ℂ
      ((bellQubitCoordinates h).prodCongr (bellQubitCoordinates h))
      (Extraction.bellProjector (d := Fin (2^h))) = bellPairTensor h := by
  letI : Nonempty (Fin (2^h)) := ⟨⟨0,by positivity⟩⟩
  exact (bellProjector_reindex (bellQubitCoordinates h)).trans
    (bellPairTensor_eq_bellProjector h).symm

end SpectralProtocol