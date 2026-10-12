import CofactorSignedRootRing
import CofactorNormalizedRankTwo

/-! A finite family of actual root rings with a reserve of zero slopes. -/
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev RingFamilyIndex (r : ℕ) (d : K → ℕ) := Fin r ⊕ ((k : K) × Fin (2*d k))

def ringFamilySlopes (r : ℕ) (d : K → ℕ) (z : (k : K) → Fin (2*d k) → ℂ) :
    RingFamilyIndex r d → ℂ := Sum.elim (fun _ => 0) (fun t => z t.1 t.2)

theorem ringFamily_card (r : ℕ) (d : K → ℕ) :
    Fintype.card (RingFamilyIndex r d) = r + 2*∑ k, d k := by
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma]
  rw [← Finset.mul_sum]

theorem ringFamily_sum (r : ℕ) (d : K → ℕ) (z : (k : K) → Fin (2*d k) → ℂ)
    (hz : ∀ k, ∑ j, z k j = 0) : ∑ i, ringFamilySlopes r d z i = 0 := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp [ringFamilySlopes,hz]

theorem ringFamily_square_sum (r : ℕ) (d : K → ℕ) (z : (k : K) → Fin (2*d k) → ℂ)
    (hz : ∀ k, ∑ j, z k j^2 = 0) : ∑ i, (ringFamilySlopes r d z i)^2 = 0 := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp [ringFamilySlopes,hz]

theorem ringFamily_normSq_sum (r : ℕ) (d : K → ℕ)
    (z : (k : K) → Fin (2*d k) → ℂ) (R : K → ℝ)
    (hz : ∀ k j, Complex.normSq (z k j) = R k) :
    ∑ i, Complex.normSq (ringFamilySlopes r d z i) = ∑ k, (2*d k : ℕ)*R k := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp [ringFamilySlopes,hz]

theorem ringFamily_imaginary_square_sum (r : ℕ) (d : K → ℕ)
    (z : (k : K) → Fin (2*d k) → ℂ) (R : K → ℝ)
    (hz : ∀ k, ∑ j, (z k j).im^2 = (d k : ℝ)*R k) :
    ∑ i, (ringFamilySlopes r d z i).im^2 = ∑ k, (d k : ℝ)*R k := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp [ringFamilySlopes,hz]

theorem ringFamily_homogeneous_product (r : ℕ) (d : K → ℕ)
    (z : (k : K) → Fin (2*d k) → ℂ) (a : K → ℂ)
    (hz : ∀ k, (∏ j, (X (0 : Fin 2)+C (z k j)*X (1 : Fin 2))) =
      X (0 : Fin 2)^(2*d k)+C (a k)*X (1 : Fin 2)^(2*d k)) :
    (∏ i, (X (0 : Fin 2)+C (ringFamilySlopes r d z i)*X (1 : Fin 2))) =
      X (0 : Fin 2)^r * ∏ k,
        (X (0 : Fin 2)^(2*d k)+C (a k)*X (1 : Fin 2)^(2*d k)) := by
  rw [Fintype.prod_sum_type,Fintype.prod_sigma]
  simp only [ringFamilySlopes,Sum.elim_inl,Sum.elim_inr,map_zero,zero_mul,add_zero,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,hz]

theorem exists_signed_ring_family (r : ℕ) (d : K → ℕ) (hd : ∀ k, 2 ≤ d k)
    (R : K → ℝ) (hR : ∀ k, 0 < R k) (ε : K → Bool) :
    ∃ z : (k : K) → Fin (2*d k) → ℂ,
      (∀ k j, Complex.normSq (z k j) = R k) ∧
      (∑ i, ringFamilySlopes r d z i) = 0 ∧
      (∑ i, (ringFamilySlopes r d z i)^2) = 0 ∧
      (∑ i, Complex.normSq (ringFamilySlopes r d z i)) = ∑ k, (2*d k : ℕ)*R k ∧
      (∑ i, (ringFamilySlopes r d z i).im^2) = ∑ k, (d k : ℝ)*R k ∧
      (∏ i, (X (0 : Fin 2)+C (ringFamilySlopes r d z i)*X (1 : Fin 2))) =
        X (0 : Fin 2)^r * ∏ k,
          (X (0 : Fin 2)^(2*d k)+C (signedRingCoefficient (ε k) (R k) (d k) : ℂ)*
            X (1 : Fin 2)^(2*d k)) := by
  classical
  choose z hnorm hsum hsquare him hprod using
    fun k => exists_signed_root_ring (d k) (hd k) (R k) (hR k) (ε k)
  exact ⟨z,hnorm,ringFamily_sum r d z hsum,ringFamily_square_sum r d z hsquare,
    ringFamily_normSq_sum r d z R hnorm,ringFamily_imaginary_square_sum r d z R him,
    ringFamily_homogeneous_product r d z _ hprod⟩

theorem ringFamily_zero_nonzero_witness (r : ℕ) (hr : 0 < r) (d : K → ℕ)
    (z : (k : K) → Fin (2*d k) → ℂ) (k : K) (hk : 0 < d k)
    (R : ℝ) (hR : 0 < R) (hz : ∀ j, Complex.normSq (z k j) = R) :
    ∃ i0 i1 : RingFamilyIndex r d,
      ringFamilySlopes r d z i0 = 0 ∧ ringFamilySlopes r d z i1 ≠ 0 := by
  let j : Fin (2*d k) := ⟨0,by omega⟩
  refine ⟨Sum.inl ⟨0,hr⟩,Sum.inr ⟨k,j⟩,rfl,?_⟩
  change z k j ≠ 0
  intro he
  have h := hz j
  rw [he,Complex.normSq_zero] at h
  exact (ne_of_gt hR) h.symm

end
end CofactorSpectral
