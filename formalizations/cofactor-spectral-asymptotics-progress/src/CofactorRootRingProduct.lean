import CofactorEntropyProduct
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! Actual homogeneous products for a full finite ring of complex slopes. -/
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
namespace CofactorSpectral
noncomputable section

def ringSlope {n : ℕ} (ζ a : ℂ) (j : Fin n) : ℂ := -(ζ^j.val*a)

theorem primitiveRoot_power_roots {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    Polynomial.nthRootsFinset n (1 : R) = (Finset.range n).image (fun j => ζ^j) := by
  classical
  rw [Polynomial.nthRootsFinset_def,hζ.nthRoots_eq (one_pow n)]
  simp only [mul_one,Multiset.toFinset_map,Multiset.toFinset_range]

theorem ring_homogeneous_product (n : ℕ) (hn : 0 < n) (ζ a : ℂ)
    (hζ : IsPrimitiveRoot ζ n) :
    (∏ j : Fin n, (X (0 : Fin 2) + C (ringSlope ζ a j) * X (1 : Fin 2))) =
      X (0 : Fin 2)^n - C (a^n) * X (1 : Fin 2)^n := by
  classical
  have hc : IsPrimitiveRoot (C ζ : MvPolynomial (Fin 2) ℂ) n :=
    hζ.map_of_injective (C_injective (Fin 2) ℂ)
  have h := IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul
    (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) (C a * X (1 : Fin 2)) hn hc
  rw [primitiveRoot_power_roots hc,Finset.prod_image] at h
  · have hp : (∏ j : Fin n, (X (0 : Fin 2)+C (ringSlope ζ a j)*X (1 : Fin 2))) =
        ∏ j ∈ Finset.range n, (X (0 : Fin 2)-(C ζ)^j*(C a*X (1 : Fin 2))) := by
      unfold ringSlope
      rw [Fin.prod_univ_eq_prod_range (fun j : ℕ =>
        X (0 : Fin 2)+C (-(ζ^j*a))*X (1 : Fin 2)) n]
      apply Finset.prod_congr rfl
      intro j _
      simp only [map_neg,map_mul,map_pow]
      ring
    rw [hp,← h]
    simp only [mul_pow,map_pow]
  · intro i hi j hj hij
    exact hc.injOn_pow hi hj hij

end
end CofactorSpectral
