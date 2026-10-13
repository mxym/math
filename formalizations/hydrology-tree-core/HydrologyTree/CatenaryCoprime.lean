import HydrologyTree.CatenaryGlobal
import Mathlib.Algebra.Polynomial.Div

/-! Minimality and true rational-response identification for endpoint paths.
Nonzero outward rates are necessary here, unlike the weaker condition for an
unreduced coefficient Jacobian. No ODE controllability theorem is claimed. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

lemma isCoprime_root_step (P F : ℝ[X]) (d k : ℝ)
    (hk : k ≠ 0) (h : IsCoprime P F) : IsCoprime ((X+C d)*P-C k*F) P := by
  obtain ⟨u,v,h⟩ := h
  refine ⟨-C k⁻¹*v, u+C k⁻¹*v*(X+C d), ?_⟩
  calc
    (-C k⁻¹*v)*((X+C d)*P-C k*F) + (u+C k⁻¹*v*(X+C d))*P
        = u*P + (C k⁻¹*C k)*v*F := by ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]; exact h

/-- Actual characteristic and cofactor polynomials have no cancellations when
all internal rates are nonzero, with the root leak arbitrary. -/
theorem catenary_characteristic_cofactor_coprime (n : ℕ) (x : TreeRates n)
    (ha : ∀ i : Fin n, x.1 i.succ ≠ 0) (hf : ∀ i : Fin n, x.2 i ≠ 0) :
    IsCoprime (physicalCharacteristic (pathTree n) x) (physicalRootCofactor (pathTree n) x) := by
  induction n with
  | zero =>
    have hF : physicalRootCofactor (pathTree 0) x = 1 := by
      simp [physicalRootCofactor]
    rw [hF]
    exact isCoprime_one_right
  | succ n ih =>
    obtain ⟨⟨u,ell,f⟩,rfl⟩ := (prependRateEquiv n).surjective x
    rw [path_characteristic_recursion, path_cofactor_recursion]
    apply isCoprime_root_step _ _ _ _ (mul_ne_zero (ha 0) (hf 0))
    exact ih u (fun i => ha i.succ) (fun i => hf i.succ)

/-- If one rational response is represented by coprime polynomials of full
prescribed degree, any other monic representation of that same degree agrees. -/
theorem full_degree_fraction_unique (P F Q G : ℝ[X])
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : Q.natDegree = P.natDegree)
    (hcop : IsCoprime P F) (h : F*Q = G*P) : P = Q ∧ F = G := by
  have hdvd : P ∣ Q := hcop.dvd_of_dvd_mul_left (by rw [h]; exact dvd_mul_left P G)
  have he : P = Q := (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP hQ hdvd hdeg.le).symm
  constructor
  · exact he
  · rw [← he] at h
    exact mul_right_cancel₀ hP.ne_zero h

/-- Input/output transfer equality, expressed as a polynomial rational-function
identity, implies equality of all coefficients for a noncancelling reference path.
The alternative model's internal rates are arbitrary. -/
theorem catenary_response_identifies_coefficients (n : ℕ) (x y : TreeRates n)
    (ha : ∀ i : Fin n, x.1 i.succ ≠ 0) (hf : ∀ i : Fin n, x.2 i ≠ 0)
    (h : physicalRootCofactor (pathTree n) x * physicalCharacteristic (pathTree n) y =
      physicalRootCofactor (pathTree n) y * physicalCharacteristic (pathTree n) x) :
    pathCoefficientMap n x = pathCoefficientMap n y := by
  apply (physicalCoefficientMap_eq_iff (pathTree n) x y).mpr
  apply full_degree_fraction_unique _ _ _ _
    (physicalCharacteristic_monic _ _) (physicalCharacteristic_monic _ _) _
    (catenary_characteristic_cofactor_coprime n x ha hf) h
  rw [physicalCharacteristic_natDegree, physicalCharacteristic_natDegree]

/-- Full real-fiber identification from the actual rational response, for a path
with nonzero internal rates; the competitor is not assumed positive or minimal. -/
theorem catenary_global_transfer_identification (n : ℕ) (x y : TreeRates n)
    (ha : ∀ i : Fin n, x.1 i.succ ≠ 0) (hf : ∀ i : Fin n, x.2 i ≠ 0)
    (h : physicalRootCofactor (pathTree n) x * physicalCharacteristic (pathTree n) y =
      physicalRootCofactor (pathTree n) y * physicalCharacteristic (pathTree n) x) : x = y := by
  exact catenary_coefficient_fiber_unique n x y ⟨ha,fun i _ => hf i⟩
    (catenary_response_identifies_coefficients n x y ha hf h)

/-- Equality on the common nonpole domain of the ACTUAL root resolvent entries
implies the rational polynomial identity. Totalized values at poles are not used. -/
theorem physical_response_eq_implies_cross_identity {n : ℕ} (t : OrderedTree n)
    (x y : TreeRates n)
    (h : ∀ s : ℝ, (physicalCharacteristic t x).eval s ≠ 0 →
      (physicalCharacteristic t y).eval s ≠ 0 →
      physicalRootResponse t x s = physicalRootResponse t y s) :
    physicalRootCofactor t x * physicalCharacteristic t y =
      physicalRootCofactor t y * physicalCharacteristic t x := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinite_nonroots
    (physicalCharacteristic t x * physicalCharacteristic t y)
    (mul_ne_zero (physicalCharacteristic_monic t x).ne_zero
      (physicalCharacteristic_monic t y).ne_zero)).mono
  intro s hs
  have hh : (physicalCharacteristic t x).eval s * (physicalCharacteristic t y).eval s ≠ 0 := by
    simpa only [Set.mem_setOf_eq, Polynomial.eval_mul] using hs
  have hx := left_ne_zero_of_mul hh
  have hy := right_ne_zero_of_mul hh
  have he := h s hx hy
  rw [physicalRootResponse_eq, physicalRootResponse_eq] at he
  have hc := (div_eq_div_iff hx hy).mp he
  simpa only [Set.mem_setOf_eq, Polynomial.eval_mul] using hc

/-- Exact equality of actual root resolvents determines every path rate, provided
only the reference path has nonzero internal edges. No alternate-model hypotheses. -/
theorem catenary_global_resolvent_identification (n : ℕ) (x y : TreeRates n)
    (ha : ∀ i : Fin n, x.1 i.succ ≠ 0) (hf : ∀ i : Fin n, x.2 i ≠ 0)
    (h : ∀ s : ℝ, (physicalCharacteristic (pathTree n) x).eval s ≠ 0 →
      (physicalCharacteristic (pathTree n) y).eval s ≠ 0 →
      physicalRootResponse (pathTree n) x s = physicalRootResponse (pathTree n) y s) : x = y := by
  exact catenary_global_transfer_identification n x y ha hf
    (physical_response_eq_implies_cross_identity (pathTree n) x y h)

end HydrologyTree
