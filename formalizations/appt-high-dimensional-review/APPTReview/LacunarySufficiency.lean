import APPTReview.LacunaryQuantumWitness
import APPTReview.JointSufficiency

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Actual all-unitary APPT for a finite lacunary hierarchy and one spike.
The graph limit, same-frame rank bridge and spike decoupling are discharged. -/
theorem lacunarySpike_absolutelyPPT_eventually (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B a : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ha : 0≤a) (ha2 : a<2) (henergy : scaleEnergyBound ds e B<2) :
    ∃ M : ℕ, 2≤M ∧ ∀ m : ℕ, M≤m → ∀ n : ℕ,
      ∀ P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      (∀ d∈ds,(P d).PosSemidef) → (∀ d∈ds,(1-P d).PosSemidef) →
      (∀ d∈ds,(P d).trace.re≤(m:ℝ)^(2-d)) →
      ∀ v : Fin m × Fin n → ℂ, star v ⬝ᵥ v=1 →
      APPT.Quantum.AbsolutelyPPT (lacunarySpike m n ds e a P v) := by
  let C := max (scaleEnergyBound ds e B) a
  have hC : C<2 := max_lt henergy ha2
  let ε := (2-C)/2
  have hε : 0<ε := by dsimp [ε]; linarith
  obtain ⟨M,hM⟩ := lacunary_single_spike_bound ds hds hd1 e B hB he heB a ε ha hε
  refine ⟨max M 2,le_max_right _ _,?_⟩
  intro m hm n P hP hI htr v hv U
  have hm2 : 2≤m := (le_max_right _ _).trans hm
  have hmM : M≤m := (le_max_left _ _).trans hm
  let Q := fun d => (U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)*P d*(U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ
  have hQ (d) (hd : d∈ds) : (Q d).PosSemidef := (hP d hd).mul_mul_conjTranspose_same _
  have huu : (U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)*(U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hu : (U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ*(U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hQI (d) (hd : d∈ds) : (1-Q d).PosSemidef := by
    have h := (hI d hd).mul_mul_conjTranspose_same (U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    simpa [Q,Matrix.mul_sub,Matrix.sub_mul,huu] using h
  have ht (d) : (Q d).trace=(P d).trace := by
    dsimp [Q]
    rw [Matrix.trace_mul_cycle,hu,Matrix.one_mul]
  have hQt (d) (hd : d∈ds) : (Q d).trace.re≤(m:ℝ)^(2-d) := by rw [ht]; exact htr d hd
  have hpositive : (APPT.Quantum.partialTranspose
      (lacunarySpike m n ds e a Q ((U:Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)*ᵥv))).PosSemidef := by
    refine lacunarySpike_partialTranspose_of_graph hm2 ds e a ha ?_ Q hQ hQI hQt _
      ((unitary_normSq_general U v).trans hv)
    intro w hw0 hw1 hwr s hs i j hij
    have hh := hM m hmM w hw0 hw1 hwr s hs i j hij
    have hconst : max (scaleEnergyBound ds e B) a+ε≤2 := by change C+ε≤2; dsimp [ε]; linarith
    exact hh.trans (mul_le_mul_of_nonneg_right hconst
      (Finset.sum_nonneg (fun k _ => sq_nonneg (s k))))
  simpa only [lacunarySpike,Q,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,huu,pure_conjugate_general] using hpositive

end APPTReview
