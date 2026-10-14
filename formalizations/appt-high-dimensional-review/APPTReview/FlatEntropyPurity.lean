import APPTReview.FullEntropySaturation

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

noncomputable def stateExcessPurity {m n : ℕ}
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℝ :=
  (Fintype.card (Fin m × Fin n):ℝ)^2*(APPT.Quantum.purity A-1/(Fintype.card (Fin m × Fin n):ℝ))

/-- Exact entropy/purity comparison on a relatively flat actual density
matrix; APPT is unnecessary for this finite Taylor consequence. -/
theorem density_flat_entropy_purity_bounds {m n : ℕ} (hm : 0<m) (hn : 0<n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ<1)
    (hflat : ∀ i,|(Fintype.card (Fin m × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ i-1|≤δ) :
    stateExcessPurity A/(1+δ)≤2*(Fintype.card (Fin m × Fin n):ℝ)*vonNeumannDeficit hρ ∧
    2*(Fintype.card (Fin m × Fin n):ℝ)*vonNeumannDeficit hρ≤stateExcessPurity A/(1-δ) := by
  let D := Fintype.card (Fin m × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  have hDN : 0<D := by dsimp [D];simpa using Nat.mul_pos hm hn
  have hD : (0:ℝ)<D := by exact_mod_cast hDN
  have hb : (0:ℝ)<1/(D:ℝ) := one_div_pos.mpr hD
  have hnon (i) : 0≤f i := by
    have ht := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using ht
  have hsum := ordered_eigenvalues_sum hρ.1.isHermitian hρ.2
  have he := spectrum_entropy_centering hDN f hnon hsum (1/(D:ℝ)) hb
  have hq := spectrum_quadratic_centering hDN f hsum (1/(D:ℝ)) hb
  have hpoint (i) : f i/(1/(D:ℝ))-1=(D:ℝ)*f i-1 := by field_simp <;> ring
  have hz : 1/((D:ℝ)*(1/(D:ℝ)))-1=0 := by field_simp <;> ring
  simp_rw [hpoint] at he hq
  rw [hz] at he hq
  simp only [entropyKernel,add_zero,Real.log_one,mul_zero,sub_zero,zero_pow,ne_eq,
    OfNat.ofNat_ne_zero,not_false_eq_true] at he
  have hE : (∑ i,entropyKernel ((D:ℝ)*f i-1))=(D:ℝ)*vonNeumannDeficit hρ := by
    unfold vonNeumannDeficit spectralVonNeumannEntropy
    change (∑ i,entropyKernel ((D:ℝ)*f i-1))=(D:ℝ)*(Real.log (D:ℝ)- -(∑ i,f i*Real.log (f i)))
    have hx : (Real.log (D:ℝ)+(∑ i,f i*Real.log (f i)))/(1/(D:ℝ))=
        (D:ℝ)*(Real.log (D:ℝ)- -(∑ i,f i*Real.log (f i))) := by field_simp <;> ring
    rw [hx] at he
    exact he.symm
  have hQ : (∑ i,((D:ℝ)*f i-1)^2)=stateExcessPurity A := by
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,sub_zero] at hq
    rw [← purity_eq_ordered_eigenvalues hρ.1.isHermitian] at hq
    unfold stateExcessPurity
    change _=(D:ℝ)^2*(APPT.Quantum.purity A-1/(D:ℝ))
    rw [hq]
    field_simp
  have hl := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (entropyKernel_quadratic_bounds δ ((D:ℝ)*f i-1) hδ hδ1 (hflat i)).1)
  have hu := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (entropyKernel_quadratic_bounds δ ((D:ℝ)*f i-1) hδ hδ1 (hflat i)).2)
  rw [← Finset.sum_div,hE,hQ] at hl hu
  have hdp : 1+δ≠0 := by positivity
  have hdm : 1-δ≠0 := by linarith
  have h1 : stateExcessPurity A/(1+δ)=2*(stateExcessPurity A/(2*(1+δ))) := by field_simp
  have h2 : stateExcessPurity A/(1-δ)=2*(stateExcessPurity A/(2*(1-δ))) := by field_simp
  constructor <;> nlinarith

theorem flat_purity_to_entropy_error (Q H K δ : ℝ) (hQ : 0≤Q) (hK : 0≤K)
    (hδ : 0≤δ) (hδ2 : δ≤1/2) (hl : Q/(1+δ)≤H) (hu : H≤Q/(1-δ))
    (hnear : |Q-K|≤δ) : |H-K|≤δ*(2*K+3) := by
  have hdp : 0<1+δ := by linarith
  have hdm : 0<1-δ := by linarith
  have hlo := (div_le_iff₀ hdp).mp hl
  have hup := (le_div_iff₀ hdm).mp hu
  have hH : 0≤H := (div_nonneg hQ hdp.le).trans hl
  have hn := abs_le.mp hnear
  have hHb : H≤2*(K+δ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hHb hδ
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

theorem flat_entropy_to_purity_error (Q H K δ : ℝ) (hK : 0≤K)
    (hδ : 0≤δ) (hδ2 : δ≤1/2) (hl : Q/(1+δ)≤H) (hu : H≤Q/(1-δ))
    (hnear : |H-K|≤δ) : |Q-K|≤δ*(K+2) := by
  have hdp : 0<1+δ := by linarith
  have hdm : 0<1-δ := by linarith
  have hlo := (div_le_iff₀ hdp).mp hl
  have hup := (le_div_iff₀ hdm).mp hu
  have hn := abs_le.mp hnear
  have hmul := mul_le_mul_of_nonneg_left hn.2 hδ
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

end APPTReview
