import BapatRealEndpoint

set_option autoImplicit false
open MeasureTheory Filter Set BapatFiniteRank BapatRankTwo.MarkedInversions
open scoped Topology

namespace BapatRealExistence
noncomputable section

def realOfRatMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j:ℝ)

@[fun_prop] theorem endpoint_matrix_continuous (n : ℕ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => (qPolynomial A).derivative.eval 1) := by
  simp_rw [qPolynomial_derivative_one]
  unfold weightedInversionSum permutationWeight
  fun_prop

@[fun_prop] theorem endpoint_rows_continuous (n : ℕ) :
    Continuous (fun v : Fin n → Fin 4 → ℝ => (qPolynomial (gram v)).derivative.eval 1) := by
  apply (endpoint_matrix_continuous n).comp
  unfold gram
  fun_prop

theorem exists_rational_gram_negative_endpoint :
    ∃ (N : ℕ) (v : Fin N → Fin 4 → ℚ), 4<N ∧
      (qPolynomial (realOfRatMatrix (gram v))).derivative.eval 1<0 := by
  obtain ⟨N,v,hN,hneg⟩ := exists_real_gram_negative_endpoint
  have hd : DenseRange (fun q : Fin N → Fin 4 → ℚ => fun i j => (q i j:ℝ)) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  have ho : IsOpen {w : Fin N → Fin 4 → ℝ | (qPolynomial (gram w)).derivative.eval 1<0} :=
    isOpen_lt (endpoint_rows_continuous N) continuous_const
  obtain ⟨q,hq⟩ := hd.exists_mem_open ho ⟨v,hneg⟩
  refine ⟨N,q,hN,?_⟩
  have he : realOfRatMatrix (gram q)=gram (fun i j => (q i j:ℝ)) := by
    ext i j
    simp [realOfRatMatrix,gram]
  rwa [he]

theorem real_gram_posSemidef {n : ℕ} (v : Fin n → Fin 4 → ℝ) : (gram v).PosSemidef := by
  convert Matrix.posSemidef_self_mul_conjTranspose (v : Matrix (Fin n) (Fin 4) ℝ) using 1
  ext i j
  change (∑ c, v i c*v j c) = ∑ c, v i c*star (v j c)
  simp

theorem exists_rational_posDef_negative_endpoint :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℚ), 4<N ∧ (realOfRatMatrix B).PosDef ∧
      (qPolynomial (realOfRatMatrix B)).derivative.eval 1<0 := by
  obtain ⟨N,v,hN,hneg⟩ := exists_rational_gram_negative_endpoint
  let A := realOfRatMatrix (gram v)
  have he : A=gram (fun i j => (v i j:ℝ)) := by ext i j; simp [A,realOfRatMatrix,gram]
  have hps : A.PosSemidef := by rw [he]; exact real_gram_posSemidef _
  have hc : Continuous (fun δ : ℝ => (qPolynomial (A+Matrix.diagonal (fun _ => δ))).derivative.eval 1) := by
    apply (endpoint_matrix_continuous N).comp
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i=j <;> simp [Matrix.diagonal,h] <;> fun_prop
  have hn : ∀ᶠ δ : ℝ in 𝓝 0, (qPolynomial (A+Matrix.diagonal (fun _ => δ))).derivative.eval 1<0 :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa using hneg))
  have hn' : ∀ᶠ δ : ℝ in 𝓝[>] 0, (qPolynomial (A+Matrix.diagonal (fun _ => δ))).derivative.eval 1<0 :=
    hn.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ,hδ,hδneg⟩ := (hn'.and self_mem_nhdsWithin).exists
  have hδpos : 0<δ := hδneg
  have ho : IsOpen {r : ℝ | 0<r ∧ (qPolynomial (A+Matrix.diagonal (fun _ => r))).derivative.eval 1<0} :=
    isOpen_lt continuous_const continuous_id |>.inter (isOpen_lt hc continuous_const)
  obtain ⟨r,hr,hrneg⟩ := Rat.denseRange_cast.exists_mem_open ho ⟨δ,hδpos,hδ⟩
  let B := gram v+Matrix.diagonal (fun _ => r)
  have hB : realOfRatMatrix B=A+Matrix.diagonal (fun _ => (r:ℝ)) := by
    ext i j
    by_cases h : i=j <;> simp [realOfRatMatrix,B,A,Matrix.diagonal,h]
  refine ⟨N,B,hN,?_,?_⟩
  · rw [hB]
    exact Matrix.PosDef.posSemidef_add hps (Matrix.PosDef.diagonal (fun _ => hr))
  · rwa [hB]

end
end BapatRealExistence
