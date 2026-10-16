import MinimaxProfile.UniversalConverse

open scoped BigOperators ComplexOrder
open Matrix ExtractionSpectrum MinimaxProfile
namespace OperationalCompletion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual capped effect misses a classical subset outside its quadratic
budget. The subset is selected from the effect, not supplied as an assumption. -/
theorem finite_quadratic_error_tail (p z : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hz : ∀ i,0≤z i ∧ z i≤1) (r t : ℝ)
    (ht : 0<t) (ht1 : t<1) (hbudget : ∑ i,z i^2≤r) :
    ∃ S : Finset ι,(S.card:ℝ)≤r/t^2 ∧
      (1-t)*(1-∑ i ∈ S,p i)≤1-∑ i,p i*z i := by
  classical
  let S := Finset.univ.filter (fun i => t<z i)
  have hcard : (S.card:ℝ)*t^2≤r := by
    calc
      _ = ∑ i ∈ S,t^2 := by simp
      _ ≤ ∑ i ∈ S,z i^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : t<z i := (Finset.mem_filter.mp hi).2
        nlinarith
      _ ≤ ∑ i,z i^2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => sq_nonneg (z i))
      _ ≤ r := hbudget
  have hpoint (i : ι) : p i*z i≤t*p i+(1-t)*(if i∈S then p i else 0) := by
    by_cases hi : i∈S
    · rw [if_pos hi]
      nlinarith [mul_le_mul_of_nonneg_left (hz i).2 (hp i)]
    · have hi' : z i≤t := le_of_not_gt (by simpa only [S,Finset.mem_filter,
        Finset.mem_univ,true_and] using hi)
      rw [if_neg hi,mul_zero,add_zero]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi' (hp i)
  have hsum : (∑ i,p i*z i)≤t+(1-t)*(∑ i ∈ S,p i) := by
    calc
      _ ≤ (∑ i,(t*p i+(1-t)*(if i∈S then p i else 0))) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hs,mul_one]
        congr 2
        simp
  exact ⟨S,(le_div_iff₀ (sq_pos_of_pos ht)).mpr hcard,by nlinarith⟩

theorem diagonalized_effect_error_tail (p : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (W : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : (1-M).PosSemidef) (r t : ℝ)
    (ht : 0<t) (ht1 : t<1) (hbudget : (M*M).trace.re≤r) :
    ∃ S : Finset ι,(S.card:ℝ)≤r/t^2 ∧
      (1-t)*(1-∑ i ∈ S,p i) ≤
        1-(M*((W:Matrix ι ι ℂ)*Matrix.diagonal (fun i => (p i:ℂ))*
          (W:Matrix ι ι ℂ)ᴴ)).trace.re := by
  let Q := (W:Matrix ι ι ℂ)ᴴ*M*W
  let z := fun i => (Q i i).re
  have hQ : Q.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hW : (W:Matrix ι ι ℂ)ᴴ*W=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  have hIQ : (1-Q).PosSemidef := by
    have h := hI.conjTranspose_mul_mul_same (W:Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hW] using h
  have hz (i : ι) : 0≤z i ∧ z i≤1 := by
    have h0 := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i:=i))).1
    have h1 := (RCLike.nonneg_iff.mp (hIQ.diag_nonneg (i:=i))).1
    refine ⟨h0,?_⟩
    change (Q i i).re≤1
    simpa only [Matrix.sub_apply,Matrix.one_apply_eq,Complex.sub_re,Complex.one_re]
      using sub_nonneg.mp h1
  have hzb : ∑ i,z i^2≤r := by
    calc
      _ ≤ (Q*Q).trace.re := diagonal_square_le_trace_square Q hQ.isHermitian
      _ = (M*M).trace.re := congrArg Complex.re (trace_square_unitary_congruence M W)
      _ ≤ r := hbudget
  obtain ⟨S,hS,herr⟩ := finite_quadratic_error_tail p z hp hs hz r t ht ht1 hzb
  refine ⟨S,hS,?_⟩
  convert herr using 1
  rw [Extraction.trace_congruence_diagonal]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A physical completely-PPT protocol determines an actual tensor-word subset
whose missing iid mass lower-bounds its error. This applies to the same input
matrix as every universal lower bound, including singular input spectra. -/
theorem KrausPPTProtocol.tensor_error_tail (m n k K : ℕ)
    (hK : 0<K) (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    ∃ S : Finset (SymmetricSupport.Word (m*n) k),
      (S.card:ℝ)≤tensorBudget m n k K/t^2 ∧
      (1-t)*(1-∑ w ∈ S,iidLaw hX.1.isHermitian.eigenvalues k w) ≤
        1-V.fidelity (tensorInput m n k X) := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let e := (SpectralProtocol.bipartitePowerCoordinates m n k).symm
  let p := hX.1.isHermitian.eigenvalues
  let q := iidLaw p k ∘ e
  let W := reindexUnitary e (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k)
  have hqs : ∑ w,q w=1 := by
    change (∑ w,iidLaw p k (e w))=1
    rw [e.sum_comp]
    exact iidLaw_sum p (density_eigenvalues_sum X hX) k
  have hqp (w) : 0≤q w := iidLaw_nonneg p hX.1.eigenvalues_nonneg k _
  have hsp : (V.U:Matrix _ _ ℂ)*tensorInput m n k X*(V.U:Matrix _ _ ℂ)ᴴ =
      ((V.U*W:Matrix.unitaryGroup _ ℂ):Matrix _ _ ℂ)*
        Matrix.diagonal (fun w => (q w:ℂ))*
          ((V.U*W:Matrix.unitaryGroup _ ℂ):Matrix _ _ ℂ)ᴴ := by
    rw [tensorInput_spectral m n k X hX.1.isHermitian]
    simp only [Submonoid.coe_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rfl
  have hM := Extraction.targetEffect_rains V.A V.complete V.ptPositive
  have hb : (Extraction.targetEffect V.A*Extraction.targetEffect V.A).trace.re≤
      tensorBudget m n k K := by
    simpa only [tensorBudget,Fintype.card_fin,Nat.cast_pow] using
      Extraction.rainsEffect_trace_square_le _ _ hM
  obtain ⟨S,hS,herr⟩ := diagonalized_effect_error_tail q hqp hqs (V.U*W)
    (Extraction.targetEffect V.A) hM.1 hM.2.1 _ t ht ht1 hb
  let T := S.image e
  have hcard : T.card=S.card := Finset.card_image_of_injective S e.injective
  have hsum : (∑ w ∈ T,iidLaw p k w)=∑ w ∈ S,q w := by
    rw [Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      exact e.injective hij
  refine ⟨T,by simpa only [hcard] using hS,?_⟩
  rw [hsum]
  unfold KrausPPTProtocol.fidelity overlap
  rw [Extraction.target_overlap_eq,hsp]
  exact herr

end
end OperationalCompletion
