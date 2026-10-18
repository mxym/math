import OperationalCompletion.HeterogeneousDecoder
import OperationalCompletion.PureTensorSector
import OperationalCompletion.WeightedCDF

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

/-- Reserving a large symmetric sector does not discard any of the decreasing
classical entropy-prefix guarantees. Both statements concern the same actual
unitary and complete local decoder selected before every unknown input. -/
theorem reserved_universal_set_protocol (m n k K J A B a₀ b₀ d₀ : ℕ)
    (hm : 0<m) (hn : 0<n) (hK : 0<K) (hd₀ : 0<d₀) (hd₀K : d₀≤K)
    (S : ℕ → Finset (Word (m*n) k)) (hS : Monotone S) (hS0 : S 0=∅)
    (d : ℕ → ℕ) (hd : ∀ j<J,0<d j) (hdk : ∀ j<J,d j≤K) (hdec : Antitone d)
    (hdp : d 0≤d₀) (ha : A+J*a₀≤m^k) (hb : B+J*b₀≤n^k)
    (hr₀ : pureSupportRank m n k≤(A/d₀)*(B/d₀))
    (hbudget : ∀ j<J,(S (j+1)).card*((m*n)*(m*n)+k-1).choose k≤(a₀/d j)*(b₀/d j)) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,V.IsProductLocal ∧
      (∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1),
        weightedDifference J (fun j => (d j:ℝ)/K)
          (fun j => ∑ w ∈ S j,iidLaw hX.1.isHermitian.eigenvalues k w)≤
            V.fidelity (tensorInput m n k X)) ∧
      (∀ Y : Matrix (Fin (m^k)×Fin (n^k)) (Fin (m^k)×Fin (n^k)) ℂ,Y.PosSemidef →
        purePowerProjection m n k*Y*purePowerProjection m n k=Y →
          ((d₀:ℝ)/K)*Y.trace.re≤V.fidelity Y) := by
  classical
  let H := purePowerProjection m n k
  let Q := fun j => nonsymmetricTensorProjection m n k (S j)
  have hHH : H.IsHermitian := purePowerProjection_hermitian m n k
  have hHP : H*H=H := purePowerProjection_idempotent m n k
  have hQH : ∀ j,(Q j).IsHermitian := fun j => nonsymmetricTensorProjection_hermitian _ _ _ _
  have hQP : ∀ j,Q j*Q j=Q j := fun j => nonsymmetricTensorProjection_idempotent _ _ _ _
  have hnest : ∀ i j,i≤j → Q i*Q j=Q i :=
    fun i j hij => (nonsymmetricTensorProjection_nested m n k _ _ (hS hij)).1
  have hnest' : ∀ i j,i≤j → Q j*Q i=Q i :=
    fun i j hij => (nonsymmetricTensorProjection_nested m n k _ _ (hS hij)).2
  have hHQ : ∀ j,H*Q j=0 ∧ Q j*H=0 := fun j => nonsymmetricTensorProjection_orthogonal_pure _ _ _ _
  have hQ0 : Q 0=0 := by simp [Q,hS0,nonsymmetricTensorProjection_empty]
  let P : Option (Fin J) → Matrix (Fin (m^k)×Fin (n^k)) (Fin (m^k)×Fin (n^k)) ℂ :=
    fun j => match j with | none => H | some j => chainSector Q j
  have hPH (j : Option (Fin J)) : (P j).IsHermitian := by
    cases j with
    | none => exact hHH
    | some j => exact projectionDifference_hermitian _ _ (hQH j) (hQH (j+1))
  have hPP (j : Option (Fin J)) : P j*P j=P j := by
    cases j with
    | none => exact hHP
    | some j =>
      exact projectionDifference_idempotent _ _ (hQP j) (hQP (j+1))
        (hnest _ _ (by omega)) (hnest' _ _ (by omega))
  have hOrth (j l : Option (Fin J)) (hjl : j≠l) : P j*P l=0 := by
    cases j with
    | none =>
      cases l with
      | none => exact False.elim (hjl rfl)
      | some l => change H*(Q (l+1)-Q l)=0; rw [mul_sub,(hHQ _).1,(hHQ _).1,sub_self]
    | some j =>
      cases l with
      | none => change (Q (j+1)-Q j)*H=0; rw [sub_mul,(hHQ _).2,(hHQ _).2,sub_self]
      | some l =>
        exact chainSector_orthogonal Q hQH hnest j l
          (fun h => hjl (congrArg some (Fin.ext h)))
  have hrP : ∀ j : Fin J,(P (some j)).rank≤(a₀/d j)*(b₀/d j) := by
    intro j
    exact (projectionDifference_rank_le _ _ (hQP (j+1)) (hnest _ _ (by omega))).trans
      ((nonsymmetricTensorProjection_rank_le m n k (S (j+1))).trans (hbudget j j.isLt))
  obtain ⟨V,hLocal,hV⟩ := heterogeneous_projection_protocol (m^k) (n^k) A B a₀ b₀ K J d₀ hK
    hd₀ hd₀K (fun j => d j) (fun j => hd j j.isLt) (fun j => hdk j j.isLt) ha hb P hPH hPP hOrth
    (by change H.rank≤_; rw [purePowerProjection_rank m n k hm hn]; exact hr₀) hrP
  have hsum : (∑ j,P j)=H+Q J := by
    rw [Fintype.sum_option]
    change H+(∑ j : Fin J,chainSector Q j)=H+Q J
    rw [chainSector_sum,hQ0,sub_zero]
  refine ⟨V,hLocal,?_,?_⟩
  · intro X hX
    let Y := tensorInput m n k X
    let F := fun j => ((H+Q j)*Y).trace.re
    let G := fun j => ∑ w ∈ S j,iidLaw hX.1.isHermitian.eigenvalues k w
    let w := fun j => (d j:ℝ)/K
    have hcomm : (∑ j,P j)*Y=Y*(∑ j,P j) := by
      rw [hsum,add_mul,mul_add,purePowerProjection_commutes_tensorInput,
        nonsymmetricTensorProjection_commutes]
    have hv := hV Y (tensorInput_density m n k X hX).1 hcomm
    have hcmp := weightedDifference_boundary_mono J w F G (by dsimp [w]; positivity)
      (fun j _ => div_le_div_of_nonneg_right (by exact_mod_cast hdec (by omega : j≤j+1))
        (Nat.cast_nonneg _)) (fun j _ => liftedProjection_mass_ge m n k (S j) X hX)
    have hG0 : G 0=0 := by simp [G,hS0]
    have hF0 : F 0=(H*Y).trace.re := by simp [F,hQ0]
    have hwd : weightedDifference J w F=∑ j : Fin J,w j*(chainSector Q j*Y).trace.re := by
      unfold weightedDifference
      apply Finset.sum_congr rfl
      intro j _
      simp only [F,chainSector,projectionDifference,add_mul,sub_mul,Matrix.trace_add,Matrix.trace_sub,Complex.add_re,Complex.sub_re]
      ring
    have hmass : 0≤(H*Y).trace.re := Extraction.positive_product_trace_re _ _
      (purePowerProjection_posSemidef m n k) (tensorInput_density m n k X hX).1
    have hweight : w 0≤(d₀:ℝ)/K := div_le_div_of_nonneg_right (by exact_mod_cast hdp) (Nat.cast_nonneg _)
    rw [hG0,mul_zero,add_zero,hF0,hwd] at hcmp
    have hgain := mul_le_mul_of_nonneg_right hweight hmass
    change weightedDifference J w G≤V.fidelity Y
    apply le_trans _ hv
    change _≤((d₀:ℝ)/K)*(H*Y).trace.re+∑ j : Fin J,w j*(chainSector Q j*Y).trace.re
    linarith
  · intro Y hY hsupport
    have hHY : H*Y=Y := by
      calc
        _ = H*(H*Y*H) := by rw [hsupport]
        _ = H*Y*H := by rw [←mul_assoc,←mul_assoc,hHP]
        _ = Y := hsupport
    have hYH : Y*H=Y := by
      calc
        _ = (H*Y*H)*H := by rw [hsupport]
        _ = H*Y*H := by rw [mul_assoc (H*Y) H H,hHP]
        _ = Y := hsupport
    have hQY (j : ℕ) : Q j*Y=0 := by
      calc
        _ = Q j*(H*Y) := by rw [hHY]
        _ = 0 := by rw [←mul_assoc,(hHQ j).2,zero_mul]
    have hYQ (j : ℕ) : Y*Q j=0 := by
      calc
        _ = (Y*H)*Q j := by rw [hYH]
        _ = 0 := by rw [mul_assoc,(hHQ j).1,mul_zero]
    have hcomm : (∑ j,P j)*Y=Y*(∑ j,P j) := by
      rw [hsum,add_mul,mul_add,hHY,hYH,hQY,hYQ]
    have hv := hV Y hY hcomm
    have hterms (j : Fin J) : (P (some j)*Y).trace.re=0 := by
      change ((Q (j+1)-Q j)*Y).trace.re=0
      rw [sub_mul,hQY,hQY,sub_self,Matrix.trace_zero,Complex.zero_re]
    simpa only [P,hterms,mul_zero,Finset.sum_const_zero,add_zero,hHY] using hv

end
end OperationalCompletion
