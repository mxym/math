import APPTReview.RankWeightedSchmidt
import APPTReview.PairHomogeneous

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def lacunarySpike (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (v : Fin m × Fin n → ℂ) :=
  (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
    (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d)+a • Matrix.vecMulVec v (star v)

theorem lacunarySpike_posSemidef (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (ha : 0≤a) (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (v : Fin m × Fin n → ℂ) :
    (lacunarySpike m n ds e a P v).PosSemidef := by
  have hsum : (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d).PosSemidef := by
    apply Finset.sum_induction (s:=ds.toFinset)
      (fun d : ℝ => (Real.sqrt (e d)*(m:ℝ)^(d/2-1)) • P d)
      (fun Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ => Q.PosSemidef)
      (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    intro d hd
    exact (hP d (List.mem_toFinset.mp hd)).smul
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  exact (Matrix.PosSemidef.one.add hsum).add ((Matrix.posSemidef_vecMulVec_self_star v).smul ha)

theorem lacunarySpike_quadratic (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (v x : Fin m × Fin n → ℂ) :
    (star x ⬝ᵥ (APPT.Quantum.partialTranspose (lacunarySpike m n ds e a P v)*ᵥx)).re=
      (star x ⬝ᵥ x).re+
      (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*
        (P d*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re)+
      a*(star v ⬝ᵥ (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv)).re := by
  rw [← trace_mul_pure,← trace_partialTranspose_pairing]
  have htrace : (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=star x ⬝ᵥ x := by
    rw [APPT.Quantum.partialTranspose_trace]
    change (∑ i,x i*star (x i))=∑ i,star (x i)*x i
    simp only [mul_comm]
  have hpure : (Matrix.vecMulVec v (star v)*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace=
      star v ⬝ᵥ (APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))*ᵥv) := by
    rw [Matrix.trace_mul_comm,trace_mul_pure]
  simp only [lacunarySpike,Matrix.add_mul,Matrix.sum_mul,Matrix.smul_mul,Matrix.one_mul,
    Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,htrace,hpure,
    Complex.add_re,Complex.re_sum,Complex.smul_re,smul_eq_mul]

/-- Physical sufficiency from a finite homogeneous graph bound. The later
uniform theorem discharges this bound; no Schmidt model is supplied by callers. -/
theorem lacunarySpike_partialTranspose_of_graph {m n : ℕ} (hm : 2≤m)
    (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ) (ha : 0≤a)
    (hgraph : ∀ w : ℝ → Fin m × Fin m → ℝ,
      (∀ d∈ds,∀ p,0≤w d p) → (∀ d∈ds,∀ p,w d p≤1) →
      (∀ d∈ds,(∑ p,w d p)≤2*(m:ℝ)^(2-d)) →
      ∀ s : Fin m → ℝ,(∀ i,0≤s i) → ∀ i j : Fin m,i≠j →
      realRayleigh (lacunarySparseMatrix m ds e w) s+2*a*s i*s j≤2*(∑ k,(s k)^2))
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (hI : ∀ d∈ds,(1-P d).PosSemidef)
    (htr : ∀ d∈ds,(P d).trace.re≤(m:ℝ)^(2-d))
    (v : Fin m × Fin n → ℂ) (hv : star v ⬝ᵥ v=1) :
    (APPT.Quantum.partialTranspose (lacunarySpike m n ds e a P v)).PosSemidef := by
  have hH := APPT.Quantum.partialTranspose_isHermitian (lacunarySpike_posSemidef m n ds e a ha P hP v).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  obtain ⟨s,L,hs,hss,hL,hW⟩ := exists_pure_signed_model x
  let w : ℝ → Fin m × Fin m → ℝ := fun d => symmetricCompressionWeight (compressionDiagonal (P d) L)
  have hb (d : ℝ) (hd : d∈ds) := compressed_schmidt_rank_witness (P d) L s (hP d hd) (hI d hd) hL hs
  have hw0 : ∀ d∈ds,∀ p,0≤w d p := fun d hd => (hb d hd).1
  have hw1 : ∀ d∈ds,∀ p,w d p≤1 := fun d hd => (hb d hd).2.1
  have hwr : ∀ d∈ds,(∑ p,w d p)≤2*(m:ℝ)^(2-d) := by
    intro d hd
    exact (hb d hd).2.2.2.2.1.trans (by have ht:=htr d hd; linarith)
  let A := lacunarySparseMatrix m ds e w
  let N : ℝ := (1/2)*realRayleigh A s
  have hpair (i j : Fin m) (hij : i≠j) : realRayleigh A s+2*a*s i*s j≤2*∑ k,(s k)^2 :=
    hgraph w hw0 hw1 hwr s hs i j hij
  have hbg : 0≤(∑ k,(s k)^2)-N := by
    let i : Fin m := ⟨0,by omega⟩
    let j : Fin m := ⟨1,by omega⟩
    have hij : i≠j := by intro he; have hv:=congrArg Fin.val he; dsimp [i,j] at hv; omega
    have hh := hpair i j hij
    have hn := mul_nonneg ha (mul_nonneg (hs i) (hs j))
    dsimp [N]
    nlinarith
  have hfloor : ((((∑ k,(s k)^2)-N):ℝ) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)+
      a • APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).PosSemidef := by
    rw [hW]
    apply diagonal_floor_lift L (schmidtSigned s) _ a hbg hL
    intro p
    unfold schmidtSigned
    split_ifs with hdiag hlt
    · exact add_nonneg hbg (mul_nonneg ha (sq_nonneg _))
    · exact add_nonneg hbg (mul_nonneg ha (mul_nonneg (hs _) (hs _)))
    · have hh := hpair p.1 p.2 hdiag
      dsimp [N]
      nlinarith
  have hsumtrace : -N≤∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*
      (P d*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re := by
    have hp (d : ℝ) (hd : d∈ds.toFinset) :
        (Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(-(1/2)*(∑ p,w d p*(s p.1*s p.2)))≤
        (Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(P d*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re := by
      apply mul_le_mul_of_nonneg_left
      · rw [hW]
        exact (hb d (List.mem_toFinset.mp hd)).2.2.2.2.2
      · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    have hh := Finset.sum_le_sum hp
    have hid : (∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(-(1/2)*(∑ p,w d p*(s p.1*s p.2))))=-N := by
      dsimp only [N,A]
      rw [lacunarySparseMatrix_rayleigh]
      calc
        _ = ∑ d∈ds.toFinset, -(1/2)*((Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(∑ p,w d p*(s p.1*s p.2))) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = _ := by rw [← Finset.mul_sum]; ring
    rwa [hid] at hh
  have hq := (RCLike.nonneg_iff.mp (hfloor.dotProduct_mulVec_nonneg v)).1
  change 0≤(star v ⬝ᵥ (_ *ᵥv)).re at hq
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_add,
    dotProduct_smul,Complex.add_re,Complex.smul_re,smul_eq_mul,hv,Complex.one_re,mul_one] at hq
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0≤(star x ⬝ᵥ (APPT.Quantum.partialTranspose (lacunarySpike m n ds e a P v)*ᵥx)).re
    rw [lacunarySpike_quadratic]
    linarith
  · change (star x ⬝ᵥ (APPT.Quantum.partialTranspose (lacunarySpike m n ds e a P v)*ᵥx)).im=0
    have him := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def,Complex.conj_im] at him
    linarith

end APPTReview
