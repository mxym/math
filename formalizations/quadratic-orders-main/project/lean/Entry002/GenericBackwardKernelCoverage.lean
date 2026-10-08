import Entry002.GenericKernelCoverage

/-! Actual backward coverage amplification for composed forward walk kernels.
Generic low-residue proof bodies are adapted from upstream-028
SignedResidues.lean lines 109–131 and 161–228; actual kernel applications follow
EntropyBand.lean lines 10–203, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
-/
namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical

lemma lowResidues_prob {G : Type*} [Fintype G] (p : FinLaw G) (τ : ℝ) :
    p.prob (fun x => x∈p.lowResidues τ) ≤ τ*(p.lowResidues τ).card/(Fintype.card G : ℝ) := by
  have he : p.prob (fun x => x∈p.lowResidues τ)=∑ x∈p.lowResidues τ, p x := by
    unfold prob
    trans ∑ x, if x∈p.lowResidues τ then p.mass x else 0
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [he]
  have hh := Finset.sum_le_sum (s := p.lowResidues τ) (fun x hx =>
    ((Finset.mem_filter.mp hx).2).le)
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  have heq : ((p.lowResidues τ).card : ℝ)*(τ/(Fintype.card G : ℝ)) =
      τ*(p.lowResidues τ).card/(Fintype.card G : ℝ) := by ring
  rw [heq] at hh
  exact hh

theorem lowResidues_backward {Ω Γ ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type*) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (u u' b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0<n) (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
    (hnext : ∑ i, w i*p.prob (fun ω => u' i≤
      (((q ω).map (h i)).lowResidues (τ+4*δ)).card) ≤ η')
    (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : e<η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd))≤e)
    (hb : ∀ i, 1≤b i)
    (hv : ∀ i, v≤Real.log (Fintype.card (G i))-Real.log (b i))
    (hu' : ∀ i, u' i/δ≤b i)
    (herr : ∀ i, (Fintype.card (G i) : ℝ)*
      Real.exp (-(n : ℝ)*δ^2*u i/(2*(Fintype.card (G i) : ℝ)))≤ε) :
    w.prob (fun i => u i≤(((p.joint q).map (fun x => Y i x.1+h i x.2)).lowResidues τ).card) ≤ η := by
  let P := fun i => (p.joint q).map (fun x => Y i x.1+h i x.2)
  let K := fun i => (P i).lowResidues τ
  let B₀ := fun i => u i≤(K i).card
  let B₁ := fun i ω => u' i≤(((q ω).map (h i)).lowResidues (τ+4*δ)).card
  let E := fun i ω => (((q ω).map (h i)).lowResidues (τ+4*δ))
  apply backward_coverage_step G w p q Y h B₀ B₁ K E b hn hτ hτ1 hδ hδ1
    hε hη hnext hsmall hscale hgap hdata
  · intro i hi
    apply Finset.card_pos.mp
    have hh : (0 : ℝ)<(K i).card := (hu i).trans_le hi
    exact_mod_cast hh
  · intro i _; exact hb i
  · intro i _; exact hv i
  · intro i _
    have hh := (P i).lowResidues_prob τ
    rw [prob_map] at hh
    exact hh
  · intro i _ ω _ x hx
    exact (((q ω).map (h i)).not_mem_lowResidues _ x).mp hx
  · intro i _ ω hω
    have hh : ((E i ω).card : ℝ)<u' i := lt_of_not_ge hω
    exact (div_le_div_of_nonneg_right hh.le hδ.le).trans (hu' i)
  · intro i hi
    apply le_trans _ (herr i)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hi (show 0≤(n : ℝ)*δ^2 by positivity)
    have hd := div_le_div_of_nonneg_right hh
      (show 0≤2*(Fintype.card (G i) : ℝ) by positivity)
    simpa only [neg_mul, neg_div] using neg_le_neg hd

end OAI.GaussianMoat.FinLaw

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- The actual finite-ball pushforward law of endpoint displacements. -/
noncomputable def ForwardKernel.displacementLaw (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (a : ℕ) :
    FinLaw (wordStepBall b e (D*K.bound)) :=
  (K.law a).map (K.displacementSymbol b e z hD hs a)

lemma ForwardKernel.displacementLaw_residue (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (a : ℕ) (i : BatchSignedIndex S) :
    let _ := batchResidueFintype data S hS i
    (K.displacementLaw b e z hD hs a).map
      (fun d => data.phi (signedBatchPrime S i.2) (i.1 i.2) d.val) =
      K.relativeResidueLaw data S hS z a i := by
  let _ := batchResidueFintype data S hS i
  dsimp only
  rw [displacementLaw, FinLaw.map_comp]
  rfl

/-- Additivity and the actual walk displacement telescope give the residue
law of composed kernels. -/
lemma ForwardKernel.then_relativeResidueLaw (K R : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (a : ℕ) (i : BatchSignedIndex S) :
    let _ := batchResidueFintype data S hS i
    (K.then R).relativeResidueLaw data S hS z a i =
      ((K.law a).joint (fun t => R.displacementLaw b e z hD hs (a+t.val))).map
        (fun v => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+v.1.val)-z a) +
          data.phi (signedBatchPrime S i.2) (i.1 i.2) v.2.val) := by
  let _ := batchResidueFintype data S hS i
  dsimp only
  unfold relativeResidueLaw ForwardKernel.then
  rw [FinLaw.map_comp, FinLaw.joint_observation_fun, FinLaw.joint_observation_fun]
  congr 1
  funext t
  rw [displacementLaw, FinLaw.map_comp]
  congr 1
  funext u
  change data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+(t.val+u.val))-z a) =
    data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+t.val)-z a) +
      data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+t.val+u.val)-z (a+t.val))
  rw [← map_add]
  congr 1
  rw [Nat.add_assoc]
  abel

/-- Genuine continuation samples are supported in the actual finite ball;
this derives the data entropy rather than assuming a certificate. -/
theorem continuation_data_entropy {Ω : Type*} [Fintype Ω]
    (p : FinLaw Ω) (a : Ω → ℕ) (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (n : ℕ) :
    (p.joint (fun ω => (K.displacementLaw b e z hD hs (a ω)).iid n)).Hf Prod.snd ≤
      (n : ℝ)*Real.log (wordStepBall b e (D*K.bound)).card := by
  have hh := (p.joint (fun ω => (K.displacementLaw b e z hD hs (a ω)).iid n)).Hf_le_log_card_type Prod.snd
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow,
    Real.log_pow] using hh

lemma ForwardKernel.coverage_data_deficit (K R : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (a n : ℕ)
    {m : ℕ} (hm : 0<m) (hmk : m≤S.card) {ε : ℝ}
    (hH : (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S (K.law a) (fun t => z (a+t.val)) m) :
    (𝔼 i : BatchSignedIndex S, (Real.log (signedBatchPrime S i.2)-
      ((K.law a).joint (fun t => (R.displacementLaw b e z hD hs (a+t.val)).iid n)).cHf
        (fun v => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+v.1.val)-z a)) Prod.snd)) ≤
      ε*batchMeanLog S + (n : ℝ)*Real.log (wordStepBall b e (D*R.bound)).card/m := by
  let q := fun t : Fin (K.bound+1) => (R.displacementLaw b e z hD hs (a+t.val)).iid n
  let P := (K.law a).joint q
  have he := signedPointEntropy_joint_fst data S (K.law a) q (fun t => z (a+t.val)) m
  have hH' : (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S P (fun v => z (a+v.1.val)) m := by
    rw [he]; exact hH
  exact signed_coverage_deficit data S hS P (fun v => z (a+v.1.val)) Prod.snd (z a)
    hm hmk hH' (continuation_data_entropy (K.law a) (fun t => a+t.val) R b e z hD hs n)

/-- Concrete backward amplification. Both the conditional-data deficit and
the future bad-prime bound are derived from actual point entropy and actual
finite-ball continuation laws. No coverage inequality is assumed. -/
theorem ForwardKernel.coverage_backward_of_entropy (K R : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1)))≤D)
    (a : ℕ) (u u' c : BatchSignedIndex S → ℝ)
    {τ δ err η εK εR cR v : ℝ} {n m mR : ℕ}
    (hn : 0<n) (hm : 0<m) (hmk : m≤S.card) (hmR : 0<mR) (hmRk : mR≤S.card)
    (hτ : 0≤τ) (hτnext : τ+4*δ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (herr0 : 0≤err) (hη : 0<η) (hcR : 0<cR) (hu : ∀ i, 0<u i)
    (hu'floor : ∀ i, 8*cR*(signedBatchPrime S i.2 : ℝ)≤u' i)
    (hK : (1-εK)*(m : ℝ)*batchMeanLog S≤
      signedPointEntropy data S (K.law a) (fun t => z (a+t.val)) m)
    (hR : ∀ t, (1-εR)*(mR : ℝ)*batchMeanLog S≤
      signedPointEntropy data S (R.law t) (fun j => z (t+j.val)) mR)
    (hsmall : εR*batchMeanLog S/cR+err≤η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : εK*batchMeanLog S+(n : ℝ)*
      Real.log (wordStepBall basis embedding (D*R.bound)).card/m<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (signedBatchPrime S i.2)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*δ^2*u i/(2*(signedBatchPrime S i.2 : ℝ)))≤err) :
    let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
    (FinLaw.uniform (BatchSignedIndex S)).prob (fun i =>
      u i≤((K.then R).passingException data S hS z a i τ).card)≤η := by
  let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
  let (i : BatchSignedIndex S) := batchResidueFintype data S hS i
  let (i : BatchSignedIndex S) : NeZero (signedBatchPrime S i.2) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i.2))).ne_zero⟩
  let w := FinLaw.uniform (BatchSignedIndex S)
  let q := fun t : Fin (K.bound+1) => R.displacementLaw basis embedding z hD hs (a+t.val)
  have hnxt : (∑ i, w i*(K.law a).prob (fun t => u' i≤
      (((q t).map (fun d => data.phi (signedBatchPrime S i.2) (i.1 i.2) d.val)).lowResidues
        (τ+4*δ)).card))≤εR*batchMeanLog S/cR := by
    simp only [q, displacementLaw_residue, FinLaw.prob, Finset.mul_sum]
    rw [Finset.sum_comm]
    have he : (∑ t, ∑ i, w i*(if u' i≤
        ((R.relativeResidueLaw data S hS z (a+t.val) i).lowResidues (τ+4*δ)).card
        then K.law a t else 0)) =
        ∑ t, K.law a t*w.prob (fun i => u' i≤
          ((R.relativeResidueLaw data S hS z (a+t.val) i).lowResidues (τ+4*δ)).card) := by
      unfold FinLaw.prob
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [he]
    have hnext (t : ℕ) : w.prob (fun i => u' i≤
        ((R.relativeResidueLaw data S hS z t i).lowResidues (τ+4*δ)).card)≤εR*batchMeanLog S/cR := by
      have hh := R.coverage_base data S hne hS z t hmR hmRk u' hτnext hcR hu'floor (hR t)
      simpa only [passingException_card] using hh
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
      mul_le_mul_of_nonneg_left (hnext (a+t.val)) ((K.law a).nonneg t))
    simpa only [← Finset.sum_mul, (K.law a).sum_one, one_mul] using hh
  have hd : (∑ i, w i*(Real.log (Fintype.card (ZMod (signedBatchPrime S i.2)))-
      ((K.law a).joint (fun t => (q t).iid n)).cHf
        (fun x => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+x.1.val)-z a)) Prod.snd))≤
      εK*batchMeanLog S+(n : ℝ)*Real.log (wordStepBall basis embedding (D*R.bound)).card/m := by
    rw [FinLaw.uniform_expect]
    simpa only [ZMod.card] using K.coverage_data_deficit R data S hS basis embedding z hD hs a n hm hmk hK
  have hh := FinLaw.lowResidues_backward (fun i : BatchSignedIndex S => ZMod (signedBatchPrime S i.2))
    w (K.law a) q
    (fun i t => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+t.val)-z a))
    (fun i d => data.phi (signedBatchPrime S i.2) (i.1 i.2) d.val)
    u u' c hn hτ (by linarith only [hτnext, hδ]) hδ hδ1 herr0 hη hu hnxt hsmall hscale hgap hd hc
    (by intro i; simpa only [ZMod.card] using hv i) hu'
    (by intro i; simpa only [ZMod.card] using herr i)
  have he (i : BatchSignedIndex S) := K.then_relativeResidueLaw R data S hS basis embedding z hD hs a i
  simp only [passingException_card]
  simpa only [he] using hh

/-- The backward amplification bound for the literal shared schedule. The
kernel decomposition follows from the proved schedule append law. -/
theorem commonSchedule_coverage_backward_of_entropy
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) (pre post : List ℕ) (N : ℕ)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1)))≤D)
    (a : ℕ) (u u' c : BatchSignedIndex S → ℝ)
    {τ δ err η εK εR cR v : ℝ} {n m mR : ℕ}
    (hn : 0<n) (hm : 0<m) (hmk : m≤S.card) (hmR : 0<mR) (hmRk : mR≤S.card)
    (hτ : 0≤τ) (hτnext : τ+4*δ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (herr0 : 0≤err) (hη : 0<η) (hcR : 0<cR) (hu : ∀ i, 0<u i)
    (hu'floor : ∀ i, 8*cR*(signedBatchPrime S i.2 : ℝ)≤u' i)
    (hK : (1-εK)*(m : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z pre 0).law a) (fun t => z (a+t.val)) m)
    (hR : ∀ t, (1-εR)*(mR : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z post N).law t) (fun j => z (t+j.val)) mR)
    (hsmall : εR*batchMeanLog S/cR+err≤η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : εK*batchMeanLog S+(n : ℝ)*
      Real.log (wordStepBall basis embedding (D*(post.sum+N))).card/m<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (signedBatchPrime S i.2)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*δ^2*u i/(2*(signedBatchPrime S i.2 : ℝ)))≤err) :
    let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
    (FinLaw.uniform (BatchSignedIndex S)).prob (fun i =>
      u i≤((commonSchedule z (pre++post) N).passingException data S hS z a i τ).card)≤η := by
  let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
  have hh := (commonSchedule z pre 0).coverage_backward_of_entropy (commonSchedule z post N)
    data S hne hS basis embedding z hD hs a u u' c hn hm hmk hmR hmRk
    hτ hτnext hδ hδ1 herr0 hη hcR hu hu'floor hK hR hsmall hscale
    (by simpa only [commonSchedule_bound, Nat.cast_add] using hgap) hc hv hu' herr
  simpa only [← commonSchedule_append] using hh

end Entry002
