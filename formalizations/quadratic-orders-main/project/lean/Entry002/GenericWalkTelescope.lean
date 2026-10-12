import Entry002.GenericWords
import Entry002.GenericResidues
import Entry002.GenericSignedArithmetic
import Entry002.GenericNumericalSchedule

/-! Common-law information telescope for actual lattice walks and actual
prime-field observations.  The block comparison and uniform shift comparison
are proved in `GenericWords`; only the explicitly displayed numerical
smoothing budget is an input.  No entropy-rate hypothesis is assumed. -/

set_option autoImplicit false
open Module
open OAI.GaussianMoat
open scoped BigOperators
namespace Entry002

variable {L : Type*} [AddCommGroup L]

theorem commonLawWalkInformationTelescope {Ω : Type*} [Fintype Ω]
    {R : ℕ → Type*} [∀ j, AddCommGroup (R j)] [∀ j, Fintype (R j)]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → L) (A : Finset L)
    (hs : ∀ t, z (t+1)-z t ∈ A) (ρ : (j : ℕ) → L →+ R j)
    (hrefine : ∀ j x y, ρ (j+1) x=ρ (j+1) y → ρ j x=ρ j y)
    (len : ℕ → ℕ) (n N : ℕ) (hL : ∀ j≤n, 0<len j)
    (hdiv : ∀ j<n, len j∣len (j+1)) (hN : ∀ j<n, len (j+1)≤N)
    {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<len (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1))+
        ((a:ℝ)/(N+1))*((len j:ℝ)*Real.log A.card+
          2*Real.log (Fintype.card (R (j+1))))≤ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v => ρ (j+1) (z (u v)))
        (fun v => incrementWord z (len j) (u v))
        (fun v => ρ j (z (u v)))/len j)≤Real.log A.card+n*ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  apply commonLawInformationTelescope P
    (fun j v => incrementWord z (len j) (u v))
    (fun j v => ρ j (z (u v))) len n hL
  · intro j v w h
    exact hrefine j _ _ h
  · intro j hj
    exact word_entropy_rate_monotone p t z A hs (ρ (j+1))
      (hL j (by omega)) (hL (j+1) (by omega)) (hdiv j hj) (hN j hj) hε
      (herr j hj)
  · exact boundedWord_entropy_le P u z A hs (len 0)

/-- The literal finite alphabet of all possible increments of a `D`-step walk
in the given full planar lattice. -/
noncomputable def wordStepBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) : Finset L :=
  (planarEmbedding_finite_balls b e D).toFinset

@[simp] theorem mem_wordStepBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) (x : L) :
    x∈wordStepBall b e D ↔ ‖planarEmbedding b e x‖≤D := by
  classical
  simp [wordStepBall]

theorem bounded_steps_in_wordStepBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) (D : ℝ)
    (hz : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) :
    ∀ t, z (t+1)-z t∈wordStepBall b e D := by
  intro t
  rw [mem_wordStepBall,planarEmbedding_sub_signed,norm_sub_rev]
  simpa only [dist_eq_norm] using hz t

/-- The common-law telescope specialized to the actual finite prime residue
families used by the manuscript. Every alphabet and its exact logarithmic
budget are constructed from actual primality, and nested families refine by
the proved coordinate restriction map. -/
theorem lattice_residue_information_telescope {Ω : Type*} [Fintype Ω]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (p : FinLaw Ω) (t : Ω → ℕ)
    (z : ℕ → L) (D : ℝ)
    (hz : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D)
    (F : ℕ → Finset (ℕ × Bool)) (hF : ∀ j i, i∈F j → i.1∈data.primes)
    (hnest : ∀ j, F j⊆F (j+1)) (len : ℕ → ℕ) (n N : ℕ)
    (hL : ∀ j≤n, 0<len j) (hdiv : ∀ j<n, len j∣len (j+1))
    (hN : ∀ j<n, len (j+1)≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<len (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1))+
        ((a:ℝ)/(N+1))*((len j:ℝ)*Real.log (wordStepBall b e D).card+
          2*(F (j+1)).sum (fun i => Real.log i.1))≤ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v => residueFamilyHom data (F (j+1)) (z (u v)))
        (fun v => incrementWord z (len j) (u v))
        (fun v => residueFamilyHom data (F j) (z (u v)))/len j)≤
      Real.log (wordStepBall b e D).card+n*ε := by
  let (j : ℕ) : Fintype (ResidueFamily (F j)) := residueFamilyFintype data (F j) (hF j)
  apply commonLawWalkInformationTelescope p t z (wordStepBall b e D)
    (bounded_steps_in_wordStepBall b e z D hz) (fun j => residueFamilyHom data (F j))
    (fun j _ _ h => residueFamily_refines data (F j) (F (j+1)) (hnest j) h)
    len n N hL hdiv hN hε
  intro j hj a ha
  have hc : Real.log (Fintype.card (ResidueFamily (F (j+1))))=
      (F (j+1)).sum (fun i => Real.log i.1) := by
    rw [← Nat.card_eq_fintype_card,residueFamily_logCard data _ (hF (j+1))]
  rw [hc]
  exact herr j hj a ha

/-- End-to-end common-law telescope with the numerical smoothing budget proved
by choosing one actual natural terminal shift size. All observations are the
actual prime residue maps, all words come from the actual bounded-step walk.
The remaining inputs are just primality, nested labels, positive divisible
block lengths, and a positive requested error. -/
theorem exists_lattice_residue_information_telescope {Ω : Type*} [Fintype Ω]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (p : FinLaw Ω) (t : Ω → ℕ)
    (z : ℕ → L) (D : ℝ)
    (hz : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D)
    (F : ℕ → Finset (ℕ × Bool)) (hF : ∀ j i, i∈F j → i.1∈data.primes)
    (hnest : ∀ j, F j⊆F (j+1)) (len : ℕ → ℕ) (n : ℕ)
    (hL : ∀ j≤n, 0<len j) (hdiv : ∀ j<n, len j∣len (j+1))
    {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v => residueFamilyHom data (F (j+1)) (z (u v)))
        (fun v => incrementWord z (len j) (u v))
        (fun v => residueFamilyHom data (F j) (z (u v)))/len j)≤
      Real.log (wordStepBall b e D).card+n*ε := by
  obtain ⟨N,hN,herr⟩ := exists_common_block_smoothing_size len n
    (fun j => (F j).sum (fun i => Real.log i.1))
    (Real.log (wordStepBall b e D).card) hε
  exact ⟨N,lattice_residue_information_telescope b e data p t z D hz F hF hnest
    len n N hL hdiv hN hε.le herr⟩

end Entry002
