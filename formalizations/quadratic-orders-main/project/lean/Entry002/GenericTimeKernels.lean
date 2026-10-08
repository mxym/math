import Entry002.GenericWalkTelescope
import Entry002.GenericWalkGeometry
import Entry002.GenericWalkExtraction
import Entry002.PosteriorCoverage

/-! Genuine finite walk-difference sampling and composed forward time kernels.
`walkDifferenceLaw` is the pushforward of the uniform law on the actual
difference set. `commonSchedule` composes its fair endpoint kernels and a
uniform terminal shift. No abstract entropy certificate replaces these laws.
Generic finite-law and kernel composition bodies are replayed from the pinned
OpenAI proof source; the walk definitions are generalized to additive lattices.
-/
set_option autoImplicit false
universe uOmega uAlpha uBeta uGamma

namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical
variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma joint_observation_fun (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    (p.joint q).map F = p.mix (fun ω => (q ω).map (fun a => F (ω,a))) := by
  exact joint_observation p q (fun ω a => F (ω,a))

lemma mix_comm (p : FinLaw Ω) (q : FinLaw α) (r : Ω → α → FinLaw β) :
    p.mix (fun ω => q.mix (r ω)) = q.mix (fun a => p.mix (fun ω => r ω a)) := by
  ext b
  simp only [mix_mass,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  ring

noncomputable def pure (ω : Ω) : FinLaw Ω where
  mass ν := if ν=ω then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  sum_one := by simp

lemma mix_pure (ω : Ω) (q : Ω → FinLaw α) : (pure ω).mix q=q ω := by
  ext a
  simp [mix_mass,pure]

lemma joint_pure_observation (ω : Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    ((pure ω).joint q).map F=(q ω).map (fun a => F (ω,a)) := by
  rw [joint_observation_fun,mix_pure]

end OAI.GaussianMoat.FinLaw

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

noncomputable def walkVertices (z : ℕ → L) (n : ℕ) : Finset L :=
  (Finset.range (n+1)).image z

omit [AddCommGroup L] in
@[simp] theorem mem_walkVertices (z : ℕ → L) (n : ℕ) (x : L) :
    x∈walkVertices z n ↔ ∃i≤n, z i=x := by
  simp [walkVertices,Finset.mem_image]

@[simp] theorem mem_latticeDifferences (E : Finset L) (x : L) :
    x∈latticeDifferences E ↔ ∃a∈E, ∃b∈E, a-b=x := by
  simp [latticeDifferences,Finset.mem_image,Prod.exists,and_assoc]

theorem walkDifference_exists_pair (z : ℕ → L) (n : ℕ)
    (d : latticeDifferences (walkVertices z n)) :
    ∃ij : Fin (n+1) × Fin (n+1), z ij.1.val-z ij.2.val=d := by
  obtain ⟨a,ha,b,hb,hab⟩ := (mem_latticeDifferences _ _).mp d.property
  obtain ⟨i,hi,rfl⟩ := (mem_walkVertices _ _ _).mp ha
  obtain ⟨j,hj,rfl⟩ := (mem_walkVertices _ _ _).mp hb
  exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hab⟩

noncomputable def walkDifferenceRepresentative (z : ℕ → L) (n : ℕ)
    (d : latticeDifferences (walkVertices z n)) : Fin (n+1) × Fin (n+1) :=
  (walkDifference_exists_pair z n d).choose

lemma walkDifferenceRepresentative_spec (z : ℕ → L) (n : ℕ)
    (d : latticeDifferences (walkVertices z n)) :
    z (walkDifferenceRepresentative z n d).1.val-
      z (walkDifferenceRepresentative z n d).2.val=d :=
  (walkDifference_exists_pair z n d).choose_spec

lemma walkDifferenceRepresentative_injective (z : ℕ → L) (n : ℕ) :
    Function.Injective (walkDifferenceRepresentative z n) := by
  intro d d' hh
  apply Subtype.ext
  rw [← walkDifferenceRepresentative_spec z n d,
    ← walkDifferenceRepresentative_spec z n d',hh]

lemma walkDifferences_nonempty (z : ℕ → L) (n : ℕ) :
    (latticeDifferences (walkVertices z n)).Nonempty := by
  refine ⟨0,(mem_latticeDifferences _ _).mpr
    ⟨z 0,?_,z 0,?_,sub_self _⟩⟩ <;>
    exact (mem_walkVertices _ _ _).mpr ⟨0,by omega,rfl⟩

noncomputable def walkDifferenceLaw (z : ℕ → L) (n : ℕ) :
    FinLaw (Fin (n+1) × Fin (n+1)) := by
  let := (walkDifferences_nonempty z n).to_subtype
  exact (FinLaw.uniform (latticeDifferences (walkVertices z n))).map
    (walkDifferenceRepresentative z n)

theorem walkDifferenceLaw_displacement_entropy (z : ℕ → L) (n : ℕ) :
    (walkDifferenceLaw z n).Hf (fun ij => z ij.1.val-z ij.2.val)=
      Real.log (latticeDifferences (walkVertices z n)).card := by
  let := (walkDifferences_nonempty z n).to_subtype
  unfold walkDifferenceLaw
  rw [FinLaw.Hf_map]
  have he : (fun d : latticeDifferences (walkVertices z n) =>
      z (walkDifferenceRepresentative z n d).1.val-
        z (walkDifferenceRepresentative z n d).2.val)=Subtype.val := by
    funext d
    exact walkDifferenceRepresentative_spec z n d
  change (FinLaw.uniform (latticeDifferences (walkVertices z n))).Hf
    (fun d => z (walkDifferenceRepresentative z n d).1.val-
      z (walkDifferenceRepresentative z n d).2.val)=_
  rw [he]
  simpa only [Fintype.card_coe] using
    (FinLaw.uniform_Hf_injective (Ω := latticeDifferences (walkVertices z n))
      Subtype.val Subtype.val_injective)

structure TimeLaw where
  last : ℕ
  law : FinLaw (Fin (last+1))

structure ForwardKernel where
  bound : ℕ
  law : ℕ → FinLaw (Fin (bound+1))

noncomputable def addOffsets (n m : ℕ) : Fin (n+1) × Fin (m+1) → Fin (n+m+1) :=
  fun v => ⟨v.1.val+v.2.val,by omega⟩

noncomputable def ForwardKernel.then (K R : ForwardKernel) : ForwardKernel where
  bound := K.bound+R.bound
  law := fun a => ((K.law a).joint (fun i => R.law (a+i.val))).map
    (addOffsets K.bound R.bound)

noncomputable def differenceKernel (z : ℕ → L) (n : ℕ) : ForwardKernel where
  bound := n
  law := fun a => ((FinLaw.uniform Bool).joint (fun _ =>
    walkDifferenceLaw (fun t => z (a+t)) n)).map
      (fun v => if v.1 then v.2.1 else v.2.2)

noncomputable def smoothingKernel (n : ℕ) : ForwardKernel where
  bound := n
  law := fun _ => FinLaw.uniform (Fin (n+1))

noncomputable def commonSchedule (z : ℕ → L) (ns : List ℕ) (N : ℕ) : ForwardKernel :=
  ns.foldr (fun n K => (differenceKernel z n).then K) (smoothingKernel N)

@[simp] lemma commonSchedule_bound (z : ℕ → L) (ns : List ℕ) (N : ℕ) :
    (commonSchedule z ns N).bound=ns.sum+N := by
  induction ns with
  | nil => simp [commonSchedule,smoothingKernel]
  | cons n ns ih =>
    change n+(commonSchedule z ns N).bound=_
    rw [ih,List.sum_cons,Nat.add_assoc]

@[simp] lemma commonSchedule_cons (z : ℕ → L) (n : ℕ) (ns : List ℕ) (N : ℕ) :
    commonSchedule z (n::ns) N=(differenceKernel z n).then (commonSchedule z ns N) := rfl

noncomputable def TimeLaw.advance (P : TimeLaw) (K : ForwardKernel) : TimeLaw where
  last := P.last+K.bound
  law := (P.law.joint (fun a => K.law a.val)).map (addOffsets P.last K.bound)

-- Generic kernel composition bodies are appended from the pinned source.


noncomputable def TimeLaw.at (a : ℕ) : TimeLaw where
  last := a
  law := FinLaw.pure ⟨a,by omega⟩

lemma TimeLaw.at_advance (a : ℕ) (K : ForwardKernel) :
    ((TimeLaw.at a).advance K).law=
      (K.law a).map (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1))) := by
  change ((FinLaw.pure (⟨a,by omega⟩ : Fin (a+1))).joint
    (fun t => K.law t.val)).map (addOffsets a K.bound)=_
  rw [FinLaw.joint_pure_observation]
  rfl


noncomputable def TimeLaw.observe {α : Type uAlpha} [Fintype α] (P : TimeLaw) (f : ℕ → α) : FinLaw α :=
  P.law.map (fun t => f t.val)

lemma TimeLaw.ext_observe (P Q : TimeLaw) (hl : P.last=Q.last)
    (h : ∀ {α : Type} [Fintype α] (f : ℕ → α), P.observe f=Q.observe f) : P=Q := by
  cases P with | mk n p =>
  cases Q with | mk m q =>
  dsimp only at hl
  subst m
  congr 1
  let f : ℕ → Fin (n+1) := fun t => ⟨min t n,by omega⟩
  have hh := h f
  have he : (fun t : Fin (n+1) => f t.val)=id := by
    funext t
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  unfold observe at hh
  simpa only [he,FinLaw.map_id] using hh

lemma TimeLaw.observe_advance {α : Type uAlpha} [Fintype α]
    (P : TimeLaw) (K : ForwardKernel) (f : ℕ → α) :
    (P.advance K).observe f=P.law.mix (fun a => (K.law a.val).map (fun t => f (a.val+t.val))) := by
  unfold observe advance
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rfl

lemma ForwardKernel.then_observe {α : Type uAlpha} [Fintype α]
    (K R : ForwardKernel) (a : ℕ) (f : ℕ → α) :
    ((K.then R).law a).map (fun t => f (a+t.val))=
      (K.law a).mix (fun t => (R.law (a+t.val)).map (fun u => f (a+t.val+u.val))) := by
  unfold ForwardKernel.then
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  congr 1
  funext t
  congr 1
  funext u
  simp only [Function.comp_def,addOffsets,Nat.add_assoc]

lemma TimeLaw.advance_then (P : TimeLaw) (K R : ForwardKernel) :
    P.advance (K.then R)=(P.advance K).advance R := by
  apply TimeLaw.ext_observe
  · exact (Nat.add_assoc _ _ _).symm
  · intro α _ f
    rw [TimeLaw.observe_advance,TimeLaw.observe_advance]
    change P.law.mix _ = (((P.law.joint (fun a => K.law a.val)).map
      (addOffsets P.last K.bound))).mix (fun a : Fin (P.last+K.bound+1) =>
        (R.law a.val).map (fun t => f (a.val+t.val)))
    rw [FinLaw.mix_map_left]
    have hj := FinLaw.joint_observation (P.law) (fun a => K.law a.val)
      (fun a t => (a,t))
    clear hj
    have hmix : ((P.law.joint (fun a => K.law a.val))).mix
        (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val))) =
      P.law.mix (fun a => (K.law a.val).mix
        (fun t => (R.law (a.val+t.val)).map (fun u => f (a.val+t.val+u.val)))) := by
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    change P.law.mix _ = (P.law.joint (fun a => K.law a.val)).mix
      (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val)))
    rw [hmix]
    congr 1
    funext a
    exact K.then_observe R a.val f


lemma ForwardKernel.ext_observe (K R : ForwardKernel) (hb : K.bound=R.bound)
    (h : ∀ (a : ℕ) {α : Type} [Fintype α] (f : ℕ → α),
      (K.law a).map (fun t => f (a+t.val))=(R.law a).map (fun t => f (a+t.val))) : K=R := by
  cases K with | mk n p =>
  cases R with | mk m q =>
  dsimp only at hb
  subst m
  congr 1
  funext a
  let f : ℕ → Fin (n+1) := fun t => ⟨min (t-a) n,by omega⟩
  have hh := h a f
  have he : (fun t : Fin (n+1) => f (a+t.val))=id := by
    funext t
    apply Fin.ext
    dsimp only [f,id_eq]
    omega
  simpa only [he,FinLaw.map_id] using hh

lemma ForwardKernel.then_assoc (K R S : ForwardKernel) :
    (K.then R).then S=K.then (R.then S) := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_assoc _ _ _
  · intro a α _ f
    rw [ForwardKernel.then_observe,ForwardKernel.then_observe]
    have hl : ((K.then R).law a).mix
        (fun t => (S.law (a+t.val)).map (fun u => f (a+t.val+u.val))) =
        (K.law a).mix (fun t => (R.law (a+t.val)).mix
          (fun u => (S.law (a+t.val+u.val)).map (fun v => f (a+t.val+u.val+v.val)))) := by
      unfold ForwardKernel.then
      rw [FinLaw.mix_map_left]
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,
        addOffsets,Nat.add_assoc,mul_assoc]
    rw [hl]
    congr 1
    funext t
    exact (R.then_observe S (a+t.val) f).symm


lemma FinLaw.map_pure {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (ω : Ω) (f : Ω → α) : (FinLaw.pure ω).map f=FinLaw.pure (f ω) := by
  ext a
  simp only [FinLaw.map_mass,FinLaw.pure]
  rw [Finset.sum_eq_single ω]
  · simp only [ite_true,eq_comm]
  · intro ν _ hν
    simp [hν]
  · simp

lemma FinLaw.mix_pure_right {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (p : FinLaw Ω) (f : Ω → α) : p.mix (fun ω => FinLaw.pure (f ω))=p.map f := by
  ext a
  simp only [FinLaw.mix_mass,FinLaw.pure,FinLaw.map_mass,mul_ite,mul_one,mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [eq_comm]

lemma smoothingKernel_zero_law (a : ℕ) :
    (smoothingKernel 0).law a=FinLaw.pure (0 : Fin 1) := by
  change FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1)
  ext x
  have hx : x=0 := Subsingleton.elim _ _
  simp [FinLaw.uniform,FinLaw.pure,hx]

lemma ForwardKernel.then_zero (K : ForwardKernel) : K.then (smoothingKernel 0)=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_zero _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (K.law a).mix (fun t => (FinLaw.uniform (Fin 1)).map
      (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    simp only [hu,FinLaw.map_pure,Fin.val_zero,Nat.add_zero]
    exact FinLaw.mix_pure_right _ _

lemma ForwardKernel.zero_then (K : ForwardKernel) : (smoothingKernel 0).then K=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.zero_add _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (FinLaw.uniform (Fin 1)).mix
      (fun t => (K.law (a+t.val)).map (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    rw [hu,FinLaw.mix_pure]
    rfl


lemma commonSchedule_append (z : ℕ → L) (ns ms : List ℕ) (N : ℕ) :
    commonSchedule z (ns++ms) N=(commonSchedule z ns 0).then (commonSchedule z ms N) := by
  induction ns with
  | nil => exact (ForwardKernel.zero_then _).symm
  | cons n ns ih =>
    rw [List.cons_append,commonSchedule_cons,commonSchedule_cons,ih,ForwardKernel.then_assoc]


noncomputable def TimeLaw.info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) : ℝ :=
  P.law.cIf (fun t => X t.val) (fun t => Y t.val) (fun t => O t.val)

lemma TimeLaw.advance_info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw) (K : ForwardKernel)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) :
    (P.advance K).info X Y O=(P.law.joint (fun a => K.law a.val)).cIf
      (fun v => X (v.1.val+v.2.val)) (fun v => Y (v.1.val+v.2.val))
      (fun v => O (v.1.val+v.2.val)) := by
  unfold TimeLaw.info TimeLaw.advance
  rw [FinLaw.cIf_map]
  rfl

lemma commonSchedule_smooth (z : ℕ → L) (ns : List ℕ) (N : ℕ) :
    commonSchedule z ns N=(commonSchedule z ns 0).then (smoothingKernel N) := by
  simpa only [List.append_nil,commonSchedule,List.foldr_nil] using commonSchedule_append z ns [] N

/-- The actual enrichment step is fair endpoint sampling of the genuine
uniform finite difference law. -/
noncomputable def TimeLaw.step (P : TimeLaw) (z : ℕ → L) (n : ℕ) : TimeLaw :=
  P.advance (differenceKernel z n)

lemma TimeLaw.advance_difference (P : TimeLaw) (z : ℕ → L) (n : ℕ) :
    P.advance (differenceKernel z n)=P.step z n := rfl

lemma walk_pair_displacement (b : Module.Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (a n i j : ℕ) (hi : i≤n) (hj : j≤n) :
    ‖planarEmbedding b e (z (a+i)-z (a+j))‖≤D*n := by
  have h := bounded_walk_pair_distance b e (fun t => z (a+t)) hi hj hD
    (fun t _ => by simpa only [Nat.add_assoc] using hs (a+t))
  simpa only [planarEmbedding_sub_signed,dist_eq_norm] using h

/-- Displacement entropy is bounded by the cardinality of the actual planar
lattice ball containing every displacement. -/
theorem displacement_entropy_le_stepBall {Ω : Type*} [Fintype Ω]
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (p : FinLaw Ω) (Z : Ω → L) (R : ℝ) (hZ : ∀ω, ‖planarEmbedding b e (Z ω)‖≤R) :
    p.Hf Z≤Real.log (wordStepBall b e R).card := by
  let Y : Ω → wordStepBall b e R := fun ω => ⟨Z ω,(mem_wordStepBall b e R _).mpr (hZ ω)⟩
  have he : p.Hf Z=p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    change (Y ω).val=(Y ν).val ↔ Y ω=Y ν
    exact Subtype.val_injective.eq_iff
  rw [he]
  simpa only [Fintype.card_coe] using p.Hf_le_log_card_type Y

theorem ForwardKernel.displacement_entropy (K : ForwardKernel) (a : ℕ)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) :
    (K.law a).Hf (fun i => z (a+i.val)-z a)≤
      Real.log (wordStepBall b e (D*K.bound)).card := by
  apply displacement_entropy_le_stepBall
  intro i
  simpa only [Nat.add_zero] using walk_pair_displacement b e z hD hs a K.bound
    i.val 0 (by omega) (by omega)

theorem TimeLaw.advance_displacement_entropy (P : TimeLaw) (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) :
    (P.law.joint (fun a => K.law a.val)).Hf
      (fun v => z (v.1.val+v.2.val)-z v.1.val)≤
        Real.log (wordStepBall b e (D*K.bound)).card := by
  apply displacement_entropy_le_stepBall
  intro v
  simpa only [Nat.add_zero] using walk_pair_displacement b e z hD hs v.1.val K.bound
    v.2.val 0 (by omega) (by omega)

/-- The telescope on the actual composed forward schedule, with a terminal
uniform shift. Semigroup identities prove that this is the same common law
at every batch. -/
theorem schedule_lattice_information_telescope
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (ns : List ℕ) (N n : ℕ)
    (F : ℕ → Finset (ℕ × Bool)) (hF : ∀j i, i∈F j → i.1∈data.primes)
    (hnest : ∀j, F j⊆F (j+1)) (len : ℕ → ℕ)
    (hL : ∀j≤n, 0<len j) (hdiv : ∀j<n, len j∣len (j+1))
    (hN : ∀j<n, len (j+1)≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀j<n, ∀a<len (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1))+
        ((a:ℝ)/(N+1))*((len j:ℝ)*Real.log (wordStepBall b e D).card+
          2*(F (j+1)).sum (fun i => Real.log i.1))≤ε) :
    let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
    (∑j∈Finset.range (n+1), P.info
      (fun a => residueFamilyHom data (F (j+1)) (z a)) (incrementWord z (len j))
      (fun a => residueFamilyHom data (F j) (z a))/len j)≤
        Real.log (wordStepBall b e D).card+n*ε := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z ns 0)
  have h := lattice_residue_information_telescope b e data Q.law (fun t => t.val)
    z D hs F hF hnest len n N hL hdiv hN hε herr
  dsimp only
  rw [commonSchedule_smooth,TimeLaw.advance_then]
  simp only [TimeLaw.advance_info]
  exact h

/-- The actual forward schedule admits a proved common-law information bound
with any requested positive per-scale error; no numerical error certificate
or entropy-rate inequality is assumed. -/
theorem exists_schedule_lattice_information_telescope
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D) (ns : List ℕ) (n : ℕ)
    (F : ℕ → Finset (ℕ × Bool)) (hF : ∀j i, i∈F j → i.1∈data.primes)
    (hnest : ∀j, F j⊆F (j+1)) (len : ℕ → ℕ)
    (hL : ∀j≤n, 0<len j) (hdiv : ∀j<n, len j∣len (j+1))
    {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,
    let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
    (∑j∈Finset.range (n+1), P.info
      (fun a => residueFamilyHom data (F (j+1)) (z a)) (incrementWord z (len j))
      (fun a => residueFamilyHom data (F j) (z a))/len j)≤
        Real.log (wordStepBall b e D).card+n*ε := by
  obtain ⟨N,hN,herr⟩ := exists_common_block_smoothing_size len n
    (fun j => (F j).sum (fun i => Real.log i.1))
    (Real.log (wordStepBall b e D).card) hε
  exact ⟨N,schedule_lattice_information_telescope b e data z D hs ns N n F hF hnest
    len hL hdiv hN hε.le herr⟩

end Entry002
