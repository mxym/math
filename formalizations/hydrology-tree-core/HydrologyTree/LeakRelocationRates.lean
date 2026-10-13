import HydrologyTree.GraphRateTransport

/-! Exact rational relocation of a single leak across one oriented graph edge.
The positive-rate transformation is invertible; it changes only the two rates
on that edge and the leak. Matrix/response preservation is proved separately. -/
noncomputable section
namespace HydrologyTree

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

@[simp] lemma leakDart_symm_fst (d : G.Dart) : d.symm.fst=d.snd := rfl
@[simp] lemma leakDart_symm_snd (d : G.Dart) : d.symm.snd=d.fst := rfl

/-- d points FROM the old leak vertex TO the new leak vertex. -/
def slideLeakRates (d : G.Dart) (y : GraphRates G) : GraphRates G :=
  (y.2 d.symm*y.1/(y.2 d+y.1),
    fun e => if e=d then y.2 d+y.1
      else if e=d.symm then y.2 d.symm*y.2 d/(y.2 d+y.1) else y.2 e)

@[simp] lemma slideLeak_leak (d : G.Dart) (y : GraphRates G) :
    (slideLeakRates d y).1=y.2 d.symm*y.1/(y.2 d+y.1) := rfl

@[simp] lemma slideLeak_forward (d : G.Dart) (y : GraphRates G) :
    (slideLeakRates d y).2 d=y.2 d+y.1 := by simp [slideLeakRates]

@[simp] lemma slideLeak_reverse (d : G.Dart) (y : GraphRates G) :
    (slideLeakRates d y).2 d.symm=y.2 d.symm*y.2 d/(y.2 d+y.1) := by
  simp [slideLeakRates,d.symm_ne]

lemma slideLeak_other (d e : G.Dart) (y : GraphRates G) (h1 : e ≠ d) (h2 : e ≠ d.symm) :
    (slideLeakRates d y).2 e=y.2 e := by simp [slideLeakRates,h1,h2]

/-- Strict positivity is retained in all original directed graph coordinates. -/
theorem slideLeakRates_positive (d : G.Dart) (y : GraphRates G) (hy : PositiveGraphRates y) :
    PositiveGraphRates (slideLeakRates d y) := by
  have ht : 0<y.2 d+y.1 := add_pos (hy.2 d) hy.1
  refine ⟨div_pos (mul_pos (hy.2 d.symm) hy.1) ht,?_⟩
  intro e
  by_cases h : e=d
  · subst e
    simpa only [slideLeak_forward] using ht
  · by_cases hr : e=d.symm
    · subst e
      rw [slideLeak_reverse]
      exact div_pos (mul_pos (hy.2 d.symm) (hy.2 d)) ht
    · rw [slideLeak_other d e y h hr]
      exact hy.2 e

lemma slideLeak_reverse_plus_leak (d : G.Dart) (y : GraphRates G) (ht : y.2 d+y.1 ≠ 0) :
    (slideLeakRates d y).2 d.symm+(slideLeakRates d y).1=y.2 d.symm := by
  rw [slideLeak_reverse,slideLeak_leak]
  field_simp
  <;> ring

/-- Exact inverse, even beyond positivity wherever the specified denominators
are nonzero. The opposite directed edge moves the leak back. -/
theorem slideLeakRates_reverse (d : G.Dart) (y : GraphRates G)
    (ht : y.2 d+y.1 ≠ 0) (ha : y.2 d.symm ≠ 0) :
    slideLeakRates d.symm (slideLeakRates d y)=y := by
  apply Prod.ext
  · rw [slideLeak_leak,SimpleGraph.Dart.symm_symm,slideLeak_forward,
      slideLeak_reverse_plus_leak d y ht,slideLeak_leak]
    field_simp
  · funext e
    by_cases he : e=d
    · subst e
      have h := slideLeak_reverse d.symm (slideLeakRates d y)
      simp only [SimpleGraph.Dart.symm_symm] at h
      rw [h,slideLeak_reverse_plus_leak d y ht,slideLeak_forward,slideLeak_reverse]
      field_simp
    · by_cases hr : e=d.symm
      · subst e
        rw [slideLeak_forward,slideLeak_reverse_plus_leak d y ht]
      · rw [slideLeak_other d.symm e (slideLeakRates d y) hr (by simpa using he),
          slideLeak_other d e y he hr]

abbrev PositiveGraphRateSpace (G : SimpleGraph V) := {y : GraphRates G // PositiveGraphRates y}

/-- Bijection of entire positive rate spaces for the two choices of leak site.
No spectral, uniqueness or cardinality input is needed for this algebraic map. -/
def slidePositiveLeakEquiv (d : G.Dart) : PositiveGraphRateSpace G ≃ PositiveGraphRateSpace G where
  toFun y := ⟨slideLeakRates d y.val,slideLeakRates_positive d y.val y.property⟩
  invFun y := ⟨slideLeakRates d.symm y.val,slideLeakRates_positive d.symm y.val y.property⟩
  left_inv y := by
    apply Subtype.ext
    exact slideLeakRates_reverse d y.val (ne_of_gt (add_pos (y.property.2 d) y.property.1))
      (ne_of_gt (y.property.2 d.symm))
  right_inv y := by
    apply Subtype.ext
    simpa only [SimpleGraph.Dart.symm_symm] using
      slideLeakRates_reverse d.symm y.val (ne_of_gt (add_pos (y.property.2 d.symm) y.property.1))
        (ne_of_gt (y.property.2 d.symm.symm))

end HydrologyTree
