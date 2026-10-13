import HydrologyTree.PhysicalBridge

/-! Canonical root-branch partition of the original parent-encoded finite tree.
This is combinatorial data independent of every rate parameter. -/
noncomputable section
namespace HydrologyTree

/-- The unique first vertex after root 0 on the parent path of v; root maps to 0. -/
def rootBranchVertex {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) : Fin (n+1) :=
  if hv : v = 0 then 0
  else if parentVertex t v = 0 then v
  else rootBranchVertex t (parentVertex t v)
termination_by v.val
decreasing_by exact parentVertex_lt t v hv

@[simp] lemma rootBranchVertex_zero {n : ℕ} (t : OrderedTree n) :
    rootBranchVertex t 0 = 0 := by rw [rootBranchVertex]; simp

lemma rootBranchVertex_child {n : ℕ} (t : OrderedTree n) (v : Fin (n+1))
    (hv : v ≠ 0) (hp : parentVertex t v = 0) : rootBranchVertex t v = v := by
  rw [rootBranchVertex]
  simp [hv,hp]

lemma rootBranchVertex_step {n : ℕ} (t : OrderedTree n) (v : Fin (n+1))
    (hv : v ≠ 0) (hp : parentVertex t v ≠ 0) :
    rootBranchVertex t v = rootBranchVertex t (parentVertex t v) := by
  rw [rootBranchVertex]
  simp [hv,hp]

/-- A nonroot vertex belongs to a nonroot branch. -/
theorem rootBranchVertex_ne_zero {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) (hv : v ≠ 0) :
    rootBranchVertex t v ≠ 0 := by
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hp : parentVertex t v = 0
    · rwa [rootBranchVertex_child t v hv hp]
    · rw [rootBranchVertex_step t v hv hp]
      exact ih (parentVertex t v) (parentVertex_lt t v hv) hp

/-- The branch representative is always a direct child of the root. -/
theorem rootBranchVertex_parent_zero {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) (hv : v ≠ 0) :
    parentVertex t (rootBranchVertex t v) = 0 := by
  induction v using (measure Fin.val).wf.induction with
  | h v ih =>
    by_cases hp : parentVertex t v = 0
    · rwa [rootBranchVertex_child t v hv hp]
    · rw [rootBranchVertex_step t v hv hp]
      exact ih (parentVertex t v) (parentVertex_lt t v hv) hp

abbrev RootChild {n : ℕ} (t : OrderedTree n) :=
  {v : Fin (n+1) // v ≠ 0 ∧ parentVertex t v = 0}

abbrev BranchVertex {n : ℕ} (t : OrderedTree n) (c : RootChild t) :=
  {v : Fin (n+1) // rootBranchVertex t v = c.val}

lemma branchVertex_ne_zero {n : ℕ} (t : OrderedTree n) (c : RootChild t) (v : BranchVertex t c) :
    v.val ≠ 0 := by
  intro hv
  have hh := v.property
  rw [hv, rootBranchVertex_zero] at hh
  exact c.property.1 hh.symm

def branchRootVertex {n : ℕ} (t : OrderedTree n) (c : RootChild t) : BranchVertex t c :=
  ⟨c.val, rootBranchVertex_child t c.val c.property.1 c.property.2⟩

def rootPartitionMap {n : ℕ} (t : OrderedTree n) :
    Unit ⊕ (Σ c : RootChild t, BranchVertex t c) → Fin (n+1)
  | .inl _ => 0
  | .inr v => v.2.val

lemma rootPartitionMap_injective {n : ℕ} (t : OrderedTree n) :
    Function.Injective (rootPartitionMap t) := by
  intro u v h
  rcases u with u | ⟨c,u⟩ <;> rcases v with v | ⟨d,v⟩
  · cases u; cases v; rfl
  · exact False.elim (branchVertex_ne_zero t d v h.symm)
  · exact False.elim (branchVertex_ne_zero t c u h)
  · have hc : c = d := by
      apply Subtype.ext
      exact u.property.symm.trans ((congrArg (rootBranchVertex t) h).trans v.property)
    subst d
    have huv : u = v := Subtype.ext h
    subst v
    rfl

lemma rootPartitionMap_surjective {n : ℕ} (t : OrderedTree n) :
    Function.Surjective (rootPartitionMap t) := by
  intro v
  by_cases hv : v = 0
  · exact ⟨.inl (), hv.symm⟩
  · let c : RootChild t := ⟨rootBranchVertex t v,
      rootBranchVertex_ne_zero t v hv, rootBranchVertex_parent_zero t v hv⟩
    exact ⟨.inr ⟨c,⟨v,rfl⟩⟩,rfl⟩

/-- Exact rate-independent reindexing of all vertices into root and child branches. -/
def rootPartitionEquiv {n : ℕ} (t : OrderedTree n) :
    Unit ⊕ (Σ c : RootChild t, BranchVertex t c) ≃ Fin (n+1) :=
  Equiv.ofBijective (rootPartitionMap t) ⟨rootPartitionMap_injective t,rootPartitionMap_surjective t⟩

@[simp] lemma rootPartitionEquiv_root {n : ℕ} (t : OrderedTree n) :
    rootPartitionEquiv t (.inl ()) = 0 := rfl

@[simp] lemma rootPartitionEquiv_branch {n : ℕ} (t : OrderedTree n)
    (c : RootChild t) (v : BranchVertex t c) :
    rootPartitionEquiv t (.inr ⟨c,v⟩) = v.val := rfl

end HydrologyTree
