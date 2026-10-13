import HydrologyTree.GraphRateTransport
import HydrologyTree.RootBranches

/-! The single-edge cut used for leak relocation is constructed from the
actual independent tree, not an additional separation premise. -/
noncomputable section
namespace HydrologyTree
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure GraphLeakCut (d : G.Dart) where
  side : V → Bool
  source : side d.fst=false
  target : side d.snd=true
  same_side : ∀ e : G.Dart, e ≠ d → e ≠ d.symm → side e.fst=side e.snd

lemma orderedGraph_root_adj {n : ℕ} (t : OrderedTree n) (v : Fin (n+1))
    (h : (orderedTreeGraph t).Adj 0 v) : v ≠ 0 ∧ parentVertex t v=0 := by
  obtain ⟨e,⟨hp,hv⟩ | ⟨hp,hv⟩⟩ := h
  · subst v
    exact ⟨Fin.succ_ne_zero e,hp.symm⟩
  · exact False.elim (Fin.succ_ne_zero e hv.symm)

lemma orderedGraph_nonroot_same_branch {n : ℕ} (t : OrderedTree n)
    (u v : Fin (n+1)) (hu : u ≠ 0) (hv : v ≠ 0) (h : (orderedTreeGraph t).Adj u v) :
    rootBranchVertex t u=rootBranchVertex t v := by
  obtain ⟨e,⟨hp,hc⟩ | ⟨hp,hc⟩⟩ := h
  · have hpn : t.parent e ≠ 0 := by simpa only [← hp] using hu
    have he : rootBranchVertex t e.succ=rootBranchVertex t (t.parent e) :=
      rootBranchVertex_step t e.succ (Fin.succ_ne_zero e) hpn
    exact (congrArg (rootBranchVertex t) hp).trans (he.symm.trans (congrArg (rootBranchVertex t) hc.symm))
  · have hpn : t.parent e ≠ 0 := by simpa only [← hp] using hv
    have he : rootBranchVertex t e.succ=rootBranchVertex t (t.parent e) :=
      rootBranchVertex_step t e.succ (Fin.succ_ne_zero e) hpn
    exact (congrArg (rootBranchVertex t) hc).trans (he.trans (congrArg (rootBranchVertex t) hp.symm))

/-- A graph-rooted parent presentation constructs the exact two sides of d. -/
def graphLeakCutOfPresentation {n : ℕ} (d : G.Dart) (p : RootedTreePresentation n G d.fst) :
    GraphLeakCut d := by
  let v := p.vertices.symm d.snd
  have hroot : p.vertices.symm d.fst=0 := by
    have he := congrArg p.vertices.symm p.root_eq
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hvadj : (orderedTreeGraph p.tree).Adj 0 v := by
    apply (p.adj_iff _ _).mpr
    simpa only [v,Equiv.apply_symm_apply,p.root_eq] using d.adj
  have hv := orderedGraph_root_adj p.tree v hvadj
  let side : V → Bool := fun w => decide (rootBranchVertex p.tree (p.vertices.symm w)=v)
  have hs : side d.fst=false := by simp [side,hroot,rootBranchVertex_zero,Ne.symm hv.1]
  have ht : side d.snd=true := by
    simp only [side]
    rw [rootBranchVertex_child p.tree v hv.1 hv.2]
    simp
  refine ⟨side,hs,ht,?_⟩
  intro e hed hes
  let u := p.vertices.symm e.fst
  let w := p.vertices.symm e.snd
  have hadj : (orderedTreeGraph p.tree).Adj u w := by
    apply (p.adj_iff _ _).mpr
    simpa only [u,w,Equiv.apply_symm_apply] using e.adj
  by_cases hu : u=0
  · have he0 : e.fst=d.fst := by
      have hh := congrArg p.vertices hu
      simpa only [u,Equiv.apply_symm_apply,p.root_eq] using hh
    have hw := orderedGraph_root_adj p.tree w (hu ▸ hadj)
    have hwv : w ≠ v := by
      intro hwv
      apply hed
      apply SimpleGraph.Dart.ext
      apply Prod.ext he0
      exact p.vertices.symm.injective hwv
    change decide (rootBranchVertex p.tree u=v)=decide (rootBranchVertex p.tree w=v)
    rw [hu,rootBranchVertex_zero,rootBranchVertex_child p.tree w hw.1 hw.2]
    simp [hwv,Ne.symm hv.1]
  · by_cases hw : w=0
    · have he0 : e.snd=d.fst := by
        have hh := congrArg p.vertices hw
        simpa only [w,Equiv.apply_symm_apply,p.root_eq] using hh
      have hu' := orderedGraph_root_adj p.tree u (hw ▸ hadj.symm)
      have huv : u ≠ v := by
        intro huv
        apply hes
        apply SimpleGraph.Dart.ext
        exact Prod.ext (p.vertices.symm.injective huv) he0
      change decide (rootBranchVertex p.tree u=v)=decide (rootBranchVertex p.tree w=v)
      rw [hw,rootBranchVertex_zero,rootBranchVertex_child p.tree u hu'.1 hu'.2]
      simp [huv,Ne.symm hv.1]
    · have he := orderedGraph_nonroot_same_branch p.tree u w hu hw hadj
      exact congrArg (fun q => decide (q=v)) he

/-- Every directed edge of every finite independent tree admits the needed cut. -/
def finiteTreeLeakCut [Fintype V] (hG : G.IsTree) (d : G.Dart) : GraphLeakCut d :=
  graphLeakCutOfPresentation d (finiteGraphPresentation G hG d.fst)

end HydrologyTree
