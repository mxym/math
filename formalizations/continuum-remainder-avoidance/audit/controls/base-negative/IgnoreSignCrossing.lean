import ContinuumGeometric.Planar
open ContinuumGeometric
-- Intentionally false: even one affine cut realizes three exact signs globally.
example : (realizedPlanePatterns (fun _ : Fin 1 => ((1,0,0) : AffineCut))).card ≤ 1 := by
  have hn : (fun _ : Fin 1 => CutSign.negative) ∈
      realizedPlanePatterns (fun _ : Fin 1 => ((1,0,0) : AffineCut)) :=
    (mem_realizedPlanePatterns _ _).mpr ⟨(-1,0), by intro i; norm_num [evalCut, cutSign]⟩
  have hz : (fun _ : Fin 1 => CutSign.zero) ∈
      realizedPlanePatterns (fun _ : Fin 1 => ((1,0,0) : AffineCut)) :=
    (mem_realizedPlanePatterns _ _).mpr ⟨(0,0), by intro i; norm_num [evalCut, cutSign]⟩
  have hp : (fun _ : Fin 1 => CutSign.positive) ∈
      realizedPlanePatterns (fun _ : Fin 1 => ((1,0,0) : AffineCut)) :=
    (mem_realizedPlanePatterns _ _).mpr ⟨(1,0), by intro i; norm_num [evalCut, cutSign]⟩
  have hsub : {(fun _ : Fin 1 => CutSign.negative), (fun _ : Fin 1 => CutSign.zero),
      (fun _ : Fin 1 => CutSign.positive)} ⊆
      realizedPlanePatterns (fun _ : Fin 1 => ((1,0,0) : AffineCut)) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hn
    · exact hz
    · exact hp
  have hthree := Finset.card_le_card hsub
  simp [funext_iff] at hthree
  omega
