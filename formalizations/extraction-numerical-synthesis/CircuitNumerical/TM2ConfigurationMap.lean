import CircuitNumerical.PacketCounterAlphabet

namespace CircuitRecursion.TM2ConfigurationMap

/-- A proved configuration translation commutes with the actual lifted
transition iteration, including post-halt none. This is an operational
simulation theorem, not an independently supplied cost annotation. -/
theorem iterate_map {σ τ : Type*} (f : σ → Option σ) (g : τ → Option τ) (tr : σ → τ)
    (hstep : ∀ c,g (tr c)=(f c).map tr) (n : ℕ) (x : Option σ) :
    (fun y : Option τ => y.bind g)^[n] (x.map tr)=
      ((fun y : Option σ => y.bind f)^[n] x).map tr := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    have hs : (x.map tr).bind g=(x.bind f).map tr := by
      cases x with
      | none => rfl
      | some c => exact hstep c
    rw [hs,ih]

def mapRun {σ τ : Type*} (f : σ → Option σ) (g : τ → Option τ) (tr : σ → τ)
    (hstep : ∀ c,g (tr c)=(f c).map tr) {c d : σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime f c (some d) t) :
    StateTransition.EvalsToInTime g (tr c) (some (tr d)) t :=
  ⟨⟨run.steps,by
    have he:=iterate_map f g tr hstep run.steps (some c)
    change (fun y => y.bind g)^[run.steps] (some (tr c))=some (tr d)
    have hr : (fun y : Option σ => y.bind f)^[run.steps] (some c)=some d := run.evals_in_steps
    rw [hr,Option.map_some] at he
    exact he⟩,run.steps_le_m⟩

theorem mapRun_steps {σ τ : Type*} (f : σ → Option σ) (g : τ → Option τ) (tr : σ → τ)
    (hstep : ∀ c,g (tr c)=(f c).map tr) {c d : σ} {t : ℕ}
    (run : StateTransition.EvalsToInTime f c (some d) t) :
    (mapRun f g tr hstep run).steps=run.steps := rfl

end CircuitRecursion.TM2ConfigurationMap
