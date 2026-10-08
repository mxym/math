import Init

namespace StandardAxiomSmoke

theorem propext_control (a b : Prop) (h : a ↔ b) : a = b := propext h

theorem choice_control {α : Sort u} (h : Nonempty α) : Nonempty α :=
  ⟨Classical.choice h⟩

theorem quotient_control {α : Sort u} (r : α → α → Prop) (a b : α) (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h

end StandardAxiomSmoke
