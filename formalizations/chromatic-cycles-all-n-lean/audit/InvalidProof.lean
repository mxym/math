import ChromaticCyclesAllN

-- Adversarial regression test: the kernel must reject this invalid proof.
example : False := by
  exact True.intro
