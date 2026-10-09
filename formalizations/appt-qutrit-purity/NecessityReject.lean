import APPT.Quantum.SpectralNecessity
open APPT.Quantum
-- Deliberately incorrect corner placement; the positive control uses 8.
example : slotA (0,0) = 7 := by decide +kernel
