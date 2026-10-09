import APPT.Quantum.SpectralNecessity
open APPT.Quantum
example : slotA (0,0) = 8 := by decide +kernel
example : slotB (1,1) = 5 := by decide +kernel
#check density_appt_has_sorted_spectrum
#print axioms density_appt_has_sorted_spectrum
