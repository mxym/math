# Concrete canonical Word packet gate provider

This package connects the actual four-gate binary output directly to the native
compiler's NativePacketDataOracle. binaryEntry stores one four-coordinate
entryBits vector and builds its signs/magnitudes plus shared denominator bits.
nativeEntryProgram runs four explicit signed normalizers and one denominator
trim; nativeEntry returns their canonical WordIntegerPacket. The value path
calls no Nat.bits, Int/Rat materialization, decoder or mathematical SU2 gate.

Eight named Lean theorems prove exact decode equality to the existing dyadic
integer packet, exact oracle equality, the original per-coordinate SU2
approximation condition, and actual represented height at mostp+1 (also the
ninth-power envelope used by the native compiler). The normalizer's actual
specified Bool/list actions are at most64(p+2). Padding and negative zero at
precision0 are handled by the actual normalizer, not an input assumption.

This is not a whole provider-machine-time theorem: precision-clock control,
the finite-state emissions, denominator list construction, allocation and
counter arithmetic are separate from that normalization counter. The provider
package proves the actual emission transition relation and output sizes; output
sizes are not silently substituted for execution time. This author scope has
ordinary type/axiom/small-data/standard-build evidence only as recorded in
verification/. No old audit, manuscript or package configuration is changed.
The SU2 density proof lives separately in extraction-rational-gate-universality;
its offline finite net is an existence result, not an efficient table finder.
