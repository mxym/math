# Extension to arbitrary bounded matching number

The [complete bounded-packing spectrum](../fractional-matching-spectrum/README.md)
uses the anchored form of this note's signed count to determine the
fractional spectrum for every fixed matching bound s, even without
intersectingness. Its finite law is

\[
\tau^*(H)\le r\Psi_s(m/r)+s/2,\qquad
\Psi_s(c)=\max_{\sum c_i=c,\ c_i\ge0}\sum_i\psi(c_i).
\]

The error s/2 is universally optimal. Common-rank disjoint components
attain every asymptotic value with matching number exactly s. The
spectrum has a finite closed formula and converges, after normalization,
to the concave endpoint interpolation when s diverges. The fixed-s and
diverging-s statements distinguish those two regimes.

The predecessor's 18 frozen files, manifest and checksums remain
unchanged. Its nine-export Lean base and exact construction helper are
copied byte for byte with explicit commit and hash attribution. Three
additional anchor exports are supplied; the spectral theorem is not
presented as a whole-paper formalization. The new result is fractional,
with no general integer-rounding or priority claim.
