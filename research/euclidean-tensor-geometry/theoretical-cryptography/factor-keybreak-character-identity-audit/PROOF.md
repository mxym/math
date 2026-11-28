# Proof and exact counterexample

Let (G=(mathbb Z/qmathbb Z)^	imes). Character orthogonality gives
[
mathbf 1_{x=ell y	ext{ in }G}
=
rac1{|G|}sum_{chiinwidehat G}
chi(x)overline{chi(ell y)}
=
rac1{|G|}sum_{chi}
overline{chi(ell)}chi(x)overline{chi(y)}.
]
After stratifying by the common gcd (delta), this is exactly the corrected
term
[
rac1{arphi(q)}
sum_chi
overline{chi(ell)}
mathcal V_{1,delta}(chi)
mathcal V_{2,delta}(overlinechi).
]

By contrast, the printed term
[
rac1{arphi(q)}
sum_chi
overline{chi(ell)}chi(x)chi(y)
]
equals (mathbf 1_{xy=ell	ext{ in }G}).

## Minimal exact witness

Take (q=10), (G={1,3,7,9}), (ell=3), (x=1), and (y=7).
Then
[
xequiv ell ypmod {10}
quad	ext{because}quad
3cdot7equiv1pmod {10},
]
but
[
xyequiv7
otequiv3pmod {10}.
]
Therefore the target left side is (1), the printed character sum is (0),
and the corrected character sum is (1).

For real (v_2),
[
mathcal V_{2,delta}(overlinechi)
=overline{mathcal V_{2,delta}(chi)},
]
so the magnitude and character-energy estimates used by the local
Cauchy–Schwarz step are unchanged.
