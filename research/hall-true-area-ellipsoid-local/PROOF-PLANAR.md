# Strict local optimum for sampling by true ellipse perimeter

Private analytic calculation. For the ellipse exp(t diag(1,−1)/2)S¹, let p(t) be the acute probability for three independent normalized arc-length samples. Then
  p(t) = 1/4 − 37 t⁴/(16π²) + O(|t|⁵).
The quadratic response cancels. This covers every sufficiently near-circular ellipse modulo similarities; no global comparison or other planar boundary curves are asserted. It is the d=2 pendant to the different quadratic argument in d≥3.

Put ρ=tanh t. The normalized pullback density in circle angle φ, relative to dφ/(2π), is the even π-periodic
  w(φ)=√(1−ρ cos(2φ))/mean√(1−ρ cos(2φ)).
Use two base points X,Y with uniform initial circle weight when expressing the integral. Their chord unit vector u=(X−Y)/||X−Y|| has uniform angle φ. Write X=cos θ u ± sin θ u_perp and Y=−cos θ u ± sin θ u_perp, with independent fair sign, θ uniform on [0,π/2], independent of φ (difference angles are uniform). The edge condition uses n=M u/||M u|| where M=diag(e^t,e^(−t)). Its angular tilt α from u satisfies
  α = arg(1+ρ exp(−2iφ))
    = −ρ sin x + (ρ²/2) sin 2x − (ρ³/3) sin 3x + O(ρ⁴),  x=2φ.
Both weights for X,Y have product W=w(φ+θ)w(φ−θ), unchanged by transverse sign. A third sample makes the angle at X obtuse exactly in the cap Z·n > X·n. The weighted cap integral, without 1/(2π), is A_n(|θ∓α|) where A_n(l)=∫_{−l}^l w(φ+α+β)dβ. For small ρ, this also agrees at both endpoints since |θ∓α|<π. Three disjoint obtuse vertex events give 1−p equal to 3/π² times the mean over φ of the θ integral of W [A_n(|θ+α|)+A_n(|θ−α|)]/2. At α=0, even using the same nonuniform w, p=1/4: under an antipodally symmetric continuous circle law, any sample point's following semicircle has mass 1/2; the three disjoint possible starts of a semicircle containing the full sample each have probability 1/4. This is just the circle-angle test used as a baseline, not an ellipse claim.

Temporarily extend A_n as an odd function of l. The unclipped difference from α=0 is
  Σ_{k≥1} (a_k/k) W sin(2kθ) D_k,
  D_k= (cos(2kφ+4kα)−cos(2kφ))/2,
where w(φ)=1+Σ a_k cos(2kφ). This is by integrating w and averaging the ± angular shifts. Restore the true modulus over 0≤θ<|α| by adding W A_n(|α|−θ); integrating this replaces exactly the sign-reversed term from one endpoint. The displayed expansions below take expectations in φ and integrate θ on [0,π/2] in the main term, and on [0,|α|] in the correction. They determine every order through four by a Taylor expansion of w, which is uniform and analytic for |ρ|<1.

Write y=2θ. Direct expansion yields
  a_1=−ρ/2−5ρ³/64+O(ρ⁴), a_2=−ρ²/16+O(ρ⁴), a_3=−ρ³/64+O(ρ⁴),
  W=1−ρ cos x cos y+ρ²[cos(2x)(1−cos(2y))/8+cos(2y)/8]+O(ρ³).
At k≥4 the order-≤4 terms vanish (the harmonics of the degree-j polynomial have order at most j, and D_k is O(ρ)). At k=3 the possible order-four average is proportional to ⟨sin x sin3x⟩=0. At k=1 the mean coefficients of W D_1 at orders 1,2,3 are, respectively, 1,0, and −17/16+3 cos y/4+3 cos(2y)/16. For clarity, the order-three contributions from D_1 alone, (W−1) at order 1 times D_1 at order 2, and W at order 2 times D_1 at order 1 average to −1, 3 cos y/4, and −1/16+3 cos(2y)/16, using ⟨sin²x cos²x⟩=1/8. Integrating against sin y dθ gives for k=1 total −ρ²/2+(9/16−5/64)ρ⁴. At k=2 the order-one mean vanishes, and the order-two mean of W D_2 is 3−cos y. Its product with sin(2y)/2 integrates to −1/3, and multiplies a_2, giving +ρ⁴/48. Thus the full unclipped difference is −ρ²/2+97ρ⁴/192+O(|ρ|⁵).

In the correction, W=w(φ)²+O(|ρ|θ²) and A_n(l)=2w(φ+α)l+O(|ρ|l³), by even integration and the bound on w″. Thus the correction equals the mean of α² w(φ)² w(φ+α)+O(|ρ|⁵). The weight product is
  1−(3/2)ρ cos x+ρ²[−1/8+(11/16)cos2x]+O(ρ³).
The mean order-two coefficient after multiplication by α² is 1/2; the order-three mean vanishes; the order-four mean is 1/8+3/8−1/16−11/64=17/64. Adding both contributions cancels the quadratic term and gives (37/48)ρ⁴ in the obtuse integral before 3/π². Substitution ρ=t+O(t³) gives the stated acute expansion. The script series.py independently replays the arithmetic in the Laurent variables exp(2iφ), exp(2iθ), rather than numerical integration. The analytic formula doesn't rely on numerics.
