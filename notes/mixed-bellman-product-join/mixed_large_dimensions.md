# Exact large-factor closure for the mixed quadratic/quartic potential

Put α=87/2000, β=11/2000 and T=α+β=49/1000. This lemma proves the mixed-potential product inequality whenever both factor dimensions are at least160. The other product cases must be proved separately before asserting the full invariant theorem.

Let r,s≥160 be integers, n=r+s, and let x,y>0. Define

C=g(r)g(s)/g(n), g(j)=j^j/j!,

B=(s x+r y)/n,

G₂=x²/(r+1)+y²/(s+1)−(r x+s y)²/[n²(n+1)],

A₄=1/(r+1)³−r/[n(n+1)³],

B₄=1/(s+1)³−s/[n(n+1)³].

Then

log(CB)−α(G₂−1)−β(A₄x⁴+B₄y⁴−1)<0.

This is stronger than the product condition for the actual harmonic-mean state H=n/(r/x+s/y). Indeed H≤(r x+s y)/n gives the G₂ lower bound, while H⁴≤(r x⁴+s y⁴)/n gives the diagonal quartic lower bound. The latter follows from monotonicity of weighted power means, or successively from weighted harmonic≤arithmetic≤fourth-power mean.

## 1. Quadratic reduction

Let Δ=4rs+3n+2 and k=(3n+2)/Δ. Direct expansion gives the exact nonnegative-square identity

G₂−kB² = [rs/((r+1)n²(s+1)(n+1)Δ)]

·[(s+1)(3r+s+2)x−(r+1)(r+3s+2)y]².

Hence G₂≥kB² for every x,y. This identity is independent of the box constraints used in the remaining finite product cases.

Also A₄,B₄>0. For example,

r(r+1)³/[n(n+1)³]<1

since r<n and r+1<n+1. Thus the diagonal quartic term is nonnegative. It follows that the left side of the claimed inequality is at most

log(CB)−αkB²+T.

Maximizing over all B>0 gives

log(CB)−αkB²+T ≤ (1/2)log[C²/(2αk)]−1/2+T.

Therefore it suffices to show C²/k<2α exp(1−2T).

## 2. Uniform factorial bound

Robbins' factorial bounds imply

C² < n/(2πrs) exp[1/(6n)−2/(12r+1)−2/(12s+1)] < n/(2πrs).

The exponent is negative because 1/(6n)≤2/(12s+1) (equivalently12s+1≤12n), while the other subtracted term is strictly positive.

Consequently

C²/k < (2/π)[n/(3n+2)+n/(4rs)]

< (2/π)[1/3+1/320]

= (2/3+1/160)/π.

Here n/(rs)=1/r+1/s≤1/80.

## 3. Exact constants

The elementary bound π>157/50 yields

C²/k < (2/3+1/160)/(157/50)=1615/7536.

Exact rational arithmetic verifies

1615/7536 < (87/1000) Σ_{j=0}^{10}(451/500)^j/j!

< (87/1000) exp(451/500)=2α exp(1−2T).

This proves the claimed strict product inequality uniformly for r,s≥160.

For completeness, π>157/50 follows from Machin's identity and alternating-series bounds:

π=16 arctan(1/5)−4 arctan(1/239)

>16[1/5−(1/5)³/3+(1/5)⁵/5−(1/5)⁷/7]−4/239>157/50.

Machin's identity follows by tangent double-angle formulas, which give tan(4 arctan(1/5))=120/119 and tan(4 arctan(1/5)−arctan(1/239))=1; the latter angle lies in(0,π/2).

The accompanying checker additionally certifies exp(1+T)<571/200=2.855. It uses a positive rational Taylor sum and a geometric bound on the remaining exponential terms. This decimal upper endpoint is applicable to the full class only after the remaining product cases, join induction, and spectral reduction are supplied.
