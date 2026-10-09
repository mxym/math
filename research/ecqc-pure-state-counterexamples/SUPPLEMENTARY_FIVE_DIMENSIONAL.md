# Additional full-Schmidt-rank five-dimensional pure witness

This supplement proves the additional witness checked by `check_intervals.py`. It is not needed for the prime-dimensional classification or the sharp low-dimensional singlets in `paper.tex`.

Use the same canonical quadratic MUBs as in the paper, identically at both parties, and set

\[
 |\eta\rangle=(20|00\rangle+20|11\rangle+|22\rangle+|33\rangle+|44\rangle)/\sqrt{803}.
\]

This is a normalized pure state of Schmidt rank five, with marginal spectrum `(400,400,1,1,1)/803`. Write its marginal entropy as `H`; its quantum mutual information is `2H` and its computational measurement mutual information is `H`.

Let `w=(20,20,1,1,1)`, `zeta=exp(2*pi*i/5)`, and

\[
 T_{a,t}=\left|\sum_{x=0}^4 w_x\zeta^{-2ax^2-tx}\right|^2,
 \quad K_a=\frac15\sum_{t=0}^4\frac{T_{a,t}}{803}\log\frac{T_{a,t}}{803}.
\]

Direct evaluation of the pure-state Born amplitude gives `P^(a)[j,k]=T[a,j+k]/(25*803)`. Character orthogonality gives `sum_t T[a,t]=5*803`, so both marginals are uniform and the setting information is exactly `K_a`.

The squared amplitudes lie in `Q(sqrt(5))`. In the following table a pair `(A,B)` denotes `A+B sqrt(5)`:

| a / t | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 0 | (1849,0) | (1083/2,361/2) | (1083/2,-361/2) | (1083/2,-361/2) | (1083/2,361/2) |
| 1 | (594,-209) | (594,-209) | (1283/2,399/2) | (1544,19) | (1283/2,399/2) |
| 2 | (594,209) | (1544,-19) | (594,209) | (1283/2,-399/2) | (1283/2,-399/2) |
| 3 | (594,209) | (1283/2,-399/2) | (1283/2,-399/2) | (594,209) | (1544,-19) |
| 4 | (594,-209) | (1283/2,399/2) | (1544,19) | (1283/2,399/2) | (594,-209) |

This is an exact expansion using `2*cos(2*pi/5)=(-1+sqrt(5))/2` and `2*cos(4*pi/5)=(-1-sqrt(5))/2`, not a floating-point table. In particular `K_1=K_4` and `K_2=K_3`.

The verifier obtains the following closed intervals in natural units; both integers in each pair are over the denominator `10^12`:

| Quantity | Lower numerator | Upper numerator |
|---|---:|---:|
| H | 719274218695 | 719274218696 |
| K_0 | 339790731249 | 339790731250 |
| K_1=K_4 | 316889919807 | 316889919808 |
| K_2=K_3 | 243964476571 | 243964476572 |

Therefore the computational score is the unique maximum and is deleted by the ECQC minimum. The excess is

\[
 K_0+2K_1+2K_2-2H\geq22951086613/10^{12}>1/50.
\]

## Why the interval checker is rigorous

For `D=10^45`, compute `m=isqrt(5D^2)`. Integer squaring verifies `m^2<5D^2<(m+1)^2`, which brackets `sqrt(5)` between `m/D` and `(m+1)/D`. All algebraic arithmetic is then rational interval arithmetic.

For a positive rational `r`, range-reduce `r=2^k y` with integer `k` and `1<=y<=2`. Put `z=(y-1)/(y+1)`, so `0<=z<=1/3`. For `n=64`, let

\[
 L_n(y)=2\sum_{j=0}^{n-1}\frac{z^{2j+1}}{2j+1},\quad
 R_n(y)=\frac{2z^{2n+1}}{(2n+1)(1-z^2)}.
\]

Integrating the geometric series gives `L_n <= log(y) <= L_n+R_n`: all omitted terms are nonnegative; each denominator is at least `2n+1`, and the remaining powers form a geometric series. Compute `log(2)` by the same formula and add `k*log(2)` with signed interval multiplication. Monotonicity of the logarithm bounds interval inputs from their endpoints. Ordinary interval products enclose `x log(x)`, including all correlations between repeated appearances of `x` by over-enclosure. Decimal display uses exact outward integer rounding.

The code recomputes the squared amplitudes from the integer vector, proves each lower probability bound positive, checks normalization, checks the strict maximum being removed, checks the coarse table above, and checks the excess exceeds `1/50`. It imports no other checker. The algorithm is a finite rational certificate with a stated analytic remainder, not a claim of Lean kernel verification.

Copyright (c) 2026 Yongxian Zhang. All rights reserved. AI-assisted research; no external funding or external professional peer review claimed.
