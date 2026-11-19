# Regular polygons from one constant powered-distance sum: the disk and the orders through eighteen

**Scope.** Let a test circle have positive radius. Translate its center to zero and divide all lengths by its radius. For N≥2 distinct planar sites, set k=N−1. Suppose the single function
\[
 U(x)=\sum_{j=1}^N |x-z_j|^{2k}
\]
is constant on |x|=1. Then the sites form a regular N-gon on a concentric circle in either of the following two regimes:

1. All sites belong to the closed unit disk, in every order N.
2. The sites are arbitrary in the plane, for each 2≤N≤18.

For N=2 “regular” means an antipodal pair. The converse in both statements is classical. Site distinctions exclude the collapsed configuration at zero. There is no claim here for general configurations of order 19 or more. The finite-order portion is a computer-assisted proof using exhaustive coefficient positivity, not floating-point sampling. All estimates below use the single exponent. The known theorem assuming every even exponent up to 2N−2 is different.

## Moments and a common peak

Put z=r exp(iφ), with arbitrary φ at zero. For 0≤m≤k put
\[
 d_m(s)=\sum_{\ell=0}^{k-m}{k\choose\ell}{k\choose\ell+m}s^\ell,\qquad
 A_m(r)=r^m d_m(r^2).
\]
Expanding (1−r exp(i(φ−θ)))^k and its conjugate gives
\[
 |e^{iθ}-z|^{2k}=A_0(r)+2\sum_{m=1}^k(-1)^m A_m(r)\cos(m(φ-θ)).
\]
Hence constancy is equivalent to \(\sum_j A_m(r_j)e^{imφ_j}=0\) for all 1≤m≤k. This Fourier criterion is prior work. Each A_m(R)>0 for R>0; A_0(r) is strictly increasing for r≥0.

Let R=max r_j>0 and rotate a chosen site of radius R to the positive axis. The Fejér polynomial
\[
 F_N(φ)=1+2\sum_{m=1}^k(1-m/N)\cos(mφ)
 =\tfrac1N\left|\sum_{a=0}^{N-1}e^{iaφ}\right|^2
\]
is nonnegative, with F_N(0)=N and exactly the other Nth-root directions as zeros. Once the radii are equal, \(\sum_j F_N(φ_j)=N\) by the moments. Every other site must occupy a zero; distinctness exhausts the roots. Conversely their geometric sums vanish.

## I. Positivity inside the circle in all orders

For 0<S≤1 define the following real polynomial in z and its conjugate:
\[
 T_S(z)=A_0(r)/A_0(S)+2\sum_{m=1}^k(1-m/N)
                   A_m(r)\cos(mφ)/A_m(S).
\]
It equals F_N on the boundary r=S. We show it is ≥0 throughout this closed disk. First suppose S<1. For |ξ|=1, the positive function \(P_\xi(z)=(1-|z|^2)/|ξ-z|^2\) is the real part of \((1+\bar ξ z)/(1-\bar ξ z)\); it is harmonic and \(|\nabla P_\xi|=2/|ξ-z|^2\). Therefore
\[
   \Delta P_\xi^{-k}=\frac{4k(k+1)}{(1-|z|^2)^2}P_\xi^{-k}.
\]
Since \(P_\xi^{-k}=(1-r^2)^{-k}|ξ-z|^{2k}\), Fourier extraction in the boundary parameter ξ shows that \((1-r^2)^{-k}A_0(r)\) and \((1-r^2)^{-k}A_m(r)\cos(mφ)\) satisfy precisely the same equation as functions of z. Extraction is a finite Fourier expansion with a common smooth denominator. Thus \(f(z)=T_S(z)/(1-r^2)^k\) satisfies \(\Delta f=V f\) where V>0. On r=S it is nonnegative. A negative minimum in the interior would have \(\Delta f\ge0\) and \(Vf<0\), impossible. For S=1, fix r<1 and let S' tend up to 1 with r<S'<1. Since A_m(1)>0, T_{S'}(z)→T_1(z); nonnegativity follows. At r=1 it follows directly from F_N. No eigenfunction is evaluated at its singular boundary.

Apply this at S=R≤1. The maximum-radius site has T_R=N and every summand is nonnegative. Yet
\[
 \sum_j T_R(z_j)=\sum_j A_0(r_j)/A_0(R)\le N
\]
by the moments. Strict increase of A_0 forces all radii equal. The common-peak argument finishes the proof.

**Direct shifted version (Bosuwan).** In the unit normalization, fix h≥0 and replace each site term by \((|x-z_j|^2+h)^k\). The same conclusion holds if max r_j≤√(1+h). To see this set c=1+h. For each r choose q∈[0,1] by q/(1+q²)=r/(c+r²); this is well-defined since c≥1 and r/(1+r²)≤1/2. Set a=(c+r²)/(1+q²)>0. The site kernel is \(a^k|x-q e^{iφ}|^{2k}\), including r=0. As r increases on [0,√c], q is nondecreasing and q>0 for r>0. Let S=q(R), and use the previous nonnegative test weighted by \(a(r_j)^k/a(R)^k\). The maximum-radius site still contributes N. The total after the nonzero modes cancel equals
\[
 \sum_j \frac{a(r_j)^k A_0(q(r_j))}{a(R)^k A_0(S)}.
\]
The numerator as a function of r is the circle average of \((c+r^2-2r\cos θ)^k\). Its binomial expansion retains only the even cos powers, with nonnegative coefficients; its zeroth even-power term \((c+r^2)^k\) strictly increases. Thus the total is ≤N with strict inequality unless all radii equal. Equal radii imply regularity by the same Fourier argument with its common positive factor. This shifted result makes no claim about general outside configurations.

## II. Arbitrary planar sites through N=18

This part always has h=0; it does not require R≤1. Write t=r/R, s=R², x=cos φ, \(T_m(x)=\cos(mφ)\) for the Chebyshev polynomial. Define
\[
 B_N(t,s,x)=1+2\sum_{m=1}^k(1-m/N)t^m
             \frac{d_m(st^2)}{d_m(s)} T_m(x).
\]
Here \(B_N(1,s,\cosφ)=F_N(φ)\). Its sum over the sites is N, by division of each vanishing mth moment by the positive A_m(R). If B_N>0 for 0≤t<1, s≥0, |x|≤1, the chosen outer site contributes N, and all other terms are nonnegative. Thus there cannot be any smaller-radius site. The preceding equal-radius proof applies.

We provide exact verification of that strict positivity for the finite range. Put \(D(s)=\prod_{m=1}^k d_m(s)\), \(D_m=D/d_m\). Choose the integer L as follows:

| N | L |
|---|---|
| 2–13 | 2k |
| 14–16 | 3k |
| 17 | 8k |
| 18 | 14k |

The auxiliary polynomial is
\[
 H(t,s,x)=ND(s)\frac{ B_N(t,s,x)-t^L F_N(\arccos x)}{1-t}.
\]
It is a polynomial of t-degree ≤L−1, because \((t^j-t^L)/(1-t)\) is a polynomial for each j≤L (zero if j=L). It suffices to certify H>0 throughout the indicated domain with t<1. We send t=u/(1+u) and clear denominators by \((1+u)^{L-1}>0\). By the hockey-stick identity the coefficient of \(u^b\) in the transform of \(\sum_{d=j}^{L-1}t^d\) is \(\binom{L-j}{b-j}\) for j≤b≤L−1, zero otherwise. Thus for each \(0≤b<L,\ 0≤e≤k(k-1)/2\), the coefficient of \(u^b s^e\) in the cleared H is the following polynomial in x:
\[
 C_{b e}(x)=N\binom Lb [s^e]D(s)+
 \sum_{m=1}^k 2(N-m)T_m(x)
 \sum_{\ell:\,m+2\ell\le b}
 \binom k\ell\binom k{\ell+m} [s^{e-\ell}]D_m(s)
 \binom{L-m-2\ell}{b-m-2\ell}.
\]
Include only 0≤ℓ≤k−m and interpret off-support coefficient extractions as zero. The stated e bound is precisely the degree of D. Certifying that every C is strictly positive on [−1,1] proves H>0: u,s are nonnegative and the constant coefficient \(C_{0,0}\) is strictly positive.

**How to replay the certificate.** Run the bundled verify.py with Python 3 and no script arguments or dependencies. For each triple (N,b,e) it constructs exactly the coefficients above by integer convolution and the recurrence \(T_{m}=2xT_{m-1}-T_{m-2}\). For a degree-at-most-k polynomial C on [a,b'] consider the homogeneous polynomial \(P(v,w)=(v+w)^k C((a v+b'w)/(v+w))\). Its ordinary coefficients in \(v^{k-i}w^i\) are computed at a=−1,b'=1 by expanding every monomial, exactly. Strict positivity of every coefficient implies strict positivity on the entire closed interval (choose v,w≥0, v+w>0). When that test does not yet succeed, bisect. If V_i are the ordinary coefficients, the new left coefficients, all scaled by a common positive factor \(2^k\), are
\[
 V'_j=2^{k-j}\sum_{i=0}^j V_i\binom{k-i}{j-i},
\]
by substituting (v+w/2,w/2) for (v,w); reflection gives the right coefficients. A nonpositive endpoint or reaching maximum permitted depth without certification gives failure. The included exhaustive transcript records every order; its success covers all positions, scales and angles continuously. No fit to sampled sites or numerical tolerance is used.

The conclusion for N≥19 with arbitrary site radii, and the general h-shift outside the stated disk, are not established.
