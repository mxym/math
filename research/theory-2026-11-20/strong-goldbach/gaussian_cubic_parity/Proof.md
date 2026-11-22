# Both cubic Frobenius parities on polynomially rough reflected primes at every center

There are absolute constants `κ,c>0` with the following property. For **each** sufficiently large even integer `N`, for **each** sign, at least `cN/(log N)^2` distinct ordinary primes `N/3<p<N/2` have these properties, with `n=N−p`:

1. `n` is squarefree, each prime factor `r` exceeds `N^κ`, and every such `r` is `1 mod 4`.
2. For each factor choose `r=a²+b²`, and test whether `(a+ib)^40=1` in `F₁₂₁=F₁₁[i]`. The parity sign `(−1)^{#{r|n : test fails}}` is the specified sign.

This is a pointwise assertion about the signs on actual, unaltered prime shifts. It neither detects the parity of *all* factors nor asserts that any of these partners is prime or semiprime. No averaging over centers, unproved zero-free region or exceptional character is used.

## 1. A genuine cubic trace and its published shifted estimate

Use the conductor-11 order in the Gaussian integers. Since these have class number one and 11 is inert, its ring class group is
`F₁₂₁× / (F₁₁× Z[i]×)`, cyclic of order `120/(10·4/2)=6`. Equivalently, on ideals prime to 11 choose a Gaussian generator and evaluate a character of order three of `F₁₂₁×` on it. All rational units mod 11 and the four Gaussian units have order dividing 40, so the character factors through that quotient and its kernel in the original group has order 40. Its conductor as a Hecke character is precisely `(11)`: it factors through reduction there, is nontrivial, and conductor-one finite-order characters on Gaussian ideals are trivial. Its induction has weight one, level `|disc Q(i)|·Norm(11)=484`, nebentypus `χ=χ₋₄` (restriction to rational units is trivial). Complex conjugation inverts the cubic quotient since `z z̄` is rational. Thus the associated degree-six extension of Q is dihedral, with group `S₃`.

For `(n,22)=1` put `h(n)=(1*χ)(n)`, the number of Gaussian ideals of norm n, and `l(n)=Σ_{Norm I=n} ψ(I)`, the real cubic character trace. Then `|l(n)|≤h(n)≤τ(n)`. At a split prime the trace is 2 or −1 according as the stated finite-field test succeeds or fails; this is independent of associates or conjugation. At an inert prime both counts vanish. On squarefree n supported on split primes the two functions are `h(n)=2^ω(n)`, `l(n)=2^j(−1)^k`, where j and k count success and failure. The failures are the 3-cycle Frobenius primes, not all split primes.

The primary analytic input is [Blomer, Grimmelt, Li and Rydin Myerson (BGLM), Lemma 2.2 and proof, Theorem 3.3, Proposition 6.1](https://arxiv.org/pdf/2111.01601). Their §3 specifically assumes the Gaussian nebentypus, and the proof of Lemma 2.2 constructs precisely the higher-order ring-class cusp eigensystems used here. Its normalized eigenvalues away from the level equal l. Compare the uniform shifted-divisor / cusp estimates of [Assing, Blomer and Li](https://arxiv.org/pdf/2005.13915). The analogous classical conductor-23 form associated with Q(√−23) ([Zagier, §2, example following (48)](https://www.its.caltech.edu/~matilde/Zagier123ModularForms.pdf)) has a **different nebentypus**; this proof makes no claim for it. BGLM themselves analyze primes plus almost-prime **squares**; here the restriction is on the rational prime factors of the whole complementary Gaussian norm and the sign is its cubic trace. Also compare [Fuchs, Stange et al. on primitively represented shifted primes](https://arxiv.org/abs/2504.20289), a different, fixed-shift representation question. These comparisons are not a priority claim.

Choose `b mod 44` with `b≡N−1 mod 4` and `b≠0,N mod 11`. Both b and n are units mod 44 for p in this class, and `χ(n)=1`. Take a fixed smooth nonnegative W, bounded by 1, compactly supported inside (1/3,1/2), with positive integral. Write `w(p)=log p·W(p/N)·1_{p≡b mod 44}`, always with **prime p**. In this interval no prime p divides even N (N/p lies strictly between 2 and 3). Thus `(n,44N)=1`.

There is an absolute `θ>0` such that for `D=N^θ` and any fixed `C,A`,
```
Σ_{d≤D squarefree} τ(d)^C |Σ_{d|n} w(p) l(n)| ≪_{A,C} N (log N)^−A.             (1)
```
Indeed for `(d,44N)=1` write `n=dm` and invert the usual Hecke relation:
`l(dm)=Σ_{e|(d,m)} μ(e)χ(e)l(d/e)l(m/e)`. For fixed e the last coefficient is at `(N−p)/(de)`; apply BGLM 3.3 with `σ=−1,f=N,q=44,Δ=de`, fixed level and smoothness. The inverse-polynomial gain `O((de)^C₀ N^{1−η})` holds with absolute fixed `C₀,η` independent of the divisor weight exponent C. Replacing Λ by genuine prime weights costs `N^{1/2+o(1)}` per d (each eigenvalue is divisor-bounded here). Take θ so small that the d-sum still saves a power, using `τ(d)^C=N^{o(1)}`. Nonunit d give zero. All dyadic support conditions of the theorem hold since both p and N−p are comparable to N. In particular we do not assume cusp cancellation after putting a nonmultiplicative sieve cutoff directly into the theorem.

## 2. Positive measure at a polynomial level

The following distribution lemma for h is needed for the *same* weighted sample. Put `L=log N`. For `r∤44N` prime let
```
H_r = Σ_{j≥0} χ(r)^j/φ(r^j),            H_N=∏_{r∤44N} H_r,
g(r) = [Σ_{j≥0} χ(r)^j/φ(r^max(1,j))]/H_r .
```
Set `g(r)=0` for other r; extend multiplicatively to squarefree d. Write `X₀=(2N/φ(44))(∫W)H_N`. With θ suitably decreased,
```
Σ_{d≤D squarefree} τ(d)^C |Σ_{d|n} w(p) h(n) − X₀ g(d)| ≪_{C,A} N L^−A.      (2)
```

Here are details on the uniformity in d. Pair complementary divisors using `χ(n)=1`: `h(n)=2Σ_{s|n,s<√n}χ(s) + 1_{n square}χ(√n)`. Squares cost `N^{1/2+o(1)}` aggregated since the d-weight counts divisors of n. Restrict throughout to d coprime to 44N; in the divisor sum s is also a unit mod 44N. Write uniquely `s=u v`, with `rad(u)|d` and `(v,d)=1`. Then the CRT congruences are `p≡w₀ mod 44[u,d]` and `p≡N mod v`, with w₀ a unit determined by b and `N mod [u,d]`. The small-modulus decomposition below is essential: taking an arbitrary cutoff for each CRT modulus is **not** part of BGLM's proposition.

Discard `u>D²` in both the prime sum and its density model. The +1 in the trivial count `N/([u,d]v)+1` costs `N^{1/2+θ+o(1)}` in total (at most √N values s per d). Every large u has `u/rad(u)>D`. Rankin with power 1/4 gives
```
Σ_{d≤D sf} τ(d)^C Σ_{rad(u)|d, u>D²} 1/[u,d]
 ≤ D^(−1/4) Σ_{d≤D sf} (τ(d)^C/d) ∏_{r|d} (1+Σ_{j≥1} r^(−3(j−1)/4))
 ≪ D^(−1/4) L^{O_C(1)}.
```
The v-harmonic sum and the prime logarithm cost at most powers of L. Density sums have the same bounds with another log power since `m/φ(m)≪log(2m)`. The same calculation without the tail factor gives an unrestricted polylog bound for the sum of `1/[u,d]`.

Partition the p-range into intervals of length at most `δ N` (all but endpoint of length comparable to this), and `u≤D²` into ratio-`(1+δ)` intervals, where `δ=L^{-B}`. Replace W by a constant in each p interval (error `O(δ N L^{O_C(1)})` by the same trivial estimates with `s≤√N`). For each pair of intervals replace `v<√(N−p)/u` by a common endpoint Q. For fixed u and fixed p interval the fringe contains `O(δ√N/u+1)` possible v; their sum of reciprocals is `O(δ+u/√N)`. Count primes trivially in this p interval by counting integers, at most `δN/([u,d]v)+1` for each v. After all p intervals the total fringe, including log weights, is
```
≪ (δ+D²/√N) N L^{O_C(1)} + N^{1/2+θ+o(1)} L^{O(B)} + N^{3θ+o(1)} L^{O(B)}.
```
Indeed in the +1 term one may sum over d,u using at most D² choices of u per d and `Σ_{u≤D²}1/u≪L`. The density fringe is bounded the same way. B can be chosen as large as needed.

Within a pair of intervals use Proposition 6.1 with free long modulus v up to the *common* Q, its unit classes mod 44 distinguishing the sign χ(v), `a₁=N,a₂=1`, and small CRT modulus `b'=44[u,d]`. Each b' receives at most `τ(b')²` choices of d,u and their weights are divisor-bounded. Apply the supremum over the unit CRT residue already present in the proposition and the triangle inequality (for a fixed b',w₀ is in fact determined). For `3θ<ϖ` with strict margin we have `b'≤44D³≤x^ϖ`, `Q≤√N≤x^{1/2+ϖ}`, and `N≤x^{1+ϖ}` at both p-interval endpoints `x≍N`; `(v,Nb')=1` is exactly the required restriction. Sum the polylog number of bins, classes and endpoints, choosing the log saving in the proposition after B. The main term there may be replaced by interval length divided by `φ(44)[φ([u,d])]φ(v)` by the ordinary prime number theorem; the total reciprocal weights are polylogarithmic. Its Λ sum can be used throughout: nonprime powers in the central range contribute `N^{1/2+o(1)}` for the sharp argument since d,s divide `N−p^j`; in the enlarged cutoffs they still divide that integer, including for a nonunit prime base, and a unit mask only decreases that bound. The harmless density PNT replacement drops primes dividing the modulus, contributing at most `O(L²)` inside its numerator. Reverse the bin approximations to obtain the density integral with short factor
`Σ_{s<√(N−t),(s,44N)=1} χ(s)/φ([s,d])`.

Multiply this factor by `φ(d)` and complete to its Euler product. In detail, the resulting summand is the convolution of `χ(s)/s` with a multiplicative sequence supported on squarefree numbers: its local degree-one correction at `r∤44Nd` is `χ(r)/(r(r−1))`, at `r|d` is `χ(r)(1−1/r)`, and at `r|44N` is `−χ(r)/r`. Its weighted absolute sum with multiplier `s^{1/4}` is `≪d^{1/4} N^{o(1)}` by the Euler factors (for target divisors `∏_{r|44N}(1+O(r^{-3/4}))=N^{o(1)}`). Periodicity gives `Σ_{n>T}χ(n)/n≪1/T`. Applying it in this convolution, including terms with correction index exceeding T, yields tail `≪T^{-1/4}d^{1/4}N^{o(1)}/φ(d)` in the original sum. Here `T≍√N`; the aggregate is power-small after θ is fixed sufficiently small. The completed product is `H_N g(d)` by the local definitions; its conditional convergence is the usual fixed-character Euler product at 1, or follows from the same convolution and the PNT in fixed arithmetic progressions. This proves (2).

For `r∤44N`,
```
g(r)=(2r−1)/(r²−r+1) if χ(r)=1,   g(r)=1/(r²−r−1) if χ(r)=−1.
H_r(1−g(r))=1−1/(r−1).
```
In particular `0≤g<1` and `Σ_{sqrt x<r≤x}g(r)≪1`, with `∏_{sqrt x<r≤x}(1−g(r))≫1`, uniformly in N and x. If `y=N^κ` with κ fixed positive, then
```
V(y)=∏_{r≤y}(1−g(r)),                 H_N V(y) ≫_κ 1/log N.                     (3)
```
Indeed the small factors now equal `1−1/(r−1)` at primes outside 44N, so Mertens applies (including extra missing primes only increases this product). The ordered tail `∏_{r>y}H_r=1+o(1)` after excluding the finitely many fixed ramified primes, by fixed-character PNT and absolute quadratic error; omitting `r|N,r>y` changes it by `1+o_κ(1)`, since there are at most `1/κ` of them. All factors are positive.

## 3. A sufficiently accurate sieve for the *signed* trace

Here a plain unspecified exponential fundamental-lemma error would not be enough: the absolute trace can lose a factor `2^(1/κ)` against h. We give an elementary sandwich to make the order of parameter choices explicit. For `y=N^κ` put primes `r≤y` into disjoint shells `(y^{2^{-j-1}},y^{2^{-j}}]`, j starting at zero; ignore empty shells. For an even integer `R≥2` truncate the binomial inclusion-exclusion for the no-divisor indicator in shell j after `K_j=R+2j` terms (that is, include degrees 0 through K_j). Write U_j for this even partial sum, ν_j for the number of distinct divisors in that shell, and `E_j=binom(ν_j,K_j)`. Bonferroni gives `U_j≥I_j≥U_j−E_j`; in particular U_j is nonnegative. By telescoping,
```
U=∏U_j ≥ I=1_{P⁻(n)>y} ≥ U−E,       E=Σ_j E_j ∏_{i≠j} U_i ≥0 .
```
Each expands in squarefree-divisibility indicators with coefficient magnitudes bounded by `1+ω(d)` and support `d≤y^(2R+4)`, since `Σ_j K_j/2^j=2R+4`. In the E expansion a divisor can only contribute in the term for a shell which contains at least one of its primes. Thus (1),(2) evaluate these polynomials provided `κ(2R+4)<θ`.

Evaluate expectations in the product model of independent divisibility events with probabilities g(r). Each shell-mean `V_j=E[I_j]` is bounded below absolutely, and `E[E_j]≤C^{K_j}/K_j!` since its prime sum is bounded absolutely. Independence across shells and the upper Bonferroni bound imply
```
0≤E[U]−V≤E[E]≤V exp(Σρ_j) Σρ_j,     ρ_j=E[E_j]/V_j.
```
Uniformly in y,N this is `≤V exp(−R log R+O(R))` for sufficiently large R, by the factorial. First fix θ satisfying (1),(2); choose R even sufficiently large, then `κ=θ/(2R+5)`, so that this last relative error is `<2^(−1/κ−5)`. This is possible since `R log R` dominates every fixed multiple of R. These are fixed absolute parameters, not a promise of a practical number of almost-prime factors.

Equations (1),(2),(3) show that the positive rough h-mass `Σ w h I` is at least `(1−2^(−1/κ−4))X₀V` for all large N (use U−E); the signed mass `|Σ w l I|` is at most `2^(−1/κ−4)X₀V` (use U and `|l|≤h` against E). Non-squarefree rough partners cost only `N^{1−κ+o(1)}+N^{1/2+o(1)}` in either mass, counting multiples of `r²` for `r>y` with weights at most `L τ(n)`. On the surviving squarefree rows h vanishes unless all primes split, and `|l|≥2^(−1/κ) h`, since `ω(n)≤1/κ`. Thus the positive- and negative-trace rows each carry absolute trace mass `≫_κ X₀V≫_κ N/log N`, by taking the half-sum and half-difference. Each row has `w(p)|l(n)|≤L·2^(1/κ)`, proving the stated **unweighted** counts.

## What is not resolved

On this nonempty restricted family the ordinary Liouville sign is `(−1)^{j+k}`, whereas the trace detects `(−1)^k`. We have not controlled the parity of j, even on one target. The argument does not localize to the Chen range `Ω(n)≤2`: its own sieve requires `(2R+4)κ<θ` with θ small. Discarding the principal split factors, or taking products of trace signs over several fields, is not a condition in the BGLM correlation estimate. The tensor decomposition at a *prime* does not identify the product of the multiplicative trace coefficients at a composite with a linear combination of those same GL₂ coefficients. In particular we neither find a binary pair nor establish a Liouville/prime correlation on all such centers.
