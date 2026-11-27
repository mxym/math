# Smoothing of all ramified powers of the dyadic cyclotomic ideal

Let d be a power of two and consider all powers of the ideal (1−Y) in Z[Y]/(Y^d+1), in determinant-one canonical normalization. Their Gaussian smoothing thresholds have three logarithmic regimes, with abrupt changes at specific depths. We give an exact formula for the first-shell coefficient and uniform asymptotics down to vanishing tolerance. This also shows that the normalized dual shortest length alone does not fix the leading smoothing width, even within this very restricted family of ideals.

This is a computation of a geometry-of-numbers invariant for an explicit family, not an algorithm for shortest vectors in general ideals or any statement about a deployed scheme. The invariant is the one in [Lyubashevsky–Peikert–Regev, Definition 2.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) and the spherical case of [Peikert–Regev–Stephens-Davidowitz, Definition 2.4](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). Repeated-root cyclic codes and their weights are classical, e.g. [Massey–Costello–Justesen, Polynomial weights and code constructions](https://backend.orbit.dtu.dk/ws/files/4637283/J%C3%B8rn.pdf) and [Castagnoli et al., Repeated-Root Cyclic Codes](https://www.isiweb.ee.ethz.ch/papers/arch/gcasta-mass-inspec-1991-1.pdf). [Cyclic Lattices, Ideal Lattices, and Bounds for the Smoothing Parameter](https://arxiv.org/abs/2112.13185) gives related general bounds. The assertions below concern the quantitative smoothing asymptotics following from the exact weight recursion for **these ramified powers**, not a new coding principle.

## Statement

Let d≥4 be a power of two. Write L_(d,k) for the coefficient lattice of (1−Y)^k, and M_(d,k)=2^(−k/d)L_(d,k) for its determinant-one form. Take 0≤k≤d; powers outside that range give the same normalized lattices up to the periodicity k↦k+d. The normalized canonical ideal lattice is isometric to this coefficient lattice. Put a=d−k (the dual depth). Let η_ε be the ordinary spherical smoothing parameter: η_ε(Λ) is the smallest s such that Σ_(y∈Λ* nonzero) exp(−πs²‖y‖²)≤ε.

Define r and A to be the minimum nonzero squared length and its multiplicity in the **unscaled** L_(d,a). Then exactly
```
a=0:                  r=1,  A=2d.
1≤a≤d/2:              r=2,  A=4b·binom(d/b,2),
                             b is the least power of 2 with b≥a.
d/2<a≤3d/4:           r=4,  A=2d+16b·binom(d/(2b),2),
                             b is the least power of 2 with b≥a−d/2.
3d/4<a≤d:             r=4,  A=2d.
```
For every 0<ε≤1, uniformly in d and a,
```
π·2^(−2a/d) η_ε(M_(d,k))² = (log(A/ε))/r + O(1).
```
For ε→0 the O(1) improves to O(ε^(1/r)), still uniformly. In particular `(log A)/r` is `log d` up to bounded terms in the cubic case a=0, and for the three positive-depth ranges is respectively
```
log d − ½ log a;        ½ log d − ¼ log(a−d/2);        ¼ log d
```
up to uniformly bounded additive terms. Both formulas allow ε to depend on d, including arbitrarily small tolerance.

## Ideal structure and exact Construction A theta formula

The determinant of multiplication by 1−Y is 2, by evaluation of the minimal polynomial Y^d+1 at 1. Modulo 2 one has (1−Y)^d=0 in the quotient ring. Hence (1−Y)^dR⊆2R, and their equal indices 2^d show equality. In particular the index of L_(d,k) in Z^d is 2^k. The full canonical coordinate map is a similarity with common factor √d: the columns for distinct powers have inner product a sum of distinct odd-root phases, equal to zero. After determinant-one normalization the factor disappears.

In coefficient coordinates transpose of the signed shift Y is multiplication by Y⁻¹, so the Euclidean dual of L_(d,k) is the coefficient lattice of (1−Y⁻¹)^(−k). Since 1−Y⁻¹ is 1−Y times a unit, and (1−Y)^dR=2R, it equals (1/2)L_(d,d−k). Thus
```
M_(d,k)* = M_(d,d−k) = 2^(−a/d) L_(d,a).
```

For 0≤a≤d, L_(d,a) contains 2Z^d; its reduction mod 2 is the binary cyclic code C_(d,a)=((1+Y)^a) in F₂[Y]/((1+Y)^d). Let W_(d,a)(x,y)=Σ_(c∈C) x^(d−wt(c)) y^wt(c). With
```
E(t)=Σ_(z even) t^(z²),    O(t)=Σ_(z odd) t^(z²),    R(t)=O(t)/E(t),
```
the unscaled theta series at 0<t<1 is exactly
```
Θ_(d,a)(t)=Σ_(x∈L_(d,a))t^(‖x‖²)=E(t)^d W_(d,a)(1,R(t)).
```
This is just the sum over binary codewords, multiplying the one-coordinate parity theta factors.

Set m=d/2, and split a binary word into polynomial blocks (u,v) of length m, representing u+Y^m v. If a≤m, its reduction u+v modulo (1+Y)^m has exactly the needed divisibility condition (the kernel of the reduction consists of multiples of 1+Y^m=(1+Y)^m). For a≥m the word necessarily has equal halves (u,u), and membership is equivalent to u∈C_(m,a−m). Thus
```
W_(d,a)(x,y)= W_(m,a)(x²+y²,2xy)        for a≤m,
              W_(m,a−m)(x²,y²)         for a≥m.
```
Both agree when a=m. In particular for a=b a power of two, the code requires one even parity in each of the b residue classes of coefficient positions mod b. Indeed (1+Y)^b=1+Y^b, so reduction modulo it is exactly those b parities. For any z≥0 and h=d/b this gives
```
W_(d,b)(1,z)= [ ((1+z)^h+(1−z)^h)/2 ]^b .
```

For a>0 no weight-one codeword exists. A weight-two word Y^i+Y^j with i<j lies in C_(d,a) precisely if the multiplicity (2^{v_2(j-i)}) of (1+Y) in (1+Y^{j-i}) is at least a. This multiplicity formula follows by writing j−i as an odd integer times a power of two; the odd-power polynomial has a simple zero at 1. Thus when a≤d/2 the number of weight-two codewords is b binom(d/b,2) with b as in the first or second line above, and otherwise it is zero. In the latter case the lattice always has the 2d vectors ±2e_i of squared norm 4; its other norm-4 vectors can only come from binary weight four, with 16 independent signs each. By the repetition-half condition those weight-four words are exactly the doubled weight-two words of C_(d/2,a−d/2). These observations prove the exact values of r,A. They use only integrality and parity, not an estimate of the next shell.

## Uniform theta bounds at the first-shell scale

We claim Θ_(d,a)(t₀) is bounded by an absolute constant for t₀=A^(−1/r), uniformly in d,a. Here and below we may prove bounds for sufficiently large d, since the finitely many smaller dimensions have finitely many a, and t₀<1 for each. As t→0, the scalar theta series give R(t)≤C t and log E(t)≤C t⁴, with an absolute C.

Here is a useful estimate for the code piece. With 1≤j≤n/2 and n a power of two, if z≤C₀√j/n for any fixed C₀, then W_(n,j)(1,z) is bounded by a constant depending only on C₀. To see this, take the largest dyadic b≤j and use inclusion C_(n,j)⊆C_(n,b), valid coefficientwise for the enumerators. Since
```
((1+z)^h+(1−z)^h)/2 ≤ cosh(hz) ≤ exp((hz)²/2)
```
(the binomial expansion bounds each even coefficient), the logarithm of the power-b enumerator is at most n²z²/(2b)≤C₀². No approximation to the sign of 1−z is used here.

For first positive range 1≤a≤d/2, A is comparable to d²/a by the exact count and d/b≥2. So t₀ is comparable to √a/d. The preceding code estimate applies with z=R(t₀), and d log E(t₀)≤C d t₀⁴=O(1). The cubic a=0 case follows directly from Θ_(d,0)(t)=(Σ_z t^(z²))^d and t₀=1/(2d).

For d/2<a≤3d/4, A is comparable to d²/(a−d/2) and t₀ to (a−d/2)^(1/4)/√d. The code recursion passes to length d/2, depth a−d/2, and variable R(t₀)². This again meets the code estimate. The even theta term is bounded since dt₀⁴=O(1).

For a>3d/4 all codewords are repetitions of a length d/4 word four times. Thus W_(d,a)(1,z)≤(1+z⁴)^(d/4), even without the residual code restriction. With t₀=(2d)^(−1/4), both this factor at z=R(t₀) and E(t₀)^d are bounded. This proves the uniform theta claim in every case.

## Extracting the smoothing width

Let t_ε solve Θ_(d,a)(t_ε)−1=ε, so the left hand side of the smoothing formula is −log t_ε by duality and scaling. Since Θ coefficients are nonnegative and A t^r is its first nonconstant term, t_ε≤t₀ ε^(1/r). Write C for an absolute upper bound on Θ(t₀). The total theta tail at any t≤t₀ is at most C(t/t₀)^(r+1), because all squared lengths are integral and the other lengths are at least r+1. Thus
```
0 ≤ ε − A t_ε^r ≤ C ε^(1+1/r).
```
For small ε this gives −log t_ε=(log(A/ε))/r+O(ε^(1/r)) uniformly (r∈{1,2,4}). For the larger ε in (0,1], the same positivity gives `Θ(t)-1≤ (C−1)(t/t₀)^r` when t≤t₀, and choosing a uniformly small constant times t₀ ε^(1/r) gives the matching O(1) bound. All constants above are absolute.

For example at fixed ε>0 choose a=1 in one family and a a power of two with log a/log d→α in (0,1) in the other. Both determinant-one primal lattices M_(d,d−a) have normalized dual minimum tending to √2, since it is exactly √2·2^(−a/d). Yet the ratio of smoothing widths in the second and first families tends to √(1−α/2), because the multiplicity of weight-two codewords now grows more slowly. This is not a contradiction to general smoothing bounds in terms of successive minima: here the shortest shell size and multiplicity, not just its length, have been evaluated.

[The verifier](verify-ramified-smoothing.js) independently enumerates all repeated-root codewords up through dimension 16, checks every coefficient against the recurrence, and checks the weight-two count. The analytic inequalities above, not finite examples, prove the asymptotics.
