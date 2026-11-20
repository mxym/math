# A stopping sieve at a fixed power, with target-uniform relative error

**Scope of the improvement.** Let L=log N, η=3/2−√2, N even, and S(N) its Goldbach singular series. There are absolute constants C,τ₀>0 such that for every **fixed** 0<τ≤τ₀,

    limsup_{N→∞ even} [1/(NS(N))] Σ_{p<N, P⁻(m)≤N^τ}
          (log p) μ²(m) |K(m)|  ≤ C τ^η,                          (1)

where m=N−p and K(m)=Σ_{k|m}μ(k)min(0,log(k/√m)). This is unconditional. Combined with the unconditional symmetric small-side evaluation in SymmetricParityReduction.md,

    R(N)/2 = NS(N) + Σ_{m<N, P⁻(m)>N^τ, μ(m)=1} Λ(N−m)K(m)
                    + O(C τ^η NS(N)) + o_τ(NS(N)).                 (2)

The notation in (2) means the limsup of the normalized error is at most an absolute constant times τ^η. The surviving m have at most 1/τ distinct prime factors, and (for m>1) even factor count. Their negative contributions are still unknown. This is **not** an o_N(1) remainder for fixed τ and does not prove Goldbach.

A second unconditional bound is for the **whole signed smooth transition** B_g of SmoothSignedTransition.md with Q=N^(1/2−τ), H=τL, α=√N/L^D for any sufficiently large fixed D. It holds with or without the centered reference:

    limsup |B_g|/(NS(N)) ≤ C τ^η.                                   (3)

Consequently the *original* all-modulus, all-prefix twisted hypothesis EH_μ(N^(1/2−τ)) from Huang–Li implies limsup |R(N)/(NS(N))−1|≤Cτ^η using **only ordinary Bombieri–Vinogradov** on the other side. For some fixed τ*>0 small enough this gives eventual Goldbach positivity under a twisted hypothesis at an exponent genuinely **below** 1/2. No numerical size for τ* is asserted. If trusted twisted levels are N^(1/2−o(1)) with arbitrary fixed logarithmic savings, the limsup is zero by first fixing τ then sending it to zero. None of these parity-sensitive input bounds has been proved here.

## 1. Avoid a logarithmic loss at a fixed stopping height

Take u=1/40 and an absolute small c>0, say c=10^(−5), and set w=N^(2c), z₀=N^c, Z₀=cL. It suffices to consider 0<τ≤c/4. Retain squarefree m; omit n=p^j with j≥2 and p|N at N^(1/2+o(1)) cost, p≤w at N^(2c+o(1)) cost, and m≤N^0.99 at O(N^0.99 L³). The latter bound uses Σ_{m≤x}τ(m)≪x log(2x) and two log weights. Dropping these is valid even in absolute estimates of individual divisor terms.

* If the product of primes of m up to z₀ is ≤N^u, call it a and put j=0. The cofactor is z₀-rough.
* Otherwise, let r be the **first** prime factor in increasing order whose inclusion would take that product over N^u. Let a be the product of the preceding primes. Assign j≥1 with Z_j=2^(−j)Z₀ and Z_j<log r≤2Z_j (use either convention consistently on equality). Then
  - a≤N^u, a>N^u/r≥exp(uL−2Z_j), and its prime factors are ≤exp(2Z_j);
  - all remaining factors of m are >z_j=exp(Z_j), or ≥r>z_j;
  - a>1 indeed has at least two prime factors since a>N^(u−c) and all its primes are ≤N^c;
  - the product of primes ≤r exceeds N^u, so by Chebyshev's bound for the primorial r≫L and z_j≥√r≫√L. There are O(log L) possible nonempty j.
  
Both j and a depend on **m alone**, not on a divisor allocation. There is no summation over choices of the crossing prime r when bounding the enlarged sums: a fixed m has exactly one stopping bin and one a. After reallocation and the triangle inequality, we merely sum over a satisfying the displayed constraints, dropping the rule that a particular r must occur. For j=0 the smoothness bound exp(2Z_j) may be used harmlessly; use the convention that no Rankin penalty is imposed then.

Write m=ak₀d₀ with the nonsmall cofactor cut into its two parts, and allocate k=e k₀ over e|a. The sign is retained in F_a(u')=Σ_{e|a}μ(e)f(u'+log e). For (1), f(u')=min(0,u'−θ), θ=(log m)/2. For (3), f(u')=ψ((u'−log Q)/H)min(0,u'−θ), θ=log(m/α), with the piecewise linear ψ of SmoothSignedTransition.md. The latter has height O(H), slope O(1), derivative variation O(1), and support O(H) whenever nonzero, with absolute constants for N large in terms of τ,D. For the former, if ω(a)≥2, F_a has support contained in [θ−log a,θ] by exact cancellation of its affine part. In either case on the relevant nonempty support, k₀≥N^0.4 and X=N/(ak₀)≥N^0.4. The exception a a single prime with the full nonsmooth kernel is treated directly in §5. The masks on m may be retained through this step and then discarded or used as restrictions on a.

Freeze log m in cells of width L^(−10) with ordinary arithmetic intervals J, preserving m in each cell through the rough prime sieve. There are O(L^11) cells; total individual-term freezing error O(N L^(−8)) by the 1-Lipschitz dependence on θ. Restricting m≤N and m>N^0.99, or to whichever interval allows nonzero f, does not affect the bound Σ_J|J|≤N. Integrable piecewise derivatives are not differentiated through the sieve.

## 2. Uniform rough-sieve factors, normalized by the true singular series

Use the elementary upper-bound sieve in [Ford, Sieve Methods, Theorems 2.3–2.4](https://ford126.web.illinois.edu/sieve2023.pdf). For an interval of length X' and at most two forbidden residues per prime ≤W, with at most one forbidden residue at 2, the upper bound is at most an **absolute constant** times X'∏_{p≤W}(1−ν(p)/p), plus O(W log(2W)). Indeed the local dimension condition is uniformly bounded (ν(p)/p≤2/p and ≤2/3 for p≥3); each squarefree CRT remainder is O(2^ω(d)), so its sum for d≤W is O(W log(2W)). This statement also follows directly from the geometrically blocked Brun sieve with constant local mass per block. The absolute constant does not depend on z_j,w or the particular local exceptions.

For fixed a,k₀ with (ak₀,N)=1, sieve d₀ on J/(ak₀) for P⁻(d₀)>z_j and p=N−ak₀d₀>w prime, using W=w. Define h(n)=∏_{r|n,r>2}(r−1)/(r−2), r prime. Mertens gives for the log-weighted count

    ≪ S(N) h(a)h(k₀) |J|/(ak₀ Z_j) + O(N^(2c+o(1))).               (4)

To see the local factors, for r≤z_j, r∤Nak₀ the number of exclusions is two; for z_j<r≤w it is one. A collision at r|N with r≤z_j costs exactly (r−1)/(r−2), and the product divides h(N) up to taking fewer factors; h(N) is an absolute constant times S(N). Each r|ak₀ costs at most the same factor (also for r>z_j, since r/(r−1)≤(r−1)/(r−2)). Treat 2 separately; the remaining base product is ≪1/(log w·Z_j), and prime weight ≤L costs only 1/(2c) times log w. The constant may depend on the **absolute** fixed c. A noncoprime numerator with p∤N has no summands. Uniformly on rough k₀, h(k₀)≪1: all its factors exceed z_j≫√L, Σ_{√(c' L)<r≤L}1/r=O(1) by Mertens and Σ_{r|k₀,r>L}1/r≪1. This also holds at j=0.

The second sieve upper bound for rough k₀ on an arbitrary interval is ≪|interval|/Z_j+O(z_j log(2z_j)). As in SmoothSignedTransition.md, partial summation by positive level sets on the O(τ(a)) monotonic pieces for |F_a| gives a main term (1/Z_j)∫|F_a(u')|du' after inserting 1/k₀. Its additive error is ≪L τ(a)^2 N^(−0.4+c+o(1)), since each |F|≤O(L τ(a)) in the operative range. The errors of (4), even summed over all cells, bins, a≤N^u and k₀≤N^(1/2+o(1)), are O(N^0.6) for large N. For the second sieve error use Σ_{a≤N^u}h(a)τ(a)^2/a=N^o(1). Thus (after summing cell lengths) it is enough for each j to bound

    [C NS(N)/Z_j²] Σ_a h(a)||F_a||₁/a.                              (5)

The additional a-weight is multiplicative and h(r)=1+O(1/r), so introduces only absolutely convergent Euler-factor corrections. Counting the finite masks or cells again only in the polynomially small additive errors is harmless.

## 3. Uniform Fourier bounds and a Rankin penalty *inside* the moments

For j≥1 majorize the restriction a>exp(uL−2Z_j) by exp(2−uL/Z_j) a^(1/Z_j). Write W_j=exp(2−uL/Z_j) for j≥1 and W₀=1; absorb absolute constants in later displays. After removing W_j, the moment weight at each prime r≤exp(2Z_j) is h(r)r^(1/Z_j) (at j=0 omit the power if desired). Uniformly for Z≥1,

    Σ_{r≤exp(2Z)} [h(r)r^(1/Z)−1]/r ≪ 1.

Indeed h(r)−1≪1/r, and r^(1/Z)−1≪(log r)/Z on this support; Σ_{r≤x}(log r)/r≪log(2x). The weights are uniformly bounded, so low-frequency quadratic marked-prime estimates also remain valid with absolute factors.

With Z=Z_j, λ=√2, b=2/λ=√2, use the sharpened uniform Fourier product estimate

    P(t) ≪ (1+Z min(1,|t|))^b (log(3+|t|))^C.                      (6)

Here P(t)=∏_{r≤exp(2Z)}(1+h(r)r^(1/Z)|1−r^(it)|²/(λr)); truncating primes only decreases this positive product. The preceding bounded correction reduces (6) to its unweighted version. For |t|≤1, PNT partial summation from any fixed sufficiently large start replaces the prime cosine sum by ∫cos(tv)dv/v with absolute O(1) error because |t|≤1. Split at v=1/|t| exactly as in SmoothSignedTransition.md to get Σ cos(t log r)/r≥log min(2Z,1/|t|)−O(1). For |t|≥1 begin at a point whose logarithm is A[log(3+|t|)]^4 with a fixed sufficiently large A. Its omitted harmonic prime mass is O(1+log log(3+|t|)); the PNT remainder is O(1) and the remaining cosine integral bounded. If this splitting point exceeds exp(2Z), the trivial bound for the entire omitted harmonic mass suffices. This proves (6) for **all** real t. The new factor is integrable against t^(−4) at infinity, unlike pulling a power of log log N in front of the integral.

## 4. Mark smallest prime layers with a geometric, summable cost

To prove (1), or the portion of (3) with P⁻(m)≤N^τ, write H=τL and partition the possible log least-prime values from O(1) to H into doubled intervals (Y/2,Y]. Include small primes in a first interval with lower harmonic endpoint normalized to 1; choose the final interval so H≤Y≤2H. At j=0 with a nonempty, and at all stopping bins j≥1, the least prime of m is in a whenever it is ≤N^τ (since τ≤c/4 at j=0 and a includes the smallest primes before crossing at j≥1). In a nonempty such layer, Y≪Z_j since a has primes ≤exp(2Z_j). Replacing Y by min(Y,2Z_j) in upper bounds changes only absolute constants; an interval with lower endpoint beyond the support is empty.

For ω(a)≥2 on a marked layer, the first Cauchy bracket of the preceding notes is now

    ≪ (Z+H') (1+Z/Y)^λ,

where H'=0 for (1) and H'=H for (3). The global kernel has support ≤log a; the smooth kernel can use log a+O(H). Factor the Euler product over r with Y/2<log r≤2Z and use Σ(log r)/r≪Z. The second bracket is

    ≪ Z^b Y^(3−b).                                                     (7)

To check (7) for the global kernel, |hat F_a|²=t^(−4)∏|1−r^(it)|². For the smooth one its unallocated Fourier weight is at most C/t² in absolute value, also sufficient here. Mark one prime ≤exp(Y) and one distinct prime ≤exp(2Z) when |t|≤1/Z. The restricted Euler sum is ≪t^4Y²Z² and its integral with t^(−4) is O(Y²Z). For 1/Z≤|t|≤1/Y mark just the small prime, integrate O(Z^b Y² t^(b−2)); for 1/Y≤|t|≤1 integrate O(Z^b t^(b−4)). The part |t|≥1 is O(Z^b) by (6). As 1<b<3 and 1≪Y≪Z, all fit (7); overlapping endpoints within bounded factors make no difference. These arguments use no conjecture. Cauchy–Schwarz with (5)–(7) gives, after restoring the Rankin factor, at most an absolute constant times

    NS(N) W_j (1+H'/Z_j)^(1/2) (Y/Z_j)^η.                           (8)

The identity of powers follows from λ=b=√2. Summing doubled layers Y≤2H costs only C(H/Z_j)^η, since η>0. Now sum j. At j=0, H/Z₀=τ/c; at j≥1 the factor W_j decays exponentially in L/Z_j=2^j/c. Therefore

    Σ_j W_j (1+H/Z_j)^(1/2)(H/Z_j)^η ≪_c τ^η                        (9)

uniformly for 0<τ≤c/4. The a single-prime exception occurs only at j=0. Its pointwise signed weight is ≤C log r for r≤N^τ (the kernel is uniformly Lipschitz). For it the rough d₀ estimate on the whole interval up to N/(rk₀) still applies even with small k₀, since k₀≤N/α for the fixed-center or ≤√N for the symmetric case and X≥N^0.4. Using Σ_{k₀ z₀-rough}1/k₀≪L/Z₀ and Σ_{r≤N^τ} (log r)/r≪τL gives ≪ NS(N)τ/c². This is smaller than the required order. These steps prove (1) and the marked part of (3).

## 5. Unmarked smooth block and interpretation

For (3) on P⁻(m)>N^τ, the first bracket is ≪(Z+H)(1+Z/H)^λ. At any nonempty stopping bin j≥1 we have H<2Z (otherwise a>1 cannot be made of primes above exp(H)). At j=0, H≤Z/4. Thus the bracket is ≪Z(Z/H)^λ up to absolute constants, including a=1. The Fourier square bracket is ≪Z^b H^(3−b): use |hat f(t)|≪min(H²,|t|^(−2)) and (6), splitting at 1/Z,1/H,1 and integrating exactly as in SmoothSignedTransition.md. The no-prime small part is harmless (its compact support for the smooth kernel has length O(H)). So (5) gives ≪NS(N)W_j(H/Z_j)^η, which sums as in (9). At a frozen θ, the local contribution of the centered reference in (3) uses the Mertens exponential bound at k≥N^(1/2−2τ), and variation O(L), hence is o(NS(N)); this argument can also be applied directly for each m without freezing. This completes (3).

Finally choose the fixed ordinary cutoff α=√N/L^D with classical BV as previously. Under EH_μ(Q), the 1−g(k) part is covered at k≤Q and the p² zero class bounds T(N); the unconditional g part incurs relative error ≤Cτ^η in the limsup by (3). All constants here may depend on the **fixed universal** u,c but not τ. This is why τ*>0 exists without a claimed practical numerical value. Similarly, (1), the symmetric small-side theorem, disappearance of μ=−1 composites, and extraction of R/2 from the prime terms yield (2). Prime m≤N^τ costs o(NS(N)) trivially. One may use (2) to seek a one-sided bound on finitely many rough even-factor patterns at fixed τ; the finite number of patterns is **not** a bound on their signed contribution. No unconditional positivity, polynomial error term, or numerical τ* is claimed.
