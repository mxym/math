# A positive signed chamber of polynomial-size aliases

This extends the [actual three-prime alias asymptotic](DirectGoldbachPrimeModulusSmallAliasCancellation.md) to offsets of polynomial size with a dyadic factor. It proves an unconditional positive order-(N) **net** contribution even after charging an equal number of specified negative neighboring aliases. It does not bound the remaining aliases or the common target atom. Put X=N, L=log X, Q=X^{1−δ}, with 0<δ<1/4. Use fixed smooth nonnegative weights w,g on the interior of (0,1), ∫w>0, and g=1 on a neighborhood of 1−supp(w); let u≥0 be a nonzero fixed compact interior weight for q/Q. Fix ε>0 with ε<δ and δ+2ε<5/12. Fix C≥0. Uniformly for integer k=±2^s m with m odd, 1≤m≤L^C, and 0<|k|≤X^ε, the existing literal alias formula holds:
\[
 \sum_{q\ {\rm prime}}\log q\,u(q/Q)R(N+kq)
  = XQ\,\mathfrak S_k(N)\int w\int u+O_A(XQ L^{-A}).
\]
Here R is the true log-weighted two-prime convolution on w,g, and
\[
 \mathfrak S_k(N)=\prod_{\ell\mid k}(1+c_\ell(N)/(\ell-1)^2)
                 \prod_{\ell\nmid k}(1-c_\ell(N)/(\ell-1)^3).
\]
Odd k is in fact identically zero. Below, log powers B,J and the saving exponents can be chosen after A, C, δ and ε. No GRH.

## Relative short-interval AP PNT at every needed denominator

The preimage under α↦−kα of the ordinary major arcs for the short prime sum on scale Q has rational centers a/d with d/(d,k)≤L^B. Each such d divides |k|r for some r≤L^B, so d=2^j b, b odd≤L^{B+C}, d≤X^ε L^B, and there are O(L^{B+C+1}) distinct d. Their widths are at most L^B/Q (the actual width is no larger than L^B/(|k|[d/(d,k)]Q)).

For all these d, starts x in a fixed compact positive range comparable to X, and lengths h comparable to Q/L^B, we prove for every unit a
\[
 \psi(x+h;d,a)-\psi(x;d,a)=h/\phi(d)+O\bigl((h/d)\exp(-c L^{1/4}(\log L)^{-3/4})\bigr).
\]
Choose fixed slack σ>0 small with δ+2ε+4σ<5/12. Set the explicit-formula height T≈X^{δ+ε+2σ} (using a standard admissible height within factor 2 for each character). The proof also gives the respective relative bound for all partial lengths h≥X^{1−δ−σ} up to O(Q/L^B); the tail below this threshold is unnecessary. Then d·2T≤X^{5/12−c_1}, and X L^{O(1)}/T ≪ (h/d) X^{−σ/2} for large X, including h at the lower threshold.

Theorem 2 of [Iwaniec, On zeros of Dirichlet’s L series](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0023/PPN356556735_0023.pdf), in the arbitrary Q dividing q^m formulation stated precisely as Lemma 5 of [Harman–Kátai](https://www.impan.pl/shop/en/publication/transaction/download/product/82101), gives inverse width O(log rad(d)+(log(d(2T+3)) log log(d(2T+3)))^{3/4}) and only a possible real, real-character exception. Here rad(d)≤2L^{B+C}; no balanced-prime-exponent hypothesis applies. Any primitive real conductor dividing d divides 8b (on the 2-primary units all real characters factor through 8). Siegel’s theorem with a fixed exponent <1/(2(B+C+1)) puts its real zero farther from 1 than cL^{-1/2}; constants may be ineffective. Thus every character modulo d is free of zeros with real part >1−cL^{-3/4}(log L)^{-3/4} up to 2T.

Use the fixed-modulus density N_d(α,2T) ≪ (d·2T)^{(12/5)(1−α)}(log(d(2T+3)))^{O(1)}, summing all characters modulo d, from [Huxley, Large values of Dirichlet polynomials III](https://matwbn.icm.edu.pl/ksiazki/aa/aa26/aa2648.pdf), cited explicitly with that formulation as (3.3) in [Banks–Shparlinski](https://arxiv.org/pdf/1605.07553), where their (6.11) also shows this standard explicit-formula calculation. Fixed-modulus uniformity is essential; this is not an average over d. Partial summation bounds ∑χ∑_{|γ|≤2T} X^{β−1} by exp(−c L^{1/4} (log L)^{−3/4}): the density exponent leaves fixed slack in (12/5)log(d·2T)/L, and the right endpoint of integration has 1−β at least the zero-free width. Very low β are bounded by the trivial count O(dT L).

For the truncated explicit formula take the evaluation endpoints to adjacent half-integers preserving the respective sums at both ends. The endpoint displacement changes h by at most 1. Standard Perron truncation then costs O(X L^{O(1)}/T) per character; equivalently this is the absolute term in (6.11) of Banks–Shparlinski, without a factor 1/φ(d). At a half-integer the nearest-integer term is bounded by O(X L/T); an endpoint term O(log X) would likewise be negligible. Use the inducing primitive L-function and pay the imprimitive Euler factors O(ω(d)L), also negligible. For each zero the difference of x^ρ/ρ at the endpoints is ≪ h X^{β−1}, by integrating t^{ρ−1}. After 1/φ(d) character averaging the zero contribution has the stated relative size; the absolute truncation error is power-smaller as checked above. This proves the AP estimate uniformly in x and d.

## Summing all rational numerators without a polynomial loss

For a fixed v=w or g first use Λ rather than the true prime weight. At each unit residue r mod d, let the signed measure μ_r consist of Λ(n)v(n/X) at n≡r minus the continuous measure v(t/X)dt/φ(d); on nonunits take μ_r=0, omitting at most the prime powers dividing d. For h=c Q/L^B with c a small fixed constant, uniformly in real x,
\[
 |\mu_r((x,x+h])|\ll (h/d)\exp(-c' L^{1/4}(\log L)^{-3/4}).
\]
For this directly replace v(t/X) on each window by v(x/X), apply the AP estimate to the h window, and pay O((h/X)(h/d+1)L) for the fixed smooth derivative, using the trivial number of integers in the progression. Compact support means active windows have starts comparable to X; no truncation at an interior endpoint is needed. Continuous means are exact and their Fourier transforms are the V_v. Equivalently one could subtract a discrete smooth mean: Poisson summation in a residue at spacing d would replace it by the identical continuous mean in the frequency range |β|≤1/h with arbitrary power error, since d≪h and the nonzero dual frequencies are ≫1/d.

For all numerators a simultaneously set μ_a^*=∑_r e(ar/d) μ_r. The box-convolution form of Gallagher’s lemma (ordinary real Plancherel, with Fourier multiplier of the length-h box bounded below by a constant times h on |β|≤L^B/Q) yields
\[
 \sum_{a\bmod d}\int_{|\beta|\le L^B/Q}|\widehat\mu_a^*(\beta)|^2d\beta
 \ll h^{-2}\int_{\mathbb R}d\sum_r|\mu_r((x,x+h])|^2dx
 \ll X\exp(-c' L^{1/4}(\log L)^{-3/4}).
\]
The factor d is exact discrete Parseval, and d sums of residue errors each (h/d)^2 cancel it. For reduced a the continuous Fourier model is μ(d)V_v(β)/φ(d), with V_v(β)=∫v(t/X)e(tβ)dt. Reinsert omitted nonunit Λ inputs if desired and then replace all Λ by actual log primes. For each fixed d, the additive rational intervals are disjoint since 2L^B/Q≪1/d, so global Parseval pays the total weighted square norm of proper prime powers only O(√X L^{O(1)}), not d times this amount; one may use exactly the same argument for omitted nonunit inputs. Sum now over the O(L^{B+C+1}) actual denominators. This gives arbitrary-log error on the entire preimage union for both long factors, true prime coefficients retained.

## Completing the genuine alias formula

Outside the short major preimage, the ordinary Vaughan bound on the short prime polynomial U gives ≪Q L^{-A-3} on taking B large; full-circle Cauchy for the two long inputs uses ∫|F_wF_g|≪XL. The remaining collar |β|>L^J/X is negligible using the last Fourier inequality, Cauchy, U≪Q, and rapid decay of V_v. In bounding the model there are no polynomially many model centers: it vanishes when μ(d)=0, while squarefree d|kr satisfies d≤rad(k)r≤2L^{B+C}. There are only polylogarithmically many centers with d squarefree. This same inequality pays the whole preimage at nonsquarefree d, regardless of distance to its center.

On remaining squarefree centers with d'=d/(d,k)≤L^B and |β|≤L^J/X, all three principal approximations follow from ordinary Siegel–Walfisz and partial summation. These narrow arcs lie in the short major preimage for X large, since |k|Q/X≤X^{ε−δ}; they are disjoint. The complete numerator sum yields the classical coefficient μ²(d)μ(d')c_d(N)/(φ(d)^2φ(d')). One can extend in d' past L^B with arbitrary-log reserve: for primes outside k the weighted absolute coefficients cost at most (p−1)^−2, and Rankin with weight (d')^{1/2} has a convergent Euler product there; primes dividing k contribute factors at most 1+O(1/p), with product at most a fixed log power (indeed bounded by a fixed power of loglog X). Unlike bounding a tail in d by |k|, this bound stays small for polynomial powers of 2. Complete the real integral by rapid decay in the long v models, leaving the true V_u(−kβ). Fourier inversion evaluates it as XQ∫w∫u, since g=1 in a fixed neighborhood of reflected supp(w) and |k|Q/X=o(1). This yields the exact claimed S_k (parity zero for odd k independently). Dependence on bounded fixed smooth derivative norms for u is uniform.

## The new signed positive sector

In the genuine centered prime-q block of the existing note, for |k|≤X^ε the two mixed terms and lattice term still sum to −X∫w+O_A(XL^{-A}) per q, since kq/X=o(1), ρ_v(q)=1+O_A(L^{-A}), and removing nonunit lattice inputs costs O((X/q+1)L) per term (power-small relative to X). Apply the three-prime evaluation with the bounded smooth weight u(t) log Q/log(Qt) to remove the prime log and normalize by Q. Hence for each such k the centered coefficient has main (X∫w)/Q · (∑prime q u(q/Q)) · (S_k(N)−1), with arbitrary-log X error. For N=2^j and k=±2^s, s≥1, S_k(N)=2∏_{ℓ>2}(1+(ℓ−1)^−3)>2 independently of s. The k with X^{ε/2}≤2^s≤X^ε number εL/(2log 2)+O(1) per sign. Each gives ≍X/L strictly positive actual contribution on this fixed nonzero prime-modulus tranche, hence collectively ≍X, with no cancellation claim for the complementary offsets, no claim after an extra noncommuting product-conductor filter, and no information on k=0 or Goldbach positivity.

### Paired positive reserve for every even target

For even N put m(N)=∏_{3≤ℓ≤13, ℓ prime, ℓ|N}ℓ, a fixed bounded odd cofactor. Choose k=m(N)2^s in [X^{ε/2}, X^ε/2] (a margin ensures k+1≤X^ε). In the genuine singular series the 2-factor is 2. The 3-factor is 3/2 when 3|N (in k) and 9/8 otherwise (outside k), so is ≥9/8. Every other odd prime ≤13 contributes at least 1 by the same case split. Every remaining ℓ>13 contributes at least 1−(ℓ−1)^{-2}; bounding the product below by the telescoping product over **all** integers n≥13 gives 12/13. Thus S_k(N)≥(2)(9/8)(12/13)=27/13=2+1/13 uniformly.

Pair each positive even alias k with its actual odd neighbor k+1. All p,p′,q in these fixed interior true-prime windows are odd for sufficiently large X, so R(N+(k+1)q)=0 exactly. Its remaining centered terms still give −X∫w+O_A(XL^{−A}) for literal q uniformly because (k+1)q=o(X); unlike the even analysis, no short-window or arithmetic assumption on k+1's odd cofactor is required. Apply identical original positive smooth prime-modulus weight u(q/Q)/Q for both members of each pair. The pair has actual main (X∫w)/Q · (∑prime q u(q/Q)) · (S_k(N)−2), bounded below by a positive constant times X/L, with arbitrary-log X absolute error. The ⌊(ε/(2log 2))L⌋+O(1) dyadic exponents yield disjoint pairs: different even offsets differ by ≥2 and the odd neighbors are distinct. Summing errors with A>2 proves a positive ≫X true signed chamber for every even N, already paying an equal number of genuine neighboring negative aliases. This is a partial selection before any additional noncommuting conductor cut, not a bound on the remaining full centered expression.

### The entire odd-offset debit on the prime-modulus tranche

For comparison with the subset just paid, the odd-offset sum itself can be evaluated over **all** offsets, without a hypothesis about prime progressions at polynomial moduli. Use the unit lattice centered sequences \(B_{v,q}\) and \(\Theta_v,\rho_v(q)\) of the [small-alias note](DirectGoldbachPrimeModulusSmallAliasCancellation.md). For odd prime \(q\asymp Q\) with \(q\nmid N\), summing over all odd \(k\) means \(x+y\equiv N+q\bmod 2q\). The true prime–prime part is identically zero. In a mixed term a true prime \(x\) fixes a unique even lift of \(y\) modulo \(2q\); this is a unit modulo \(q\) unless \(x\equiv N\bmod q\). By smooth lattice Poisson summation at spacing \(2q\), its mass is \(X\int v/(2q)\) up to arbitrary power accuracy. For the lattice–lattice term each of the \(q-2\) admissible unit residue pairs has exactly two parity lifts at modulus \(2q\). Consequently the full odd-offset sum, before multiplying by the delta weight \(c_Q C_{q/Q}/Q\), is
\[
 -\frac{\Theta_g(\Theta_w-\Theta_w(N;q))+
        \Theta_w(\Theta_g-\Theta_g(N;q))}{2(q-1)}
 +\frac{\Theta_w\Theta_g(q-2)}{2(q-1)^2}
 +O_A(X^{-A}).
\]
Here \(\Theta_v(N;q)\) is the true weighted prime count at that residue. The uniform summed Poisson error follows by taking enough derivatives, since \(q\asymp X^{1-\delta}\). For the at most one such prime divisor \(q\mid N\), substitute \(q-1\) for \(q-2\) in the last term and \(\Theta_v(N;q)=0\); the same estimate below holds. The elementary bound \(\Theta_v(N;q)\ll(X/q+1)L\) now gives
\[
 \sum_{k\ {\rm odd}}(B_{w,q}*B_{g,q})(N+kq)
 =-\frac{\Theta_w\Theta_g}{2q}
     +O\!\left(\frac{X^2L}{q^2}\right).
\]
Thus for a fixed nonzero positive smooth prime-modulus weight the full odd debit after normalization has size comparable to \(X^2/(QL)\), much larger than \(X\). The corresponding even aliases cannot be omitted. It is their cancellation with this known negative mass, including the desired target, that matters for a complete lower bound. The positive paired subset above accounts for only the stated selected neighbors.
