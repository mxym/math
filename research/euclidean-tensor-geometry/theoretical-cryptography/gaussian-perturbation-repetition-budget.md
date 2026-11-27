# Sharp repetition budgets for Gaussian perturbation amplification

[Peikert–Regev–Stephens-Davidowitz, §3](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) amplify an average single-call success probability by repeatedly perturbing the same Gaussian input. The calls are independent conditioned on that input, not independent unconditionally. Corollary 3.2 and Proposition 3.3 give a sufficient o(1) correlation for a polynomial repetition budget and negligible failure. Here we pin down the worst all-failure probability as a function of the budget, success mass, and correlation in that statistical step. This is not a new Gaussian isoperimetric inequality, a decoder, or a statement about a concrete oracle or scheme.

The finite extremality comes from the classical Borell rearrangement (see [Kindler–O’Donnell–Witmer, Theorem 3.2](https://www.cs.cmu.edu/~odonnell/papers/continuous-most-informative-function.pdf); [Mossel–Neeman](https://arxiv.org/abs/1307.8082) treat multivariate forms). Asymptotics at zero threshold and lower-tail orders for related Gaussian maxima are in [Theisen–Klusowski–Mahoney](https://proceedings.mlr.press/v130/theisen21a/theisen21a.pdf) and [Lopes–Yao](https://arxiv.org/abs/1809.08539). The conclusions below address the moving threshold for rare success, the transition to clustered successes from the opposite tail, the change in the worst-case polynomial budget, and the full range of standardized cross-covariances.

## 1. Exact bound including anisotropy

Let X be standard Gaussian in R^d. In m repetitions, conditional on X, take independent standard-marginal Gaussian vectors Y_i, possibly different dimensions and cross-covariances C_i=E[Y_i Xᵀ]. Conditional on all these vectors, success bits are independent and have probabilities g_i(Y_i), with 0≤g_i≤1 and E g_i ≥p, where 0<p<1. Write ρ=max_i ||C_i||₂, s=sqrt(1-ρ²), u=Φ^{-1}(1-p) for the standard normal CDF Φ. Let M_m be the maximum of m independent standard normals, and Z another standard normal independent of M_m. Then the probability of no success is at most

    F_m(p,ρ) = P(ρ Z + s M_m < u) = E_Z [Φ((u-ρ Z)/s)^m],

where the integral is interpreted by continuity at ρ=0 or 1. At 0 the answer is (1-p)^m, and at 1 it is 1-p. The bound is sharp for every p,ρ,m, already in one dimension with all calls testing the same halfspace of Gaussian mass p. For a single repeated cross-covariance, equality in the abstract model can use its top singular direction. With different matrices the upper bound need not be achieved for those fixed matrices if their directions differ. The bound is sharp over the stated class.

**Derivation.** For isotropic correlation ρ, let W(x)=E[g(Y)|X=x]. Let A be a level event defining E[(W-c)_+]=E[1_A(W-c)]. For Gaussian measure a of A, Borell bounds E[1_A(X)g(Y)] by the probability of parallel equal-orientation halfspaces with masses a and p. To extend the indicator-set form to fractional g, integrate over level sets of g and use concavity of the Gaussian two-halfspace probability in the second mass: its derivative at mass b is Φ((Φ^{-1}(a)-ρΦ^{-1}(b))/s). Optimizing in a gives E[(W-c)_+] no greater than for g equal to a halfspace. The means coincide, so the same bound holds for every convex function of W, by integrating positive-part functions and adding an affine term. In particular apply it to (1-W)^m. If E g exceeds p, compare the corresponding nested halfspaces.

For any matrix C with ||C||₂≤ρ and 0<ρ<1, introduce U=ρX+sZ_1 (after padding independent coordinates if necessary) and Y=(C/ρ)U+(I-CCᵀ/ρ²)^{1/2}Z_2, with Z_1,Z_2 independent standard Gaussians. This has the intended standardized joint law, and E[g(Y)|X] is the isotropic operator applied to the bounded function E[g(Y)|U]. If C reaches the norm bound, the second stage adds no noise in a maximizing left singular direction, giving the equality example for a repeated matrix. Conditional independence gives E[prod_i(1-W_i)] for arbitrary calls. Hölder and the single-function bound on each m-th moment give the exact upper bound. The endpoints follow directly (or by continuity and those examples). For the halfspace example, the event that every draw fails means that the common coordinate plus the noisiest independent draw is below u, giving the maximum formula. Under positive common correlation the failures are not generally bounded by (1-p)^m.

This sharpness is over bounded statistical success functions with the given mass, not over all constraints on valid lattice outputs. In the GDP proof it bounds the event of no valid response among the perturbed attempts. Any separate correctness condition for selecting an output or for unique lifting is not assessed here.

## 2. Quantitative asymptotics

Write v=Φ^{-1}(1-1/m) for m>2, and let G denote a standard Gumbel random variable, with distribution P(G≤x)=exp(-exp(-x)). Standard normal tail ratios give W_m=v(M_m-v)→G in distribution. The exact maximum formula becomes

    F_m = P((ρv/s) Z + W_m < v(u/s-v))          (0≤ρ<1).

This yields a continuous crossover: if ρv/s→γ∈[0,∞) and v(u/s-v)→x, then F_m→P(γ Z+G≤x), with independent Z,G. In particular a Gaussian common offset at correlation order 1/sqrt(log m) changes the pure Gumbel profile. If ρv/s→∞ and (u-sv)/ρ tends to x (allowing ±∞), then F_m→Φ(x).

For fixed ρ∈(0,1), suppose u,v→∞ and define λ=s/(ρv). On the small-failure side, d=(s v-u)/ρ→+∞, and automatically r=dλ is bounded (since u≥0 eventually). Then

    F_m ~ barΦ(d) Γ(1+r),        barΦ=1-Φ.

The assertion with r varying means the ratio to the right-hand side tends to one. On the intermediate small-success side, d=(u-sv)/ρ→+∞ and limsup r<1 for r=dλ; there

    1-F_m ~ barΦ(d) Γ(1-r).

On the other small-success side and across the onset of clustering put b=s u-v. If b→+∞, then 1-F_m~m p. If |b|=o(v), including b→-∞ slowly and all bounded b, then

    1-F_m ~ m p Φ(b/ρ).

The latter formula resolves the regime where the intermediate Gamma factor approaches its pole and a bounded positive r-margin would not apply. In particular, at b→0 only about half of the union-bound mass survives, even though m p tends to zero in that regime.

### Proof of the tail factors

A Gaussian Mills ratio, or integration of the normal hazard, gives m barΦ(v+w/v)→e^(-w) for each fixed w, hence W_m→G. For w≥0, the Gaussian hazard is at least the positive argument, so P(W_m>w)≤e^(-w). For 0≤w≤v², comparing barΦ(v-w/v) with barΦ(v) in the other direction gives P(W_m<-w)≤exp(-exp(w/2)). For w≥v², the argument v-w/v is nonpositive and the bound is

    P(W_m<-w) ≤ 2^(-m) exp(-m (w-v²)²/(2v²)).

The last expression follows from Φ(-x)≤(1/2)exp(-x²/2), x≥0. These estimates yield uniform integrability of exp(B(-W_m)_+) for any fixed B, and of exp(B(W_m)_+) for each B<1. For the negative part integrate the first bound up to v²; the integral past v² is at most a constant times 2^(-m)e^(Bv²)(v/sqrt(m)) exp(B²v²/(2m)), which vanishes since v²=O(log m).

Conditioning on M_m, the small-failure probability divided by barΦ(d) is E[barΦ(d+λW_m)/barΦ(d)]. For fixed w, the integrand tends along r→r_* to e^(-r_*w) since the normal hazard divided by its argument tends to 1 at infinity. For w<0, the ratio is at most exp(λ(d+1)|w|) for large d: the hazard is increasing and bounded by d+1 at argument d≥1. For w≥0 the ratio is at most one. Uniform integrability proves convergence of this expectation to E[e^(-r_*G)]=Γ(1+r_*). The analogous ratio on the small-success side is E[barΦ(d-λW_m)/barΦ(d)]; now a positive exponent acts on the right tail, and the bound limsup r<1 ensures uniform integrability. The Gamma moment is Γ(1-r_*). Compact subsequences give the varying-r equivalents in both cases.

### Proof of the onset of clustering

Given the common coordinate Z=x, let R(x)=barΦ((u-ρ x)/s). Put A_m(r)=[1-(1-r)^m]/(m r), continued as 1 at r=0. The identity

    (1-F_m)/(m p) = E[A_m(R(Z)) | ρZ+s Z_1 ≥ u]

holds for an independent Z_1: conditioning on the first single call succeeding size-biases the law of Z by R. Under that conditioning Z=ρ(u+V)+s N with N standard normal, V≥0 independent of N, and V distributed as the excess of a standard normal above u. Then

    R(Z)=barΦ(v+b-ρN-βV),     β=ρ²/s.

We have uV bounded in probability, by upper-tail ratio estimates. A_m(r) tends to 1 if m r→0 and to 0 if m r→∞; it is decreasing in r because it is the average of 1,(1-r),…,(1-r)^(m-1). If b→+∞, the Gaussian tail at v+b-ρN-βV is negligible compared with barΦ(v) in probability, giving (1-F_m)/(m p)→1. If b has a finite limit the sign of b-ρN changes the ratio abruptly, yielding Φ(b/ρ) asymptotically by dominated convergence.

For the relative estimate with b→-∞, |b|=o(v) implies v∼s u. Choose Δ→0 so that vΔ→∞ and |b|Δ→0 (for example (v|b|)^(-1/2)). On βV≤Δ and ρN≤b-2Δ, mR is o(1) uniformly, so the expectation is at least (1-o(1)) Φ((b-2Δ)/ρ)~Φ(b/ρ). For the upper bound drop βV, which can only increase A_m. The contribution with ρN≤b is at most Φ(b/ρ). For 0<x=ρN-b≤v/2, mR≥exp(vx-x²/2)≥exp(3vx/4), and A_m≤1/(mR). Integrating this contribution over N>b/ρ is at most C φ(b/ρ)/v (write N=b/ρ+y and absorb the factor exp(|b|y/ρ) into exp(-3vρy/4)), where φ is the standard density. Its ratio to Φ(b/ρ) tends to zero by |b|=o(v). For x>v/2 the corresponding contribution is at most exp(-3v²/8), also negligible relative to Φ(b/ρ). This proves the remaining transition regime.

## 3. Polynomial budgets and negligible error

Fix a>0, c>0 and 0<ρ<1, and take p=n^(-a), m=floor(n^c). Then u∼sqrt(2a log n), v∼sqrt(2c log n). The complete logarithmic phase diagram is:

* If c<a s², success 1-F_m~m p. At c=a s² it is asymptotic to m p/2.
* If a s²<c<a/s², then 1-F_m=n^(-((sqrt(a)-s sqrt(c))/ρ)^2+o(1)).
* If c=a/s², then F_m→1/2; if c>a/s², then F_m=n^(-((s sqrt(c)-sqrt(a))/ρ)^2+o(1)).
  
At either equality point the needed centered quantity tends to zero by the O(log log n/sqrt(log n)) quantile remainder. Thus to attain failure exponent B>0 the precise budget exponent is (sqrt(a)+ρ sqrt(B))²/(1-ρ²), with a logarithmic-order guarantee at equality; constants at equality are read from the quantile and Gamma form above. In particular, constant residual correlation suffices for any prescribed inverse-polynomial reliability, but the required repetition exponent grows with that reliability exponent.

For arbitrary sequences ρ_n∈[0,1], with only a single-call success lower bound p≥n^(-a), a uniformly negligible failure bound at some fixed polynomial repetition budget is possible in this statistical abstraction **if and only if** ρ_n→0. For sufficiency take c>a, and choose a fixed η>0 with (1-η)sqrt(c)>sqrt(a). The independent maximum is at least (1-η)sqrt(2c log n) except with superpolynomially small probability (use scalar Gaussian tails); then ρ_n Z would have to be below -Ω(sqrt(log n)) for all calls to fail. This has negligible probability when ρ_n→0, including the independent endpoint. Conversely on any subsequence with ρ_n bounded from below, choose the halfspace mass exactly n^(-a) and use the event Z≤-C sqrt(log n) and M_m≤C' sqrt(log n), where C' is fixed by the polynomial upper bound on m and C is sufficiently larger. The second event has probability at least 1/2 eventually by the Gaussian union bound, and the first is inverse polynomial; their intersection implies all failures. This necessity is black-box sharpness under the single statistical mean premise, not a new worst-case hardness implication.

The adjacent verifier checks finite algebraic repetition identities (26,208 exact checks) and illustrates this phase diagram by one-dimensional Gaussian integrals (142 floating comparisons). It uses no lattice instances, oracle implementations, or decoding code.
