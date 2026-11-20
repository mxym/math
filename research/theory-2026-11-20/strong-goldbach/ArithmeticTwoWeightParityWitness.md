# An arithmetic parity witness for the two low-factor weights

The idea of removing one entire Liouville parity while preserving sieve divisibility data is Selberg's classical parity example; compare [Friedlander–Iwaniec on the asymptotic sieve](https://arxiv.org/abs/math/9811186), [their historical discussion, §2](https://msp.org/ent/2022/1-1/ent-v1-n1-p02-p.pdf), and [Tao–Brady's exposition of the more general parity obstruction](https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/). The point here is the specific **proved, target-dependent arithmetic model, progression ranges, and numerical values for W₂,W₃**, not priority for the parity principle.

Write L=log N, z=exp(L^{1/10}), P(z)=∏_{r≤z} r, c_z=P(z)/φ(P(z)) and λ(n)=(−1)^Ω(n) (completely multiplicative, counting multiplicity). For each even target set

    b_N(n)=c_z 1_{(n,P(z))=1} (1+λ(N−n)),       1≤n<N,
    a_N(m)=b_N(N−m),                             1≤m<N.                    (1)

These are nonnegative model weights on **integers**, not indicators or log weights of actual primes. In particular, n may be composite; a_N vanishes identically on every prime m. Define model statistics by replacing the log weight of the prime n=N−m in QuadraticLowDegreeReduction.md by a_N(m), including all 1≤m<N. The factors of squarefree m, when the statistic imposes a specified factor count, are ordinary, genuine prime factors.

For every fixed ε>0, A>0 and C≥0, uniformly in even N,

    Σ_{d≤N^{1−ε}} τ(d)^C max_{0≤X≤N}
      |Σ_{m≤X,d|m}a_N(m) − X·1_{(d,N)=1}/φ(d)| ≪_{ε,A,C} N/L^A.          (2)

There is in addition an ordinary Bombieri–Vinogradov-type property for the *reflected candidate* n (not merely the special residue n≡N mod d): for every fixed 0<ε<1/2,

    Σ_{q≤N^{1/2−ε}} max_{(b,q)=1} max_{0≤X≤N}
      |Σ_{n≤X,n≡b mod q} b_N(n) − X/φ(q)| ≪_{ε,A} N/L^A.                  (3)

These are distinct statements. In (3) no exact square-root logarithmic endpoint, level beyond 1/2, actual primality of n, or parity-sensitive Type-II bilinear axiom is claimed.

For symmetric nonnegative continuous G on factor-log space supported away from zero and fixed k≥1, one has
   
    [L/(NS(N))] Σ_{m squarefree, ω(m)=k} a_N(m) G((log r)/L:r|m)
        → (1+(−1)^k) I_k(G),                                             (4)

with the simplex integral and its 1/k! convention from SixPrimeNegativeSector.md; for k=1 this is G(1). (4) is an **asymptotic in this arithmetic model** for fixed k, not a heuristic. In particular after justifying the semiprime coordinate face below,

    R_model = 0,        W₃_model = 0,        W₂_model/(NS(N)) → 1.        (5)

The proposed upper threshold for W₂+W₃ is 1.11(½+log 2−π²/24)<.869. Hence (2),(3), together with all the fixed-degree, off-coordinate-face bounds with constant 4 in the actual comparison, cannot by themselves prove that upper threshold: even ranks here have density exactly 2 rather than 4, odd ranks zero, and nevertheless the desired upper comparison fails. This is **not** a counterexample to Goldbach, to any estimate specifically for genuine primes, or to the distinct twisted research hypotheses, and it does not purport to model every possible Chen switching input.

## 1. Liouville in small-average moduli, including all prefixes

Use the standard consequence of [Granville–Shao, Theorem 1.1(b)](https://arxiv.org/abs/1706.05710) that for fixed γ>0, any H>0 and X≥3,

    Σ_{q≤X^{1/2−γ}} max_{(c,q)=1} max_{U≤X}
       |Σ_{v≤U,v≡c mod q} λ(v)| ≪_{γ,H} X/(log X)^H.                    (6)

Here λ and its Dirichlet-convolution inverse μ² are both in their class C (their logarithmic-derivative coefficients at prime powers have absolute value log r); λ is −1 on primes so the restriction-to-primes BV input is classical, and its Siegel–Walfisz criterion follows from the standard zero-free/Siegel–Walfisz estimates for its character series L(2s,χ²)/L(s,χ) (the constants need not be effective). To pass from their discrepancy to the *raw* sum in (6), the coprime total has negligible mass: by inclusion-exclusion and complete multiplicativity it is Σ_{e|rad(q)} Σ_{j≤U/e}λ(j), since μ(e)λ(e)=1 on squarefree e, and the ordinary PNT for Liouville has error O(y exp(−c√log y)). At any U≥X/log^B X, all relevant U/e≥X^.49 for large X, uniformly here. Sum the divided errors using Σ_{q≤X} (1/φ(q))Σ_{e|q}1/e≪(log X)^{O(1)}. For maximal prefixes, apply the fixed-cutoff theorem with arbitrarily large log savings to a grid of O(log^B X) equal-length cells covering [0,X]. All positive endpoints are ≥X/log^B X and q≤U^{1/2−γ/2}. Going from an endpoint to an intermediate U costs at most X/(q log^B X)+1 per q since |λ|≤1; the same bound from the zero endpoint covers small U. Choose B large in terms of H. One can insert τ(q)^C in (6) at the cost of raising H before applying it, by Cauchy–Schwarz and the trivial maximum X/q+1 in the second bracket. These reductions are used only with fixed positive exponent slack.

## 2. Main terms and errors from the short Bonferroni expansion

Take an even J with J=L^{1/20}+O(1), and Y=z^J=exp(O(L^{3/20})). The indicator 1_{(n,P(z))=1} is bracketed by its alternating divisor expansions of orders J−1 and J, and their difference is Σ_{s|n, s|P(z), ω(s)=J}1. Every modulus s is at most Y=N^{o(1)}. Harmonic mass of the terminal layer is at most

    [Σ_{r≤z}1/r]^J/J! ≪_H L^{−H}                                         (7)

for arbitrary fixed H by Stirling. This remains true with 1/(r−1) at odd primes. Finite unsigned counts in a single reduced linear progression can be modeled by length divided by its modulus with O(1) error per s, hence O(Y) total per starting modulus. The same terminal layer bounds the error in using a Bonferroni sum against the signed λ, since |λ|≤1. We use c_z≪log z and freely increase H.

For (2), first take (d,N)=1, K=N/d≥N^ε and m=dk. For any prefix k≤X/d, the unweighted rough indicator of N−dk has main (X/d)∏_{r≤z,r∤d}(1−1/r) up to O_H(KL^{-H}+Y) by (7), CRT and the elementary product version of Bonferroni. If s shares a prime with d, there is no admissible k. For the tilted sum, factor out λ(d), take the truncated expansion and let g=(s,N). Since s is squarefree and (s,d)=1, the single progression k≡d^{-1}N mod s may force g|k, but then k=g v and v is in a **reduced** class modulo s/g. Its maximal prefix length is K/g≥K/Y≥N^{ε/2}; for s/g≤Y, (6) is therefore uniform. Summing (6) at each g≤Y dividing rad(N), with the fixed g now permitting at most one s=g q per q, gives total ≪ K L^{-H}Σ_{g|rad(N)}1/g ≪ K L^{−H}log L (adjust H freely). The unweighted terminal-layer cost applies as above. Thus after multiplying by c_z the main is (X/d)∏_{r≤z,r|d}(1−1/r)^{-1}. Replacing it by X/φ(d) introduces relative error ≪Σ_{r|d,r>z}1/r≪L/z. All errors sum as claimed, including τ(d)^C, by the standard divisor harmonic moment bounds and N^{1−ε}Y=N^{1−ε+o(1)}.

If (d,N)>1 and has a prime r≤z in common, every N−dk is divisible by this r and the model sum is identically zero. For the remaining noncoprime d, there is a common prime r>z. Bounding a_N≤2c_z, their total (including prefixes, whose target main is zero) is

    ≪_C c_z N Σ_{r|N,r>z} r^{-1} (log N)^{O_C(1)} ≪_C N L^{O_C(1)}/z.

Indeed #multiples m≤N of d is ≤N/d; use τ(r v)≤2τ(v) and sum over d=r v. This proves (2) including all prefixes, without supposing the progression is reduced where it is not.

For (3), fix q≤Q=N^{1/2−ε} and a reduced residue b mod q, apply the same expansion to n≡b mod q. Only (s,q)=1 contributes. Its unweighted main is (X/q)∏_{r≤z,r∤q}(1−1/r), with error O_H((N/q)L^{-H}+Y). After scaling it is again X/φ(q) up to a relative O(L/z). For the signed term put h=(q,N−b), g=(s,N). The CRT condition on m=N−n forces hg|m since (q,s)=1. Write m=hg v. The class of v modulo (q/h)(s/g) is reduced, including when q is nonsquarefree (if p^e|q with valuation f<e in N−b, dividing by p^f leaves a unit; if f≥e no p remains from q). We can use the maximum of two prefixes in (6) of length Z=N/(hg) to handle [N−X,N]. Drop restrictions with positive costs, majorize the maximum over possible h by summing h|q, and then fix h≤Q, g|rad(N), g≤Y. The remaining pairs q'=q/h, s'=s/g yield each u=q's' at most τ(u) times, with

    u ≤ QY/(hg) ≤ Z^{1/2−ε/2},     Z ≥ N/(QY) ≥ N^{1/2+ε/2}

for all sufficiently large N. Thus the weighted version of (6) bounds their aggregate at each h,g by O_H(N L^{-H}/(hg)). Summing h and g costs only powers of log N. The O(Y) CRT errors summed over q have size O(QY), and all log losses from c_z are absorbed; this proves (3). Omitting the open endpoint n=N or m=N affects these estimates at most negligibly.

## 3. Computation on real prime-factor boxes

For (4) first choose a fixed factor box with all r_i>N^δ, δ>0, and write A_box for its ordinary unrestricted count of squarefree products with those factor ranges, counted once. See [Liu–Park–Song, Theorem 3.2](https://people.math.harvard.edu/~pspark/boundedgaps.pdf) and §1 of SixPrimeNegativeSector.md for the genuine products' BV estimate and ordinary PNT simplex measure. All r_i>z. If a Bonferroni modulus s has a prime factor in common with N then no product in this box can satisfy m≡N mod s. For every remaining s, m is coprime to s throughout this box. Consequently the distribution theorem supplies A_box/φ(s) as main term, with total error ≪_H N/L^H over s≤Y, which is below the available distribution level. Bonferroni with local factors 1/(r−1), r∤N, and (7) imply the unweighted count of the surviving products is

    A_box V_N(z) + O_H(N/L^H),       V_N(z)=∏_{r≤z,r∤N} (1−1/(r−1)).

Since N is even the factor r=2 is not present. Comparing local factors, c_z V_N(z)=S(N)[1+O((L+1)/z)], because the missing infinite nonsingular tail is O(Σ_{r>z}r^{−2}) and Σ_{r|N,r>z}1/r≪L/z. On each squarefree box 1+λ(m)=1+(−1)^k is constant. Thus PNT for the ordinary A_box, followed by finite partitions for continuous G as in the six-factor note, proves (4).

At k=2 use G=x₁x₂. The omitted face P⁻(m)≤N^δ has scaled mass O(δ)+o(1) uniformly for each fixed δ<1/5: omit m≤N^.99 trivially and write m=s r with s the small prime and r≥N^{.99−δ}. Sieve r for r prime up to w=N^.001 and for N−sr rough up to z<w; the elementary two-linear-form upper sieve on the interval of length N/s gives O(S(N)h(s)N/(s L log z)) choices, h(s)≤2. The checks are the same as for the two-prime bound in SixPrimeNegativeSector.md, with different sieve heights: at primes ℓ≤z the two forbidden residues coincide when ℓ|N, with the usual factor (ℓ−1)/(ℓ−2); at ℓ=s∤N only the residue r≡0 is forbidden. If ℓ=s|N and s≤z there is no contribution. For z<ℓ≤w there is only the condition on r. Treat ℓ=2 separately. The CRT additive remainder is negligible compared to the main bound since N/s≥N^{.8}. Multiplying by 2c_z cancels the log z density; since LQ₂≤log s, the normalized bound is ≪Σ_{s≤N^δ}(log s)/(sL)≪δ. Hence (4) extends to this G. As I₂(x₁x₂)=1/2, W₂_model/(NS)→1. Odd k, including primes and k=3, carry zero weight identically. This proves (5).

The real-prime factor-box BV estimates enter here on the unrestricted product side; no surrogate has been promoted to primality on the reflected side. Any successful proof of the specified upper comparison for real primes must use something not forced by the simultaneously exhibited properties (2)–(4).
