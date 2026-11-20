# What an exceptional zero would do to the two genuine Goldbach weights

This is an application of the proved exceptional-character estimate of [Friedlander–Iwaniec, *Exceptional zeros, sieve parity, Goldbach* (2022), Proposition 11.1 and the improved error immediately following it](https://msp.org/ent/2022/1-1/ent-v1-n1-p02-p.pdf), **not** their heuristic pointwise Appendix. We do not assert that any such zeros exist. The conditional effect is on genuine prime weights; it is not another synthetic sequence.

Use n for an even additive target, S(n) for the usual Goldbach singular series and R(n) for its actual ordered prime-prime log weight. Use W₂,W₃ from QuadraticLowDegreeReduction.md. Suppose there is a sequence of real primitive characters χ of conductors q→∞, each having a real zero β such that

    d=(1−β)log q→0.     Take V=d^(−1/2), X=q^V, e=χ(−1).

For any restriction E on even n write

    M_E(U) = [Σ_{n even, E} U(n)e^(−n/X)] / [Σ_{n even, E} nS(n)e^(−n/X)].

Put c₂=1/2 and c₃=log 2−π²/24. Then, along this sequence,

    M_{q|n}(R)=1+e+o(1),
    M_{q|n}(W₂)=c₂(1−e)+o(1),    M_{q|n}(W₃)=c₃(1+e)+o(1).                 (1)

More generally for each proper divisor D|q all three averages on D|n alone have their unmodified values 1,c₂,c₃, respectively, up to o(1), uniformly in D. In particular if T=φ(q)/φ(D)>1, subtraction gives

    M_{D|n, q∤n}(R)=1−e/(T−1)+o(1),
    M_{D|n, q∤n}(W₂)=c₂[1+e/(T−1)]+o(1),
    M_{D|n, q∤n}(W₃)=c₃[1−e/(T−1)]+o(1).                               (2)

The errors stay o(1) since T, when greater than 1, is an integer ≥2. Neither (1) nor (2) is a pointwise asymptotic on that family. Both use weighted averages of ratios with positive weights nS(n)e^(−n/X).

Consequences. Along arbitrarily close **odd** exceptional characters, (1) forces limsup W₂/(nS(n))≥1 on even targets divisible by the corresponding conductors. The same is true for **even** exceptional characters with 4|q or 3|q, now on the complementary family in (2): choose D=q/2 if 4|q, or D=q/3 if the odd prime 3 divides the primitive quadratic conductor (its odd part is squarefree). In both cases T=2. All such target sequences can be taken to tend to infinity; the mass of bounded n is negligible. Thus any uniform W₂+W₃ upper strictly less than 1 in these units already excludes these corresponding exceptional-zero sequences, since W₃≥0. In particular this applies to the proposed 1.11-reference joint upper. The argument does not exclude all even conductors prime to 6 using that threshold. Nor does the existence of a zero or a conditional zero-density effect refute binary Goldbach: small normalized representation counts need not be zero.

## 1. Put the kernels in the form of the primary theorem

For an odd squarefree m of rank j=2,3, let t_i=log r_i/log m, sorted increasingly, and define a_j(m)=(log m)Q_j(t), zero otherwise, where

    Q₂(a,b)=ab,            Q₃(a,b,c)=2ab−(a+b−c)_+²/2.

Set a₁(m)=log m on odd primes, zero otherwise, and b(p)=log p on primes. FI work with the prime log weight on squarefree support; in any version using von Mangoldt one can remove proper powers in the smoothed sums at cost O(X^{3/2+o(1)}), negligible even after multiplying by q=X^{o(1)}. Restricting b to odd primes changes the sums by O(X), likewise negligible. Define F_j(n)=Σ_{m+p=n}a_j(m)log p for odd p. Then F₁=R at all even n>4, with the harmless target 4 omitted. Since Q₂≤a, 0≤Q₃≤2ab≤2a, FI condition (7-1), |a_j(m)|≪log r for every r|m, holds literally on fixed-rank squarefree support. Their (8-1),(8-2) hold with the inner convolution coefficient supported at 1. On these supports μa_j=(−1)^j a_j and μb=−b.

The ordinary prime number theorem gives, as Y→∞,

    Σ_{m≤Y} a_j(m) = (c_j+o(1))Y,     c₁=1;
    A_j(X,1)=Σ_m a_j(m)e^(−m/X)=(c_j+o(1))X,   B(X,1)=(1+o(1))X.           (3)

For j=2,3 the usual prime-factor boxes on the log-simplex give the symmetric integral I_j(Q_j) off faces (SixPrimeNegativeSector.md, §1); the simplex constants are evaluated in QuadraticLowDegreeReduction.md. At m≤Y/log^B Y the contribution is O(Y/log^B Y) by FI Lemma 7.3. Above this cutoff log m/log Y→1 uniformly, justifying conversion of its log coordinates and prefactor. To check the remaining faces, put L=log Y, let s≤Y^δ be the smallest prime and m>Y^.9. For rank two a₂≤log s and the larger prime has ≪Y/(sL) choices. For rank three write s≤t≤u; here a₃≤C log s log t/L and the largest prime u has ≪Y/(stL) choices since u≥Y^.3. Using Σ_{p≤y}log p/p≪log y shows in each case a total O(δY) uniformly for 0<δ<1/10. This also permits omission of the even prime. Partial summation using the linear mass bound yields (3).

## 2. Multiple of conductor and proper divisors

FI Prop. 11.1 takes a squarefree almost-prime coefficient a with their (7-1), and a convolution b with their (8-1),(8-2). Specifically when b is the prime log weight, they state after (11-3) that the error is O(ηX²), **not** the O(ηX²log X) for general b. By their (11-4), for fixed rank r≤3,

    |η| ≪ (Vd+1/V)(log V)^r = o(1).

Their (11-1) gives, for j=1,2,3,

    φ(q) Σ_{q|n} F_j(n)e^(−n/X)
      = A_j(X,1)B(X,1)+ e A_j(X,μ)B(X,μ)+o(X²)
      = [1+e(−1)^{j+1}] c_j X²+o(X²).                                  (4)

The coefficients a_j,b are supported on odd numbers after the negligible p=2 removal, enforcing n even.

For a proper divisor D|q, exclude first summands m,p with (mp,q)>1. On the remaining units, use orthogonality modulo D: inflate every character modulo D to a character modulo q. The exceptional χ, being primitive of conductor q, does **not** occur. FI (9-3) with their inner convolution argument h=1 bounds the sum of the *absolute values* of the B(X,ψ) over **all** nonprincipal nonexceptional ψ modulo q by O(Xd). A restriction to the inflated subset preserves this bound; |A_j(X,ψ)|≪X by (3). The principal restricted terms are A_j(X,1)+o(X) and B(X,1)+o(X), by FI (9-10) and the fact that the omitted prime mass Σ_{p|q}log p≤log q. Therefore the q-coprime portion has size [c_j+o(1)]X²/φ(D).

Here is a direct check of removing the restriction, uniform in D. Terms p|q have total O(X log q) even without the congruence, which is negligible after multiplication by φ(D)≤q=X^{o(1)}. If (m,D)>1 and D|m+p then p|D, already covered. For (m,D)=1 but (m,q)>1 use Brun–Titchmarsh and partial summation in the reduced residue p≡−m mod D to bound Σ log p e^(−p/X) by O(X/φ(D)), uniformly: below X^.5 use the trivial X^.5 log X, above X^.5 log(y/D)≫log y, since D=X^{o(1)}. By (9-10), Σ_{(m,q)>1}a_j(m)e^(−m/X)≪ X(loglog X)^r/log X=o(X). This proves

    φ(D) Σ_{D|n}F_j(n)e^(−n/X) = [c_j+o(1)]X².                           (5)

In (4),(5), the error estimates have the relative modulus scale required for these rare progressions. A total imbalance of primes between the two signs of χ alone would not suffice.

## 3. Transfer to target-dependent weights; normalize

For each term of F_j(n), j=2,3, the corresponding term of W_j(n) is precisely (log m/log n) times as large, by degree-two homogeneity. This is exact apart from the harmless p=2 term (total over target O(X) up to log factors by (3)). To pass to (4),(5), fix δ>0. For n>X^{1+δ}, exponential decay gives o(X²/q) by (3) for the two marginal sums and a factor exp(−X^δ/2). For m<X^{1−δ} the unrestricted loss is O(X^{2−δ}) by (3), again o(X²/q). On the remaining pairs the relative discrepancy is ≤2δ/(1+δ). By the nonnegativity and bounded normalized means (4),(5), first taking the sequence limit, then δ→0, gives o(X²/φ(D)) error including D=q. This is an absolute normalized statement also when the dominant parity gives zero main term.

For completeness one can normalize the singular mean without invoking a uniformity convention in an averaged Hardy–Littlewood conjecture. Write H=lcm(2,D), g(k)=μ²(k)∏_{ℓ|k}(ℓ−2)^{-1} for odd k, zero for even k. The local product gives S(Ht)=S(H)Σ_{k|t,(k,H)=1}g(k). Consequently the denominator on D|n is

    [X² S(H)/H] Σ_{(k,H)=1} [g(k)/k] K(Hk/X),
    K(u)=u²e^{-u}/(1−e^{-u})².

Now 0<K≤1, K(u)→1 at zero, and Σg(k)/k converges by its Euler product. Since H≤2q=X^{o(1)}, replacing K by 1 has uniform o(1) error in the sum, whose full mass is ≥1. Directly comparing Euler factors gives

    [S(H)/H] ∏_{ℓ∤H}(1+1/[ℓ(ℓ−2)]) = 1/φ(H) = 1/φ(D).

Thus the denominator is (1+o(1))X²/φ(D). Combining this with (4),(5) and subtracting the nested sets proves (1),(2).

The prime-prime dichotomy has a stronger prior pointwise formula in [Matomäki–Merikoski, Theorem 1.4 and Corollary 1.2](https://arxiv.org/pdf/2112.11412). The additional use here of the FI mechanism is for these exact semiprime/triprime weights and for their comparison across conductor strata, not a new assertion of their exceptional-zero mechanism. In particular the uniform fixed-margin two-weight strategy asks more than single-representation existence.
