# A coupled critical quadratic sieve on the actual Goldbach polynomial

Let P run through even integers, I=[P/3,2P/3], L=log P, and F=n(P−n).
Let W≥0 be smooth and compactly supported in (1/3,2/3); take W(x)=W(1−x)
when using symmetry between physical rows. Put X=P∫W. Let
S(P)=2∏_{p>2}(1−1/(p−1)²)∏_{p|P,p>2}(p−1)/(p−2).
A prime means a positive rational prime. For a fixed 0<δ≤10⁻⁵ take a smooth
symmetric unimodal probability density ν supported in [−δ,δ]. Define
$$
K(F)=\int\sum_{d\mid F}\mu(d)\big((1+u)\log F-2\log d\big)_+^2\,\nu(u)\,du.
$$
This is one jointly truncated divisor, not two separately truncated sums.

**Theorem.** For every A>0, uniformly along the even targets,
$$
\sum_n W(n/P)K(n(P-n))=8X S(P)+O_{A,W,\nu}(P L^{-A}).\tag{1}
$$
On squarefree F of even rank the summand K(F) vanishes unless F has exactly
two prime factors; for rank two K(F)=4 log p log q. All central rank-two rows
are therefore true prime pairs. On squarefree F of rank three it is
nonnegative, and on every squarefree F of rank five it is nonpositive. These
are exact, even with the fixed positive smoothing width. There is no universal
sign used for rank seven or higher, and no proof that the true prime row is
nonempty.

## Proof of the progression comparison at the actual coupled critical level

Write Z=P/g, where g ranges over squarefree divisors of P. Assign every
prime of d that divides P to g (its single root is n=0 modulo that prime).
Independently assign each remaining prime of d to a (root 0) or b (root P).
Thus d=gab, (a,b)=(ab,P)=1, with coefficient μ(g)μ(a)μ(b). On actual rows
n=gt, one has a|t, b|Z−t and t/Z=n/P. This representation enumerates
residue *classes*, so it counts every divisor once on every physical row.
The CRT model for the weighted t-sum is
$$
\frac{Z}{ab}\int W(x)\int \big((1+u)\log(P^2x(1-x))-2\log(gab)\big)_+^2\,\nu(u)\,du\,dx.\tag{2}
$$
Here and below an empty congruence has zero physical contribution.

We show the total physical sum equals the sum of (2), with error
O_A(P L^{-A}). For g>P^.01 both totals, even absolutely, are negligible:
the physical bound is ∑_{g|P,g>P^.01} (1+P/g)P^{o(1)} using the maximum
divisor bound on F, and the model is bounded by
∑_g (P/g)L^4 (because ab≪(P/g)P^δ). For other g, Z≥P^.99.
The archimedean weight B(x,y) in (2), with y=ab (and without the Z/(ab)
prefactor), vanishes for y>Z P^δ. All fixed-order derivatives in x and
log y are O_{j,W,ν}(L²), uniformly when the weight is nonzero and y≥1.
Indeed it is W(x) log²(P²x(1−x)) times a fixed smooth function of
2log(gy)/log(P²x(1−x)); extend with a smooth lower cutoff outside the
actual argument range. This is where the fixed smoothing is useful.

For ab≤Z/L^B, all nonzero frequencies in ordinary Poisson on the single
CRT residue t mod ab have total O_W(Z L^{4−2B}) per g: integrate three
times in x and sum reciprocal a,b dyadically. Equivalently one can compare
each progression with its integral by bounded variation with error O(L²)
and use ∑_{ab≤Z/L^B}1≪Z L^{1−B}. Take B as large as needed.

For the remaining ab≥Z/L^B, separate dyads a≈M, b≈D (or the reverse),
and all sharp support cuts may use independent subintervals as explained
below. The model is negligible: the longer label, say b, has D≥Z^{.49}.
Every incomplete prefix on that dyad satisfies, uniformly for H≤P³,
$$
\sum_{\substack{b\in J\\(b,H)=1}}\mu(b)\ll_C D L^{-C}\qquad(J\subset[D,2D]).\tag{3}
$$
In fact μ(b)1_{(b,H)=1} = (μ*1_{s|H^∞})(b). For s≤√D use ordinary
Mertens with arbitrary log saving; ∑_{s|H^∞}1/s≪loglog(3H). For s>√D
Rankin at exponent 1/log L bounds the remaining reciprocal mass by
exp(−cL/log L)(log L)^{O(1)}: primes p|H up to L cost at most
exp(O(∑_{p≤L}1/p)); above L use ω(H)≪L and
p^{-1+1/log L}≪1/L. The same proof works with multiplicity powers on a
fixed H; no target-uniform zero-free input is hidden. Apply (3) with
H=aP and partial summation of B(x,ab)/b including the ab-cut. Summing
the short label reciprocally proves the claim. The argument of (3) works unchanged for H≤P^C₀ for any fixed C₀. If b>Z the physical sum
is zero, and (3) still disposes of that part of the model. We may
therefore assume both labels ≤Z in the subsequent physical estimates.

**Short label.** Suppose the shorter label a≤2Z^.05 (interchanging roots
and replacing x by 1−x if needed). Write k=(Z−t)/b. Then
1≤k≪Z^.051 for large P, b=(Z−t)/k≈Z/k, and a|t forces (a,k)=1 and
b≡Z times the inverse of k mod a, a unit class. For each k the sum over
a of the maximal-prefix Möbius progression errors at b-length Y≈Z/k
is O_C(YL^{-C}) even with (b,P)=1. Details: expand 1_{(b,P)=1}μ(b)
by the same convolution as (3). For s≤Z^.03, (s,a)=1 and the classical
[maximal-prefix Möbius Bombieri–Vinogradov theorem, (3.1)](https://arxiv.org/html/2610.20242v2#S3)
applies at Y/s to every a≤2Z^.05, with arbitrary log savings. For s>Z^.03
bound absolute counts per reduced progression by O(Y/(as)+1), still
using (s,a)=1. The reciprocal tail is as in (3); the number of s≤2Y
supported on divisors of P is P^{o(1)} uniformly. For the latter fact
use Rankin at any fixed σ>0 and ∑_{p|P}p^{-σ}=o_σ(log P) by splitting
at any sufficiently large fixed prime, then let σ↓0. The aggregate +1 cost
per k is Z^.05 P^{o(1)}, power-small compared to Y. B((Z−kb)/Z,ab)
has O(L²) variation on each physical b-interval, including the lower
cut ab≥Z/L^B and dyadic restrictions. Partial summation, the harmonic
k-sum and log-many dyads prove negligible total.

**Incomparable polynomial labels.** Use this branch when
M≥Z^.05/2, D≥Z^.55/2, MD≤4ZP^δ and M≤D. Thus M≤Z^.451 and M/D≤Z^−.098
for large P (fixed factors in dyadic endpoints are immaterial). Exact CRT
Poisson has nonzero phases e(hZ bar b/a), up to a smooth factor
e(±hZ/(ab)) when reversing the orientation; reciprocity of inverses gives
this factor identically. Keep |h|≤H₀=ceil(Z^{4δ}). Tails are negligible
with any fixed log saving, since MD/Z≤Z^{2δ} for large P and arbitrarily
many integrations by parts are permitted. The amplitude is Z/(ab) times
the Fourier transform in x of B(x,ab) at hZ/(ab). In logarithmic a,b
coordinates on dyads the amplitude after removing Z/(MD) and its first
derivatives are O(L²(1+|h|Z/(MD))^{O(1)}); more usefully the transform
and its log-derivatives of any fixed order are O_j(L²) uniformly in h by
integration by parts in x, also after inserting the reciprocity phase.
It follows by ordinary one-variable partial summation in the long label
that it suffices to bound every prefix on D≤b≤2D, with a,h fixed.

Here c=±hZ, q=a, (q,Z)=1 and e(t)=exp(2πit). Uniformly in such prefixes,
$$
\sum_{\substack{b\in J\\(b,Pq)=1}}\mu(b)e(c\bar b/q)\ll D Z^{-.003}.\tag{4}
$$
A proof avoiding any prime-modulus restriction is as follows. Put U=Z^.01,
let M₀ be the function μ truncated to arguments ≤U, and use
μ=2M₀−(M₀*M₀)*1+(μ−M₀)*(μ−M₀)*1. The first term vanishes at this
dyad. In Type I the short variable k≤U² has coefficient ≤τ(k). Open
(s,P)=1 for the long ordinary integer by inclusion-exclusion over
v|P. For each (k,qP)=1, the complete periods modulo q have sum c_q(h),
independent of the units k,v,Z, of magnitude ≤(h,q)≤H₀. The remainder
is O(q) per v. Thus the total Type I contribution is
≪D L^{O(1)} H₀/q + U² q P^{o(1)}, both within (4).
For the remaining Type II the two variables k,l both exceed U and have
coefficients bounded by 1 and τ(l) respectively, after absorbing the
unit restrictions. For rectangle lengths K,T and square-summable
coefficients A,B on the units, completion in the two intervening residue
classes gives
$$
\left|\sum A_k B_l e(c\bar k\bar l/q)\right|\le [q(c,q)(1+2K/q)(1+2T/q)]^{1/2}\,\|A\|_2\,\|B\|_2.
$$
Indeed inversion permutes unit residues, the full Fourier matrix with
frequency multiplier c has norm √(q(c,q)), and folding interval
coefficients into residue classes costs at most the displayed
multiplicities by Cauchy. With KT≈D the resulting ratio to D is
≪L^{O(1)}[H₀(q/D+1/K+1/T+1/q)]^{1/2}≪Z^{-.0048}.
The sharp product-prefix cutoff k l≤z may be separated by the standard
truncated Perron identity at the half-integer floor(z)+1/2, Re(s)=1/log Z,
height Z⁵, costing O(L) and error O(Z^{-2}) per dyad by the divisor bound.
There are O(L²) dyads. This proves (4). Summing over h, the shorter
label, and the normalized Z/(MD) prefactor gives
≪Z L^{O(1)} Z^{4δ-.003} per dyad, as required.

**Comparable labels.** In the only remaining case both labels are
≤2Z^.55 and MD≈Z up to the factor Z^{2δ} or a power of L. Use
[Bettin–Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769) for
each nonzero h≤H₀ individually, with a frequency sequence supported at
1 and target numerator θ=hZ; the factor (1+|θ|/(MD))^{1/2} costs at most
Z^{2δ}L^{O(1)}. The two coefficients include their unit masks with P,
and (a,b)=1 is the theorem's own restriction. Mellin inversion in log(ab) of a compact dyadic bump times the Poisson amplitude separates
the coefficients at cost O(L²) in L¹ of the transform, by the derivative
bounds above. For the temporary lower cut ab≥Z/L^B, sharpen or mollify
as in the paragraph below. The bound (before the Z/(MD) prefactor) is
$$
(MD)^{1/2+o(1)}Z^{2\delta+o(1)}\big((MD)^{7/20}(M+D)^{1/4}+(MD)^{3/8}(M+D)^{1/8}\big).
$$
Since MD=Z^{1+O(2δ)+o(1)} and max(M,D)≤2Z^.55, the worst exponent is
.5+.35+.55/4=.9875 before the O(δ) and o(1) losses. Thus summing
over H₀, inserting Z/(MD)≤L^{O(1)}, and summing the dyads leaves a
power saving. We used an existing theorem for nonzero integral θ,
not a fixed-numerator specialization.

To avoid any discontinuity at the border ab≈Z/L^B throughout, use a
smooth cutoff of ab L^B/Z supported above 1 and equal to 1 above 2.
Its derivatives in the logarithmic argument are O_j(1). Its complement
is entirely within the trivially treated region ab≤2Z/L^B. Other sharp
restrictions concern single variables or ordinary intervals in the
switched b-sum. Summing over g uses ∑_{g|P}1/g≪loglog(3P) for the
arbitrary-log terms and at most P^{o(1)} losses in fixed-power savings.
This proves the claimed progression comparison.

## The pole and actual physical signs

Upon summation over residue assignments and changing t/Z=x, (2) equals
$$
P\int W(x)\int 4\sum_{d\le R_x(u)}\frac{\mu(d)\rho_P(d)}d\log^2(R_x(u)/d)\,\nu(u)\,du\,dx,\qquad R_x(u)=(P^2x(1-x))^{(1+u)/2}.
$$
where ρ_P(p)=1 at p|P and 2 elsewhere on squarefree integers.
At s=0 the series ∑ μ(d)ρ_P(d)/d^{1+s} equals
ζ(1+s)^{-2}H_P(1+s), where H_P(1)=S(P).
In Re(z)≥1−c/log L, H_P(z) is holomorphic and ≪(log L)^{O(1)}:
use the absolutely convergent unexceptional Euler factors
(1−2p^{-z})/(1−p^{-z})² for p≥3, the single p=2 factor
1/(1−2^{-z}), and the replacements (1−p^{-z})/(1−2p^{-z})
at odd target primes. The log bounds are precisely as in the Rankin
estimate for (3); finitely many small odd primes have denominators
bounded uniformly away from zero. Mellin inversion with 2 R^s/s³
therefore gives 2S(P)+O_A(L^{-A}) for the inner sum without its 4.
For detail truncate at |Im(s)|=exp(c₁√L) on Re(s)=1/L (absolute
sum ≪L^{O(1)}), shift to Re(s)=−c₂/√L inside the classical zero-free
region, where 1/ζ(1+s) is log-bounded. The double zero at s=0
leaves residue 2H_P(1). Horizontal and left contour errors are
exp(−c₃√L)L^{O(1)}, uniformly for R≈P^{1+O(δ)}. This proves (1).

For F squarefree write x_i=log p_i/log F>0, ∑x_i=1 and m=ω(F).
If m is even pair each divisor with its complement and use symmetry
of ν: the sum equals one half of the alternating finite difference of
(1−2t)²+∫u²ν(u)du at the subset sums t. Its order m annihilates
degrees less than m. For m=2, expansion gives 4(log p₁)(log p₂).
All central n,P−n exceed 1, whence rank two means exactly two genuine
distinct prime summands.

For m≥3 let Y_i be independent uniform variables on [−x_i,x_i] and let
f be the density of the sum of the Y_i convolved with ν. It is smooth,
even, and unimodal: convolution of two symmetric unimodal densities is
symmetric unimodal by layer-cake decomposition into centered interval
indicators, whose convolutions are unimodal. Repeated fundamental theorem
of calculus, or distributional derivatives of t_+², gives
$$
K(F)/\log^2 F=2\left(\prod_i 2x_i\right)f^{(m-3)}(0).
$$
Indeed differentiating t_+² three times gives 2 times the Dirac mass;
odd derivative signs are immaterial in the even density and the even
derivatives have positive prefactor. In particular rank 3 is nonnegative,
rank 5 is nonpositive since f has a maximum at 0; rank 7 has a fourth
derivative, not controlled by unimodality alone.

**Scope.** No claim that all nonsquarefree F have zero K, or that the
sum of ranks ≥7 has a favorable sign. The CRT identity (1) includes
these rows and is not a masked statement. A positive rank-three term
is generally a true prime against a genuine semiprime, not a prime pair.

## Literal hinge, physical squarefreeness, and the remaining signed terms

Put ε₀=10⁻⁵ in all the preceding *exponent bounds*, even when the
density ν has width smaller than ε₀. For clarity, at dyadic boundaries
partition the actual labels at Z^.05 and Z^.55 before dyadization, so
short means min(a,b)≤Z^.05 and comparable means max(a,b)≤Z^.55.
Otherwise the dyadic ranges lie in the incomparable case stated above.
These cutoffs are on individual labels; the y=ab cutoff is smooth.
A harmless factor (log P)^{O(1)} on a label is absorbed by the strict
power margins, as detailed for the squarefree restriction below.

Define the unsmoothed detector
$$
K_0(F)=\sum_{d\mid F}\mu(d)(\log F-2\log d)_+^2.
$$
All the conclusions of (1) and the physical rank signs hold *also* for
K₀. Given any accuracy A, take a smooth symmetric unimodal scaled bump
of width L^{-C}, C>A+10. The archimedean derivative costs in each fixed
order are now fixed powers of L. These are absorbed by every fixed-power
saving above and by increasing the requested arbitrary-log savings in
(3) and the short-label BV estimate. The direct low-product
bounded-variation comparison requires just O(L²), uniformly in C:
the derivative of x₊² is O(L) for the present arguments, even before
smoothing. Equivalently choose the smooth low-product separation after
fixing C. The quadratic hinge is convex with 2-Lipschitz derivative, so
$$
0\le {\mathbb E}\,(s+u\log F)_+^2-s_+^2\le L^{-2C}\log^2 F.
$$
By Cauchy, ∑_{n∈I}τ(n)τ(P−n)≪P L³. Thus replacing the smoothed
kernel by K₀ costs O(P L^{5−2C}) in total variation, also under any
physical submask. The same smoothing argument justifies the rank
statements for K₀ pointwise, or take width↓0 for each fixed F.

**Squarefree first moment.** Independently of W-symmetry, for either
the fixed smooth K or literal K₀, the very same estimate holds with a
physical squarefree indicator:
$$
\sum_n W(n/P)\mu^2(F)K_0(F)=8XS(P)+O_{A,W}(P L^{-A}).\tag{5}
$$
Here is the full residue modification. Because F=n(P−n),
μ²(F)=1_{(n,P)=1}μ²(n)μ²(P−n). On these rows all divisor labels
are coprime to P. First leave 1_{(n,P)=1} unexpanded, write the
remaining factors as square-divisor sums k²|n, l²|P−n, and truncate
k,l≤T=L^{A₁}. The absolute error is negligible for sufficiently
large fixed A₁=A₁(A). In fact the set with any square divisor k² of
a side, k>T, has size ≪P/T+√P; absolute truncated or original
multiplicities (including all d|F) are bounded by
L² τ(n)²τ(P−n)². Cauchy and the standard fixed divisor moments
∑_{m≤P}τ(m)^j≪_j P(1+L)^{2^j−1}, applied also to the reflected side,
give the assertion. In the truncated expansion one may insist
(kl,P)=(k,l)=1; this does not change the sum under the as yet
unexpanded physical unit condition.

Now expand that condition by c|(P,n) with coefficient μ(c) and put
Z=P/c, t=n/c. The cost of c>P^{ε₀/4} is P^{1−ε₀/4+o(1)}
by the divisor bound and the number of multiples, including all
truncated square divisors. Keep c≤P^{ε₀/4}, hence
P^{1+ε₀}≤Z^{1+2ε₀} for large P. Assign d=ab, (ab,P)=(a,b)=1
to the two roots. The short constraints are k²|t, l²|Z−t.
Terms with (a,l)(b,k)>1 have no compatible residue, since (kl,P)=1.
Write a=a₀ a′, b=b₀ b′, with a₀|rad(k), b₀|rad(l), and
(a′b′,Pkl)=1. Actual progressions now have precisely the moduli
$$
M_1=k^2a'\mid t,\qquad M_2=l^2b'\mid Z-t.
$$
They are coprime, including at the powers of k,l, and they are coprime
to Z. The archimedean coefficient still uses *d=a₀b₀a′b′*;
its log differs from log(M₁M₂) only by a constant O_{A₁}(log L)
for each fixed k,l,a₀,b₀. The same proof of the progression
comparison applies with M₁,M₂ as the dyadic labels, while the actual
two independent coefficients on them are respectively μ(a′),μ(b′)
on their required multiples. In detail:

* The local spacing is exactly M₁M₂. The small-product transition
  M₁M₂≈Z/L^B is again smooth; the product on support is at most
  Z^{1+2ε₀}L^{O(A₁)}, which does not change any exponent rail.
  Nonzero h are still truncated at Z^{4ε₀} with arbitrary power-log
  savings. The corresponding model on high dyads uses (3) for the
  long variable b′ (or a′), with the extra unit mask Pkla′ of size
  P^{O(1)}; its length is still ≥Z^.48.
* In the short case M₁≤Z^.05 write j=(Z−t)/(l²b′). Compatibility
  forces (j l²,M₁)=1. Thus b′≡Z times the inverse of j l² modulo
  M₁ and b′≈Y=Z/(jl²), with j≤Z^.052 and Y≥Z^.94. The relevant
  moduli k²a′ are a subset of moduli ≤Z^.05. Expand the unit mask
  (b′,Pkl)=1 as in (3). A smooth-supported divisor s not coprime to
  the modulus has zero contribution in a reduced progression and is
  omitted; otherwise s can be inverted. The product Pkl≤P^{O(1)}
  gives the identical Rankin and counting bounds. Thus the cumulative
  prefix errors over a′ for each j are O_A(Y L^{-A}); logarithmic
  factors from all k,l,a₀,b₀ and dyads are harmless.
* In the comparable case pack the exact individual μ coefficients
  on multiples M₁, M₂ into the two dyadic sequences of Bettin–Chandee.
  Norms are no greater than the full dyadic lengths' square roots.
  In the incomparable case the short modulus is M₁. The long
  Möbius variable is b′, the phase has slope ±hZ times the
  inverse of l² modulo M₁, and the gcd with M₁ is ≤|h|. The
  long dyadic length is M₂/l². Polylogarithmic length ratios leave
  M₁/(M₂/l²)≤Z^{−.097} and the bilinear proof (4) unchanged,
  with fixed extra coprimality Pkl included in Type I by
  inclusion–exclusion (nonunits of M₁ are omitted). Swapping the
  two root labels gives exactly the symmetric other case.

All power savings absorb P^{o(1)} choices when appropriate. The
arbitrary-log errors are O_{A,A₁}(Z L^{-A}) **per c**, not O(P L^{-A})
per c, so ∑_{c|P}1/c≪loglog(3P) suffices. The model main may now
restore the square labels k,l to infinity and all c|P. To check absolute
convergence of this restoration before taking prime products, the
density for root assignments a,b coprime to P with the extra square and c
conditions is at most
$$
\frac{(a,k)(b,l)}{c k^2 l^2 a b}.
$$
The harmonic sums over the squarefree a,b≤P^{O(1)} cost at most
L²·2^{ω(k)+ω(l)} up to a constant (one factor ≤2 per marked prime).
Together with the archimedean O(L²), ∑_{k>T} 2^{ω(k)}/k²≪log(2T)/T
and ∑_{c|P}1/c≪loglog P, this gives arbitrary powers of log saving.
The c-tail above P^{ε₀/4} has a power saving times τ(P).
For each prime, averaging in this restored model is over residues
mod p². In its Mellin series (the unfixed factor d^{-s}, in addition
to density of d|F), the local factors become
$$
\begin{cases}
1-2p^{-1-s}-2p^{-2}(1-p^{-s}),&p\nmid P,\\
1-1/p,&p\mid P .
\end{cases}
$$
Indeed at p∤P, p does not divide F with probability 1−2/p and
divides it exactly once with probability 2/p−2/p², contributing
1−p^{-s} on the latter event. At p|P one must have p∤n for F to
be squarefree. These local factors agree with the original ones at
s=0, and their product times ζ(1+s)² is holomorphic with the same
(log L)^{O(1)} bound on the same contour: the extra generic terms
are absolutely summable there, and the target replacements at p|P
have uniformly bounded logarithmic size by the same prime split.
Thus the *same* double zero and residue yield (5). This is a
signed squarefree localization, not an assertion of small total
variation on the discarded rows for K₀.

**Exact prime leg and signed ledger for K₀.** Let p be prime, m>1
squarefree, (p,m)=1, and 1/2≤m/p≤2. Separating divisors d of m and
p d and then changing d↦m/d in the missing part of the full square gives
$$
K_0(pm)=Q_p(m)-(1+\mu(m))(\log(m/p)_+)^2,\qquad
Q_p(m)=\sum_{d\mid m}\mu(d)(\log(pm)-2\log d)^2.
$$
In fact the omitted short-divisor sum only uses d≤√(m/p)≤√2,
so its only possible label is 1. The full finite difference Q_p(m)
is 4 log p log m for prime m, 8 log a log b for m=ab a squarefree
semiprime, and zero for rank≥3. The entire endpoint correction summed
over true source primes is O(P/L), since it is bounded per prime.
In particular no unknown prime-versus-higher-rank main remains.

For symmetric W, write G for the W-weighted ordered log-prime-pair
sum, T₁₂=∑_{p+ab=P}W(p/P)log a log b over primes and a<b with the
three primes distinct, E₂₃ for minus the actual sum of WK₀ on both
orientations of squarefree semi×triprime rows, and E₇ for the actual
signed sum on squarefree composite×composite rows of odd total rank ≥7.
By the rank signs E₂₃≥0. Combining the pointwise formulas with (5)
gives the unblurred, prescribed-target identity
$$
4G=8XS(P)-16T_{12}+E_{23}-E_7+O_W(P/L).\tag{6}
$$
Any diagonal duplicate true prime or nonsquarefree semiprime pair omitted
from these definitions has at most the negligible indicated contribution
to G (the prime–prime diagonal is a single O(L²) term). No bound on
E₇ sufficient for positivity and no independent lower bound on E₂₃
are inferred. At rank seven alone there are both signs, not a second
unimodality argument. In integer log units take the two legs
(1,11) and (1,1,1,1,8), or (3,9) and (1,1,1,1,8).
Both legs sum to 12, whereas direct subset evaluation gives respectively
−8 and +8. Each sign occurs on genuine physical inputs along even targets:
for every listed exponent a, choose a distinct odd prime in a small fixed
relative neighborhood of Y^a using the prime number theorem. The products
of both legs are then comparable within a factor 2, and the strict signs
survive after division by (log Y)². This is not a count at each target.

**Provenance.** This is a first moment of the classical *coupled*
truncated generalized von Mangoldt weight: at a fixed R the sharp
quadratic expression is eight times the two-form, ℓ=0 weight of
[Goldston–Pintz–Yıldırım, Primes in Tuples I, (2.8)–(2.13)](https://arxiv.org/pdf/math/0508185).
No invention of this sieve weight or its short-range Euler product is
claimed. Here the actual cutoff varies with n and reaches √(n(P−n)),
and the symmetric smoothing includes cutoffs a fixed power above the
length of the n-sum. The calculation of the signed mean there, including
its squarefree/target-unit version, uses the published inverse-fraction
bound in the comparable range plus a Möbius reciprocal estimate in the
full remaining range. The separate rectangular two-divisor cutoffs in
[Pan's Goldbach decomposition, Huang–Li (3)–(6)](https://arxiv.org/html/2005.03811v2)
do not themselves give (5) or (6). The actual 2×3 sign is a consequence
of centered box-spline unimodality, not a parity-breaking estimate of
the whole odd-rank population. No exhaustive priority claim is intended.

For another comparison at the signed-boundary level, [Pham's October 2026 preprint](https://www.preprints.org/manuscript/202610.3061), Section 8 and the appendices, separates several fixed-target mixed and prime-boundary estimates from its unresolved full signed comparison. The benchmark (5) here is for the particular coupled quadratic weight; it is not an estimate of that full comparison. The companion [exact replay](replay.py) checks finite identities and exponent rails, not the cited analytic estimates.
