# True fixed-target CQ mixed prime–positive-block bounds

This concerns actual pairs x+y=N (unlike [the CRT relaxation](CQFixedCRTNoPairObstruction.md)). Fix J compact in (1/3,2/3), N an even target, L=log N, M=|J|N𝔖(N), and real ⟨X,Y⟩=Σ X(x)Y(N−x) on x∈NJ and (x,N)=1. Define Π as actual prime log weight, R_J=⟨Π,Π⟩, and P the true one-arm squarefree rank-two/three positive score H on least factor >N^.123, zero elsewhere. On either orientation, for the explicit w₀≈.4974230623420378 proved below,
\[
 \boxed{\quad \langle \Pi,P\rangle\ge .146M-w_0R_J+o(M),\qquad
                 \langle \Pi,P\rangle+R_J\le4.300M+o(M). \quad}
\]
In particular at a hypothetical no-pair target the actual mixed moment has a nontrivial strictly positive lower. The upper is weaker than the <m(P)+1 desired to reject that value from the relaxed model. These are not Goldbach lower bounds. Use the pinned CQ proof/inputs at [989aea5](https://github.com/mxym/math/commit/989aea5aebbf6116d633a6c296ec02f568bf91d2), particularly CubicQuinticSharp, WiderPositiveBlock and its companion exact checker. Primary dimension-two sieve reference is Diamond–Halberstam Theorem 9.1 and Franze–Kao §4, as used in WiderPositiveBlock.

## 1. Actual prime-side rough lower; count actual rank four separately

Put α=947/4000=.23675 and θ=.499. Write
\[
C_α=L\sum_{\substack{x\in NJ,(x,N)=1,\,P^-(x)>N^α\\ N-x\ \mathrm{prime}}}\log(N-x).
\]
For the actual opposite prime use ordinary Bombieri–Vinogradov to sieve x=N−y at level N^θ. Relative local density at p∤N is 1/(p−1), at p|N zero on target units. Uniform product is (1+o(1))e^−γ𝔖(N)/(αL), as in the pinned linear-sieve calculation; actual unit/prime exceptions y|N have negligible O((log N)^C) total. Weighted ordinary BV with central y interval and partial summation is at a strict margin θ<.5. With s=θ/α∈(2,4) the lower linear function gives
\[
C_α\ge K_αM+o(M),\qquad K_α=2\log(θ/α−1)/θ.
\]
Terms having any repeated prime factor at this floor cost o(M): they lie in O(N^{1−α}+N^{1/2}) integer rows by summing over squares q² with q>N^α, and the prime×count weight is O(L²). More than four prime factors are impossible by 5α>1. The genuine rank-one terms contribute R_J+o(M): both prime arguments lie at scale N so log x=L+O_J(1), and O(M) for their count/log weight follows from the usual rough upper. There is no such term under no-pair.

For a rank-four squarefree x choose **once** its three least true prime labels p₁<p₂<p₃, let d=p₁p₂p₃, and write x=d n with fourth true prime n=p₄. Then n>N^α, d≤N^(1−α) by x<N, and (d,N)=1 by actual target units. For each such d let X_d=N/d. We upper-sieve the two linear forms n and N−dn on n∈NJ/d (length |J|X_d), dropping the sorting/last-prime restriction after selecting d. Both sieve parameters are measured in this new variable length: **cutoff z_d=X_d^.123 and level D_d=X_d^.999**. So s=.999/.123 exactly as in the calibrated DHR upper. No use of a cutoff N^.123 at the smaller variable length. Both real primes in the counted rows exceed z_d uniformly: n≥N^α, y=N−dn∼_J N, and X_d≤N^(1−3α), .123(1−3α)<α. Also X_d≥N^α, so all uniform sieve asymptotics run at polynomially long length even when d reaches its maximum N^(1−α).

The local root count for the two forms modulo a prime ℓ is two if ℓ∤Nd and one if ℓ|Nd, including the one root at ℓ=2 (d odd, N even). If ℓ|d then N−dn is nonzero mod ℓ because (d,N)=1; only n=0 is removed. If ℓ|N and ℓ∤d roots coincide. Thus the corresponding singular factor is 𝔖(N) ∏_{p|d}(p−1)/(p−2)=𝔖(N)(1+O(N^−α)); fixed three true large labels give uniform o(1), and missing roots only decrease the dimension-two ratio. Apply the same upper DHR constant C_DHR<20.881873 as WiderPositiveBlock at s=.999/.123, now with (log X_d)^−2:
\[
\#\{n\in NJ/d:\ n,N-dn\text{ both prime},\ n>N^α\}
\le (C_{\rm DHR}+o(1))\frac{|J|\mathfrak S(N)N}{d(\log X_d)^2}
     +O(X_d^{.999+o(1)}).
\]
The progression error for the linear forms is an exact floor remainder with at most two roots per prime, hence total O(D_d polylog) in the sieve; no prime distribution at the length N/d is being assumed. Summing errors (one sorted triple per d, or harmless divisor powers) is O(N^{1−.001α+o(1)}), since Σ_{d≤N^{1−α}}(N/d)^.999≪N^{.999+.001(1−α)}; multiplied by L² still o(M).

Write t_i=log p_i/L, using **target-log** angles here. Then t_i>α and Σ_{i≤3}t_i≤1−α exactly since p₄>N^α, x<N. Ordinary prime harmonic in fixed angular boxes, with sorted triples in the symmetric simplex, gives
\[
\sum_{d\ \,\text{selected}}\frac1d
\le\frac1{3!}\int_{t_i\ge α,\ \sum t_i\le1−α}\frac{dt_1dt_2dt_3}{t_1t_2t_3}+o(1)
\le\frac{(1−4α)^3}{36α^3}+o(1).
\]
Removing (d,N)=1 only enlarges this upper. The first factor 3! orders the real labels (ties are excluded, boundaries negligible in harmonic boxes); the other 3! is simplex volume. No double count of actual rank-four rows: the unique smallest three labels were selected prior to the enlargement. Since log X_d≥αL, multiplying the bound by L log(N−x)≤(1+o(1))L² yields total rank-four weighted prime cross in C_α at most
\[
K_4 M+o(M),\qquad K_4=20.881873\frac{(1−4α)^3}{36α^5}<.116104 .
\]

## 2. Lower true weighted P×prime

The remaining actual count from C_α is squarefree rank two or three above α and lies in P's original floor. For x∈NJ, own-log angles satisfy log p_i/log x≥α because log x≤L; the amplitude conversion log x/L=1+O_J(1/L) is uniform. Rank two amplitude is w(t)=1−2(1−2t)^3+(1−2t)^5 on minimum own angle t≤1/2, increasing, hence ≥w(α). For rank three, the exact CQ formula is 16∏u_i(3−5Σu_i²). Under u_i≥α, the product is at least α²(1−2α) by concavity of log on the simplex (minimum at a vertex); the sum of squares is at most (1−2α)^2+2α² by convexity (maximum at the same extreme shape). Define
\[
w_0=16α^2(1−2α)\{3−5((1−2α)^2+2α^2)\}.
\]
Its bracket is positive and w(α)>w₀. Thus
\[
\langle\Pi,P\rangle\ge w_0(K_α−K_4)M - w_0 R_J+o(M).
\]
All floors and weights were on the same target; prime-prime rank was subtracted only once. The corresponding orientation replaces J by 1−J throughout (same length and fixed bounds); neither inequality is added twice unless explicitly summing both ordered moments.

Exact lower log via first atanh term: θ/α−1=1049/947 and log(1049/947)>2(1049−947)/(1049+947)=51/499. Hence K_α>102000/249001. Rational arithmetic verifies w₀(102000/249001−K₄)>.146 (approximately .1460103792947203, so even .1458 has extra margin).

## 3. Genuine mixed upper with the actual prime-pair term retained

For least own angle t in rank three, its positive amplitude is at most
\[
w_3^+(t)=4t(1−t)^2(1/2+5t−15t^2/2)
\]
whenever the bracket is nonnegative: for fixed t, geometric product of the other two ≤(1−t)^2/4 and their squared sum ≥(1−t)^2/2, making the bracket and product largest together at equality. If bracket negative, actual weight nonpositive, trivially below w(t). Exact polynomial difference w(t)−w₃⁺(t)=4t³−2t⁵≥0; rank two equals w(t), and w increasing on [0,.5]. Let a=.123 and t₀=θ/3. With rough gates keyed by actual least factor at N^a and N^t₀, write R_a,R_{t₀} for indicators. Pointwise on central integers (including primes), 
\[
P/L+1_{\mathrm{prime}}\le w(t_0)R_a+(1−w(t_0))R_{t_0}+O_J(L^{−1})R_a.
\]
For P below the higher floor, its own-log least angle ≤t₀+O_J(1/L), and w Lipschitz; above the floor normalized score ≤1+O(1/L). Prime term is exactly on both rough gates, and P is zero on primes. The genuine weighted prime-rough upper at floor a is U(a)<4.651445 as pinned in WiderPositiveBlock (true rank-one source); at t₀ ratio θ/t₀=3, the linear upper F₁(3)=2e^γ/3 gives U(t₀)=2/θ. Multiplying by actual opposite prime log and L, the extra O(1/L) costs o(M) via U(a); L×prime indicator equals true Π up to relative O(1/L), similarly o(M). This yields the claimed upper with coefficient w(t₀)·4.651445+(1−w(t₀))·2/θ≈4.35416463358521<4.355.

## 4. Minimal exact replay for the constants

```python
from fractions import Fraction as Q
a=Q(947,4000); th=Q(499,1000)
w=lambda t: 1-2*(1-2*t)**3+(1-2*t)**5
z=1-2*a
w0=16*a*a*z*(3-5*(z*z+2*a*a))
K4=Q('20.881873')*(1-4*a)**3/(36*a**5)
Klo=Q(102000,249001)
assert w(a)>w0 and K4<Q('.116104')
assert w0*(Klo-K4)>Q('.146')  # even the conservative .1458
U=w(th/3)*Q('4.651445')+(1-w(th/3))*2/th
assert U<Q('4.355')
```

The two-layer mixed bounds do not exclude the relaxed predicted m(P)+1≈≥3.0377; they constrain the real conditional moment, not mere marginal compatibility. The next mathematical target is a lower bound for the genuine opposite-prime score deficit on rough non-P rows (or a direct conditional upper <m(P)+1−η).


## 5. Five-layer upper and comparison with the CRT witness

The two-layer upper can be sharpened without any new distribution assumption by using actual rough gates at t=.123,.130,.140,.150,.160,θ/3. If B(t) is the actual weighted prime-versus-t-rough count (the unweighted arm is multiplied by L), then B(t)≤U(t)M+o(M) for each fixed t, U(t)=e^{−γ}F₁(θ/t)/t. On the range 3≤s≤θ/.123<5 the linear-sieve delay equations give
\[A(s)=s e^{-\gamma}F_1(s)=2+2\int_3^s\frac{\log(u-2)}{u-1}\,du,\qquad U(t)=A(θ/t)/θ.\]
Indeed A'(s)=B(s−1)/(s−1), B(v)=v e^{−γ}f₁(v)=2log(v−1) for 2≤v≤4. Integrand increases on [3,4.058]: derivative sign is (u−1)/(u−2)−log(u−2)>0 there, using (u−1)/(u−2)>1.48 while log(u−2)≤u−3<1.06. Upper rational rectangles (8192 per interval), with the 6-term atanh upper of the logarithm, give
\[
U(.123)<4.651445,\quad U(.130)<4.45375,\quad U(.140)<4.23835,\quad U(.150)<4.09565,\quad U(.160)<4.02113,\quad U(θ/3)=2/θ.
\]
First number is pinned exact checker; the others use above integral. Integrate the pointwise score cap in §3 as an upper step: writing t₀=.123, t₅=θ/3, each term [w(t_i)−w(t_{i−1})]R_{t_{i−1}} pays that score band plus the initial w(a)R_a and final [1−w(t₅)]R_{t₅}; all sum to 1 on actual primes, so R_J is retained and subtracted once. Thus
\[
\langle \Pi,P\rangle+R_J\le
\Big[w(.123)U(.123)+\sum_{i=1}^5 (w(t_i)-w(t_{i-1}))U(t_{i-1})+(1-w(t_5))2/θ\Big]M+o(M)
<4.300M+o(M).
\]
Exact upper from the displayed rational U's is 4.299979195132343…, compared to ~3.04+ for m(P)+1. Under no pair this remains too high. It is nevertheless a real fixed-target mixed cap, not a reshuffling of the relaxed model.

Mandatory comparison: the specific positive law of the CRT obstruction note **does already fail the authentic prime-by-rough cap** U(.123). This is within its advertised scope (it preserved calibrated V rows and stated scalar signed inequalities, not all rough gates). Write c=m(1_{P>0}) and m_R=m(1_{squarefree, P^->.123}) for ordinary count harmonics, p=m(P) for score harmonic. The model simple reservoir ℓ² is outside the .123 floor. Thus its Π-by-.123-rough normalized value is m_R−1+c/p, since f is 1 on primes and −1/p on P's support. We can certify m_R>4.5628 and c/p>1.1555, yielding >4.7183 versus actual <4.651445. Consequently a claimed relaxation retaining this true prime-rough mixed condition cannot use the old witness unchanged; do not take its compatibility with all one-arm V rows for compatibility with this genuine constraint. This comparison does not exclude the model’s PΠ prediction p+1 by itself, nor prove an actual contradiction under no pair.

For the ordinary numbers, use b_r(t)=(1_{u>a}du/u)^{*r}(t)/r!, a=.123, r≤8. Then t b_r(t)=∫_a^{t-(r−1)a} b_{r−1}(t−u)du for r≥2. On cells [j/K,(j+1)/K], K=10000, floor lower ticks from complete preceding cells [ (r−1)a,(j−aK)/K ] and use denominator j+1; upper ticks include the next cell and use denominator j. Initial rank one lower K/(j+1), upper K/j. Directed ticks at scale 10^13 give Σ b_r(1)>4.5628563 and b₂+b₃<3.217944, b₃>1.2515575. Since rank-three amplitude ≤64/81, its deficit contributes ≥(17/81)b₃; rank-two harmonic defect on least t between a and .2 is at least F(.2)·(.2−a)/(.2(1−.2)) (the true ordered rank-two density is 1/(t(1−t))). Here F(.2)=.35424. So c−p>.43315, c/p≥3.217944/(3.217944−.43315)>1.1555. Exact ticks and additional rational U comparisons replayed using integer arithmetic; pseudocode follows.

```python
from fractions import Fraction as F

def req(x):
    if not x: raise ArithmeticError('bound')

def ceil(q):
    return -((-q.numerator)//q.denominator)

def loghi(x):
    z=(x-1)/(x+1)
    return 2*sum(z**(2*j+1)/F(2*j+1) for j in range(6))+2*z**13/(13*(1-z*z))

th=F('.499'); K=8192; S=10**12
steps=[F('.123'),F('.130'),F('.140'),F('.150'),F('.160'),th/3]
ub=list(map(F,['4.651445','4.45375','4.23835','4.09565','4.02113']))
for t,U in zip(steps[1:-1],ub[1:]):
    d=(th/t-3)/K
    total=0
    for j in range(1,K+1):
        u=3+d*j
        total+=ceil(S*loghi(u-2)/(u-1))
    req((2+2*d*F(total,S))/th<U)
w=lambda t:1-2*(1-2*t)**3+(1-2*t)**5
bound=w(steps[0])*ub[0]+sum((w(steps[j])-w(steps[j-1]))*ub[j-1] for j in range(1,6))+(1-w(steps[-1]))*2/th
req(bound<F('4.300'))

K=10000; aa=1230; S=10**13; ups=[]; los=[]
for r in range(1,9):
    low=[0]*(r*aa); high=low.copy()
    for i in range(r*aa,K+1):
        low.append((K*S if r==1 else lpre[i-aa])//(i+1))
        v=K*S if r==1 else hpre[i-aa+1]
        high.append((v+i-1)//i)
    los.append(F(low[-1],S)); ups.append(F(high[-1],S))
    lpre=[0]; hpre=[0]
    for x,y in zip(low,high):
        lpre.append(lpre[-1]+x); hpre.append(hpre[-1]+y)
C=ups[1]+ups[2]; L=F('.35424')*F('.077')/F('.16')+F(17,81)*los[2]
req(sum(los)>F('4.5628') and C<F('3.217944') and L>F('.43315'))
req(C/(C-L)>F('1.1555') and sum(los)-1+C/(C-L)>F('4.7183'))
```
