# True middle marks: a joint Poisson–Weil remainder for N at size H²

**Status.** Research note, 2026-11-24. Proven analytic input and an actual prime upper with two marked divisor coordinates. It crosses the modulus H^(1/2) and the affine-per-progression remainder levels in a fixed middle strip. It does not give the full N^.07-rough P3 moment. No restriction on rad(N) is needed. No claim of novelty over all literature; the comparison is to the specific prior affine/BV methods.

## 1. Statement

Let N be a sufficiently large even integer, H=sqrt(N), L=log N, and e(u)=exp(2pi i u). Let W be a smooth compactly supported function in a fixed compact subinterval of (0,infinity), with its fixed-order derivatives bounded by powers of L if W depends on N. Put I=(aH,bH] for fixed 0<a<b when using the prime application.

Take Q=N^t with .200<=t<=.230, delta=.25−t, sigma=7delta/6, rho=.25+delta/12−.001, S=N^sigma and D=N^rho. Use prime q~Q with q not dividing N, and squarefree s<=S with (s,N)=1. In particular q>s, so (q,s)=1. Let b_{q,s} be arbitrary complex coefficients of absolute value at most one, independent of r. For each r<=D with (r,s)=1 define

    E(r,s) = sum_{q~Q prime, q∤Nr} b_{q,s}
      [sum_{j integer, s|j, r|(N−qj)} W((N−qj)/H)
        − H/(rqs) · integral W ].

There exists an absolute epsilon0>0 (e.g. 1/10000 after absorbing fixed divisor powers) such that

    sum_{s<=S, s squarefree, (s,N)=1} sum_{r<=D,(r,s)=1}
          |E(r,s)| <= C_W N^(.5−epsilon0).

The bound also tolerates any fixed divisor powers in the external r,s coefficients, by the standard pointwise N^o(1) divisor bound. In the proof all variables r,s are arithmetic filters on integer p=N−qj and integer j. Writing p=r m never factors a genuine prime p; r occurs when expanding the p-sieve weight.

For long marks s~S, qs~N^(.25+delta/6) exceeds the BV modulus threshold for actual source p~H. Moreover rho+sigma+t=.5+delta/4−.001>.5, so the usual fixed-q,s interval remainder with O(1) per r no longer sums within H. Both improvements are powers on this fixed parameter strip. N is not substituted into a theorem with a small fixed residue.

## 2. Exact switched Poisson

Fix coprime r,qs. Write p=N−qj, with s|j and r|p, and abbreviate p=r m. The resulting condition is precisely m ≡ N bar r (mod qs); it is equivalent in both directions. Since W is supported at p positive and of size H≪N, the accompanying j=(N−p)/q is automatically positive for large N. Poisson for this one arithmetic progression gives, with Fourier transform hat W(x)=integral W(u)e(−xu)du,

    sum_{m ≡ N bar r (mod qs)} W(rm/H)
    = H/(rqs) sum_{h∈Z} hat W(Hh/(rqs)) e(hN bar r/(qs)).

The h=0 term is exactly the subtracted main term in E(r,s). The only occurrence of N in the nonzero phase is the integer numerator hN in a modular inverse; in particular there is no loss proportional to N/H in the real smooth amplitude.

Work on dyadic r~R,s~S0 and q~Q (possibly arbitrary interval clips). For fixed s and h, the normalized weight of (r,q) is

    H/(rqs) · hat W(Hh/(rqs)).

Its value and mixed first log derivatives in r and q are bounded by

    L^C_A · [1/A0] · (1+|h|/A0)^(-A),    A0=RQS0/H.

Two successive partial summations justify separating this weight, using uniform sums over clipped r and q subintervals; the coefficients remain a_r (including each sign chosen after fixing s) and b_{q,s}, independent of one another. The h tail |h|>N^eps(1+A0) is negligible by taking A sufficiently large and using the trivial bound. In fact the maximum A0 exponent is rho+sigma+t−.5=delta/4−.001<=.0115; hence all nonzero retained h satisfy |h|<q. In particular q∤hN for all supported q.

## 3. Cauchy, CRT and completion over r

For fixed s,h and clipped intervals, define

    K = sum_{r~R,(r,s)=1} a_r
           sum_{q~Q prime, q∤Nr} b_{q,s} e(hN bar r/(q s)),
    |a_r|<=1.

Cauchy in r costs O(R). Diagonal terms q1=q2 cost O(RQ) in the remaining squared sum. For distinct prime q1,q2, the r summation is over the units modulo M=s q1 q2, and its phase is exactly

    e_M( hN(q2−q1) bar r ).

This identity uses that the inverse modulo M reduces to the inverses modulo s q_i. Neither q_i divides hN(q2−q1) since |h|<q_i, q_i∤N and q1,q2 are distinct primes. For the s factors, coprimality (s,N)=1 is fixed in the stated support. Here M is squarefree and R<M on the entire parameter range. Completing the incomplete r interval by additive Fourier coefficients (total normalized absolute size O(log M)) and the classical Weil estimate for each complete Kloosterman sum gives the bound

    N^o(1) Q sqrt(s) · (s,h(q2−q1))^(1/2).

Indeed the local estimate at each prime divisor of M is <=2 sqrt(l) unless both coordinates vanish, and the general multiplicative bound is tau(M) sqrt(M) (M,A_freq,B_freq)^(1/2). Replacing that gcd by (M,A_freq) only raises it. The zero additive frequency is also covered. This proves the assertion for the actual incomplete intervals rather than assuming a complete r sum. It is enough here to cite the classical Weil bound; completion conventions are as in Duke–Friedlander–Iwaniec, Invent. Math. 128 (1997), 23–43, §1 and Lemma 8, https://www.math.ucla.edu/~wdduke/preprints/bilinear.pdf . No bound for a Kloosterman-fraction bilinear form with a restricted large fixed numerator is being invoked.

Use (s,ab)^(1/2)<=(s,a)^(1/2)(s,b)^(1/2). Counting q pairs by difference modulo d gives

    sum_{q1≠q2}(s,q2−q1)^(1/2)
      <= sum_{d|s} sqrt(d) · O(Q²/d+Q)
      <= Q² N^o(1),

since s<=Q². (Counting all integers in the clipped q interval is legal for this auxiliary upper bound.) Therefore

    |K| <= N^o(1) [ R Q^(1/2)
                    + R^(1/2) Q^(3/2) S0^(1/4) (h,s)^(1/4) ].

For each s, take a_r to be the conjugate sign of the original q-summed discrepancy E(r,s), including the dyadic restriction. It may depend on s, but not on h. The bound just proved is valid uniformly for every such choice, and remains valid after the partial summations. For h≥1,

    sum_h (1+h/A0)^(-A) (h,s)^(1/4)
      <= sum_{d|s} d^(1/4) sum_{k≥1}(1+kd/A0)^(-A)
      <= [A0/(A−1)] sum_{d|s} d^(−3/4).

This holds even when A0<1 by monotone integral comparison. It absorbs both signed frequencies, and cancels the 1/A0 amplitude. Summing over s~S0 gives total block bound

    N^o(1) [ R S0 Q^(1/2) + R^(1/2) Q^(3/2) S0^(5/4) ].

No loss from the number of frequencies remains except these powers, and the dyadic endpoint sums add only powers of L. At the worst parameters the first exponent is

    rho+sigma+t/2=.374+.75delta<=.4115,

and the second is

    rho/2+3t/2+5sigma/4=(1−.001)/2=.4995.

Smaller R or S0 only improve the bounds; thus the asserted N^(.5−epsilon0) follows. The absolute bound is for the q-summed error and is not an estimate for each q separately.

## 4. A genuine consequence above BV

For the same Q,S and parameters, restrict s to [S/2,S] squarefree, coprime to N. Let 0<=b_{q,s}<=1. There is an improved averaged upper for actual prime p in I with p≡N (mod qs):

    sum_{q~Q prime,q∤N} sum_{s~S squarefree,(s,N)=1}
       b_{q,s} · # {p∈I prime : qs divides N−p}
    <= [ (2+o(1))(b−a)H/(rho L) ]
          sum_{q,s} b_{q,s}/phi(qs)     + O(N^(.5−epsilon0)).

To prove this, choose W nonnegative, at least one on [a,b], by convolving the indicator of [a−L^−2,b+L^−2] with a positive smooth approximate identity of width L^−2. Then integral W=(b−a)+O(L^−2), its derivative growth is logarithmic, and its support is positive for large N. For each s apply the upper linear sieve for p at level D and sifting cutoff z_p=D^(.5), ignoring primes dividing s. Every genuine p∈I survives; q and p exceed z_p because rho/2<.13<t and H is larger still. The main density in r is 1/r on the allowed squarefree support. If (r,s)>1, the actual divisibility term vanishes because p≡N mod s and (s,N)=1; those r are not used. This resolves the shared-root issue without treating overlapping roots as independent. The same fact ensures that true p with q|N or (s,N)>1 cannot occur in the prescribed range (any omitted p divisor of N is harmless by construction).

The sieve remainder, even with s-dependent coefficients, is controlled by sum |E(r,s)| and fixed divisor factors. Here the input q weights b_{q,s} may depend freely on s, but not on r. Uniformly s<z_p since sigma<=.05834 and rho/2>.124, so all s-primes are omitted from the Euler product, yielding

    V_s(z_p)=(1+o(1)) e^(−gamma_E) (s/phi(s))/log z_p.

The dimension-one condition is uniform, since deleting local factors only reduces upper prime-product ratios. As the linear upper sieve at parameter 2 has F(2)=e^(gamma_E), the total main factor in units (b−a)H sum b_{q,s}/(qs) is 2(s/phi(s))/(rho L). Replacing q by phi(q)=q−1 changes it by relative o(1). This gives exactly the displayed bound. References for the standard linear-sieve normalization: Montgomery–Vaughan II, §21.3, Theorem 21.9, https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf .

For comparison, term-by-term Brun–Titchmarsh on the actual interval and modulus qs gives the same expression with rho replaced by .5−t−sigma=.25−delta/6. Here

    rho−(.5−t−sigma)=delta/4−.001>0,

uniformly in the stated strip. For ordinary dense mark weights the absolute power-saving is negligible, so this is a strict gain in the proven upper constant. The moduli qs sit above H^(1/2), unlike the case s=1 (where ordinary BV is better than this upper-sieve result). No asymptotic for the primes in these progressions is claimed.

## 5. What this does and does not pay toward P3

The desired mark uses the exact factor j with P^−(j)>=N^.07. Here s is a divisor tested in the expansion for that condition; the proven joint range only sees s up to N^.05834 in the chosen strip. In fact the elementary completion mechanism cannot give a full-level, one-shot cofactor sieve here while simultaneously overtaking the trivial affine remainder: if r=N^u,s=N^v,q=N^t, overtaking needs u+v+t>.5, whereas the off-diagonal condition just proved is u+3t+(5/2)v<1. Together these force v<(4/3)(.25−t)<=1/15<.07 for t>=.20. Thus this method by itself cannot even see all single cofactor primes to the original rough cutoff in its beyond-affine block. An upper for the unsigned counts at s is also not an upper that may be inserted blindly into a signed rough-sieve sum. No P3 bound or improvement to the previous constant for the full rough middle moment is claimed.

A precise next analytic step is to extend the same q-summed discrepancy (or bound signed rough weights directly) for a wider s range whose r exponent maintains u+v+t>.5, notably t in [.20,.23] with v>=.07. The q1,q2 off-diagonal completion currently pays Q sqrt(s) for each pair; even after gcd averaging its S0^(5/4) in the physical remainder is the barrier. A result exploiting cancellation between these incomplete CRT sums or extra factorability of the actual p/j weights rather than taking each s absolute is what would change that. Applying a fixed-residue theorem with a=N~H² is neither required for the result above nor a substitute for this missing step.
