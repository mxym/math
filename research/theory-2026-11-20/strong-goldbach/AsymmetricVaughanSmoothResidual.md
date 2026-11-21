# Exact large-prime elimination in the squarefree weighted residue

Use the genuine \(K_P\)-weighted carrier and matched sequence of [FlexibleMarkedCarrierFiveEighths.md](FlexibleMarkedCarrierFiveEighths.md), and the squarefree Type I reserve in [WeightedVaughanLargestPrimeDescent.md, §5](WeightedVaughanLargestPrimeDescent.md#5-squarefree-version-with-a-fixed-reserve). Write \(c_{\rm sf}(m)=\mu^2(m)c_N^W(m)\), \(J=[x,3x/2)\) (with the harmless integer endpoints inherited from \(I\)), and \(Q_0=x^q\), \(q=5/8-\eta-\zeta\). Use \(0<\eta<.006,\ 0<\zeta<.001\), so \(.618<q<.625\). The Type I link means
\[
          \sum_{r\le Q_0}\tau_j(r)\sup_t
               \left|\sum_{\substack{m\le t\\r\mid m}}c_{\rm sf}(m)\right|
                       \ll_{j,B}xL^{-B}
 \tag{1}
\]
for each fixed \(j,B\). All estimates here are for this actual signed sequence; no roughness of \(m\) is assumed. The conclusion is a representation of its actual prime-log discrepancy by a signed sum only on squarefree \(m\) with \(P^+(m)\le\sqrt x\). It is not a bound on that sum.

## 1. Asymmetric adaptive subtraction

Take \(U=\sqrt{x},\ V=Q_0/U\), positive real thresholds. The same Vaughan identity imposes \(d>U,\ k>V\); its other terms are Type I by (1), including the \(\mu_{\le U}*\Lambda_{\le V}*1\) term since \(UV=Q_0\). The isolated small Mangoldt term vanishes on \(J\). No assumption that \(U,V\) are comparable was used in the two unfolding steps or their cross term of the adaptive subtraction. Thus with \(m=d k\) and \(H=H(m)=m/Q_0\) one obtains
\[
 \sum_m c_{\rm sf}(m)\Lambda(m)
     =\sum_{m\in J} c_{\rm sf}(m)\,\mathcal B(m)+O_B(xL^{-B}),
 \tag{2}
\]
where the new actual coefficient, on squarefree \(m\), is
\[
\begin{split}
 \mathcal B(m)&=\sum_{\substack{d k=m\\d>U,\ k>V}}
            b(d;k)\left(1_{k<H}\log k
                       -\sum_{\substack{p\mid k\\p\le V}}\log p\right),\\
 b(d;k)&=\mu(d)+\sum_{\substack{c\mid d\\c k\le Q_0}}\mu_2(c).
\end{split}
\tag{3}
\]
Indeed \(H>V\), since \(\log_xH\ge1-q>.375\) and \(\log_xV=q-.5<.125\); this checks the required \(H>V\) hypothesis in the \(k\)-side simplification. The true \(k>V\) and \(d>U\) constraints remain; the squarefree support lets the small Mangoldt-divisor term in (7) be exactly a sum over primes. All low-modulus coefficient and maximal prefix steps are the same (including \(r=e h c z\) in the cross term) with the larger/smaller \(U,V\). In particular nothing required \(m\min(k,dh)>Q_0^2\) for the subtractions as such; that inequality was only one sufficient way to establish the previous smooth support across *all* \(k\).

Suppose a prime \(P>\sqrt x\) divides \(m\in J\). Then \(P>H\) for all sufficiently large \(x\), and \(P>U>Q_0/k\) whenever \(k>V\). If \(P\mid d\), write \(d=P t_d\). We have \(t_d=d/P<Q_0/k\) by \(P>H\). Thus the permitted divisors \(c\mid d,\ c\le Q_0/k\) are precisely all divisors of \(t_d\). The equality \(\mu_2*1=\mu\) gives \(b(d;k)=\mu(d)+\mu(t_d)=0\). This uses coprimality with \(P\), which follows either from squarefree \(m\) or from \(t_d<Q_0/k<P\).

Otherwise \(d\mid m/P=:t\). But \(t<1.5U<2U\); any proper divisor is at most \(t/2<U\). Therefore the only possible \(d>U\) here is \(d=t\), giving \(k=P>H,V\). The bracket in (3) then vanishes: the log indicator is zero, and the only prime divisor of \(k\) exceeds \(V\). It follows that
\[
                        \mathcal B(m)=0
                       \quad\text{if }P^+(m)>\sqrt x .
 \tag{4}
\]
In particular this removes the **whole** former extreme \(P>Q_0\) adaptive sector termwise, regardless of its true cofactor \(t\), and considerably more. It also means \(\mathcal B(m)=0\) on all squarefree primes and semiprimes: a \(d>U\) for a semiprime with both factors \(\le U\) cannot be a proper divisor, and \(k=1\) is excluded. At the earlier more symmetric thresholds the original residual can include nontrivial signed terms at \(m=P t\) outside these supports; (4) is a different exact arithmetic arrangement.

More generally, on the \(d\)-slot the same short-divisor proof shows \(b=0\) whenever any prime of \(d\) exceeds \(\max(H,Q_0/k)\). Thus for \(k\ge Q_0^2/m\) one retains the stronger bound \(P^+(d)\le m/Q_0\), and in the remaining \(k\)-range (4) still applies to the entire \(m\). For an interval \(J=[a,b)\) of any fixed ratio \(b/a<2\), the same argument permits \(U=\sqrt{b/2}\), \(V=Q_0/U\), and a cutoff \(P^+(m)\le U\), provided \(U\gg\max_{m\in J}m/Q_0\) and \(H>V\). No absolute estimate is needed to discard these coefficients.


Both weighted components in \(c_{\rm sf}(m)\) require \(N-m\) to be odd for large \(x\): the carrier is \(y\)-rough and the reference is \(Z\)-rough, with \(y,Z>2\). Since \(N\) is even, \(m\) is odd on the actual support. Any proper divisor of \(t=m/P\) is therefore at most \(t/3\). Consequently the same proof, if desired, uses \(U=\sqrt{x/2}\), \(V=Q_0/U\) to obtain the exact cutoff \(P^+(m)\le\sqrt{x/2}\) (now \(t<3U\) for \(P>U\)). This is a constant improvement, not an exponent improvement.

## 2. Optional subpower-rough transfer and lower cutoff

There is a genuine additional exact cutoff available with a small fixed level reserve. Set \(Z_m=\exp(L/(\log L)^2)\), and let \(c_{\rm sr}(m)=c_{\rm sf}(m)1_{P^-(m)\ge Z_m}\), with the indicator at 1 taken as 1. This does **not** change the prime-weighted quantity at all: \(c_{\rm sf}(m)\Lambda(m)\) is supported on actual primes \(m\asymp x>Z_m\). We do not approximate the true shifted prime support by roughness. For any fixed \(\xi>0\) small, \(c_{\rm sr}\) inherits (1) up to \(Q_1=Q_0 x^{-\xi}\).

Here are the complete uniform cutoff details. Truncate the exact small-prime inclusion-exclusion at order \(J_0=\lfloor C_0\log L\rfloor\) (adjust by one for parity if desired). Its difference from the indicator is at most \(\binom{\omega_{<Z_m}(m)}{J_0+1}\), by the finite alternating binomial identity. In each retained term, \(e\mid m\) is squarefree, with all prime divisors \(<Z_m\) and \(\omega(e)\le J_0\). The combined modulus is \(R=\operatorname{lcm}(r,e)\le rZ_m^{J_0}\le Q_0\) eventually, since \(Z_m^{J_0}=x^{O_{C_0}(1/\log L)}\). Both \(r\) and \(e\) divide \(R\), so the exact multiplicity, even with the fixed divisor weight \(\tau_j(r)\), is bounded by a fixed divisor power of \(R\); the maximal prefix is unchanged. Use (1) with a larger divisor exponent and arbitrary log reserve.

For the absolute omitted term, \(|c_{\rm sf}|\ll L^C\) and \(\sum_{r\mid m}\tau_j(r)=\tau_{j+1}(m)\). Expand the binomial count into squarefree products \(e\) of exactly \(J_0+1\) such primes. The sum of \(\tau_{j+1}(m)\) over their multiples up to \(O(x)\) is at most
\[
 \sum_{\substack{m\ll x\\e\mid m}}\tau_{j+1}(m)
   \ll \frac{x}{e}(j+1)^{J_0+1}L^j
\]
by submultiplicativity and the elementary divisor moment (if \(e>x\) use zero when outside support). Thus the weighted sum of the absolute difference is at most
\[
 x L^{C+j}
   \frac{\big((j+1)\sum_{p<Z_m}1/p\big)^{J_0+1}}{(J_0+1)!}.
\]
By Mertens' bound \(\sum_{p<Z_m}1/p\le\log L+O(1)\) and the factorial bound, take \(C_0=C_0(j,B)\) large enough to obtain any desired \(xL^{-B}\). The fixed \(\xi\) absorbs this choice of \(C_0\) for sufficiently large \(x\). This proves the rough transfer at a **subpower** threshold, not at a fixed positive power of \(x\).

Now repeat (2)–(3) with \(Q_1,\ H=m/Q_1,\ U=\sqrt{(3x/2)/Z_m}\), and \(V=Q_1/U\). The exponent of \(U\) is still \(1/2-o(1)\), \(H>V\), and \(UV=Q_1\). If \(P>U\) divides an \(m\) on this rough support, the \(P\mid d\) contribution is zero as before because \(P>H,Q_1/k\). Otherwise \(d\mid t=m/P<Z_mU\); a proper divisor is at most \(t/Z_m<U\), since \(t\) is \(Z_m\)-rough. Thus \(d=t\) and the \(k=P\) bracket is zero. The transferred residue is therefore supported on
\[
           \mu^2(m)=1,\qquad P^-(m)\ge Z_m,\qquad
           P^+(m)\le\sqrt{(3x/2)/Z_m}.
\]
Semiprimes and primes again give zero there. The balanced triples below, however, satisfy the rough and smooth cutoffs as well, so this does not remove their coefficient.

## 3. The remaining balance, and what this does not compute


The exact residual still has a substantial **balanced three-prime** coefficient. If \(m=p_1p_2p_3\) is squarefree with each \(\log_xp_i\in(.328,.338)\), then the only contributions in (3) are \(d\) a pair, \(k\) the other prime. Indeed \(d>U,\ V<k<H\). Also \(Q_0/k<x^{.297}\), less than both prime divisors of \(d\), so \(b(d;k)=2\) (only \(c=1\) in its short sum). Thus
\[
                         \mathcal B(m)=2\log m .
 \tag{5}
\]
The same coefficient survives every choice \(x/Q_0\le U\le\sqrt x,\ V=Q_0/U\), since this retains exactly the same contributing positions on these prime-exponent boxes. Convex mixtures of those particular Vaughan choices cannot damp this central three-prime coefficient. Equation (5) is only a pointwise coefficient test; it does not assert any sign of its multiplication by \(c_{\rm sf}\).

In fact at the asymmetric thresholds coefficients can have either sign even with exactly three prime factors. If the exponents are near \((.140,.429,.431)\), only the complement with \(k\) the .140 prime can contribute: the other two single-prime \(k\)'s exceed \(H\) and \(V\), and prime \(d\) factors are \(\le U\). Here \(V<k<H\) and both prime factors of \(d\) are below \(Q_0/k\), while \(d>Q_0/k\). The short sum on \(d\) is \(1-2-2=-3\), so \(b(d;k)=-2\); this chamber gives \(-2\log k\). Both signs hold on genuine open exponent ranges with no cutoff ambiguity, attainable for distinct integer primes by PNT at large scales.

Finally the **different** elementary identity obtained by expanding \(\log m=\sum_{r\mid m}\Lambda(r)\) says
\[
 \sum_m c_{\rm sf}(m)\Lambda(m)
     =-\sum_{\substack{P>Q_0\ {\rm prime},\ t>1\\Pt\in J}}
            (\log P)c_{\rm sf}(Pt)+O_B(xL^{-B}).
 \tag{6}
\]
The log total and the divisors \(r\le Q_0\) use (1); each prime \(P>Q_0\) is unique in a contributing squarefree product. Formula (4) does **not** imply any individual estimate for the terms in (6); (2) and (6) are two different decompositions of the same original signed quantity. In (2) the whole signal now lies on squarefree \(\sqrt x\)-smooth \(m\), containing in particular the **actual** balanced prime-product coefficient (5). Controlling that weighted signed shifted count is a concrete next arithmetic problem; neither unweighted modulus averages nor the sign table by itself bounds it. No Goldbach conclusion is asserted.

This is a support identity for one matched carrier, not a bound on the weighted boundary operators in [*Uniformity, Local Structure and Boundary Correlations in Goldbach Representations* (October 2026)](https://www.preprints.org/manuscript/202610.3061) or the separate signed operator in [Arneth (October 2026)](https://zenodo.org/records/23504447).
