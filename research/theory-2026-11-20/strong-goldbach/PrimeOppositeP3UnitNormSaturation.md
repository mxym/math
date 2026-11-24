# Actual-unit norm saturation at the .06 crossing and the exact multiplicative transform

Written follow-up, 2026-11-24, to the [signed two-frequency completion](PrimeOppositeP3SignedTwoFrequencyCompletion.md) and [joint s-orthogonality](PrimeOppositeP3JointSOrthogonality.md). This isolates a genuinely full-size obstruction to reducing the first term by estimating the two local norms separately. It is not an obstruction to a new signed joint estimate.

Fix a true prime \(q\asymp Q\), a squarefree odd \(s\asymp S\) with \((q,s)=1\), and units \(c,d\bmod q\), \(a\bmod s\). Let \(h\) lie in one consecutive interval of length \(A\) whose integers are distinct and nonzero modulo \(q\), and let \(\ell\) lie in one nonwrapping interval of length \(B\le q\). Let \(\alpha_h\) be arbitrary coefficients of absolute value at most 1 with \(\sum|\alpha_h|^2\asymp A\), and put
\[
 F(x,\ell)=\sum_h\alpha_h e_s(a\bar x h)\operatorname{Kl}_{q}(ch,d\ell),
 \qquad x\in(\mathbb Z/s)^*.
\]
Uniformly if \(B\) exceeds \(Q^{1/2}\) by a power and \(\varphi(s)B\) exceeds \(A Q^{1/2}\) by a power,
\[
 \sum_{x\bmod s}^{*}\sum_{\ell}|F(x,\ell)|^2
   =(1+o(1))\varphi(s)B(q-1)\sum_h|\alpha_h|^2.
 \tag{1}
\]
Thus the *actual unit* norm saturates the size previously obtained by extending \(x\) to all residues; that extension has not lost a power. The result also applies to clipped intervals and to bounded complex smooth local coefficients of positive squared mass, and does not use artificial signs on the actual sums.

To prove (1), use inversion on the units. The \(x\)-sum for any \(h,h'\) is the exact \(c_s(a(h-h'))=c_s(h-h')\). For \(h=h'\), this is \(\varphi(s)\). The zero-twist complete prime-local energy is exactly \(q(q-1)\) by additive orthogonality in \(\ell\). Each nonzero twist is \(q\) times a two-pole sum, as in the prior \(\ell\)-correlation proof; its Möbius transformation is one ordinary Kloosterman minus its omitted value. This applies also when the two numerators agree, since the poles for a nonzero twist are distinct and the numerators are nonzero. Thus the incomplete diagonal energy is \(B(q-1)+O(Q^{3/2}\log Q)\). For \(h\ne h'\), the complete zero twist is \(-q\) and the same nonzero twist bound gives \(O(Q^{3/2}\log Q)\) for the incomplete correlation. For a nonzero difference, \(|c_s(h-h')|\le(s,h-h')\le\sum_{d\mid s,\ d\mid h-h'}d\). For each \(d\mid s\) with \(d\le A\), the number of ordered distinct pairs is \(O(A^2/d)\) by counting nonzero multiples among the possible differences; a divisor \(d>A\) occurs for none. Thus the off-diagonal is \(O(A^2 \tau(s) Q^{3/2}\log Q)\). The stated fixed margins absorb the divisor and logarithmic factors and prove (1).

This saturation occurs in the actual desired beyond-affine middle strip. For \((t,v,u)=(.20,.068,.27)\), one has \((A_0,B_0)=(N^{.038},N^{.198})\); the product safety target \(u+3t+1.8v=.9924<1\) applies, but \(t+v=.268>.25\) fails the current first bound. Choose true \(s\) with two distinct prime factors in fixed thin angular windows near .034; it is squarefree and all sifting primes are below the genuine .06 cutoff. Then \(\varphi(s)\asymp S\). The conditions for (1) are strict by large margins, and a fixed proportional \(h\)-window around a sufficiently small positive multiple of \(A_0\) has a smooth Poisson coefficient bounded away from zero after normalization whenever the usual nonnegative source window \(W\) is used (\(\widehat W(0)>0\)). Likewise take a fixed positive proportion of the physical dual interval in the rectangular estimate. This is a saturation of estimates based on separate absolute norms, not a lower bound for the original paired signed sum with its exact joint weight.

The multiplicative transform of the remaining \(s\)-phase is explicit. On the actual units \((\ell,s)=1\), write \(y=\ell x\), and define \(\tau_s(\overline\chi)=\sum_{r\in(\mathbb Z/s)^*}\bar\chi(r)e_s(r)\). Then
\[
 e_s(y\overline{q_1q_2})
   =\frac1{\varphi(s)}\sum_{\chi\bmod s}
          \tau_s(\bar\chi)\chi(y)\bar\chi(q_1)\bar\chi(q_2).
 \tag{2}
\]
The h-dependent \(s\)-phases before this transform are already separately functions of \(q_i\): their coefficients are \(N\bar q_1\) and \(-N\bar q_2\). Thus (2) genuinely factors the third *additive* \(s\)-phase. But the actual prime-local factors at \(q_1,q_2\) still carry the mutually dependent \(\bar q_2\bmod q_1\), \(\bar q_1\bmod q_2\) in their \(\ell\) coefficients:
\[
 \operatorname{Kl}_{q_1}(Nh_1\bar s,\ell\overline{s q_2}),\qquad
 \operatorname{Kl}_{q_2}(-Nh_2\bar s,\ell\overline{s q_1}).
\]
Therefore a formal factorization into two independent prime-\(q\) averages would not be an identity. Also the normalized \(\ell^1\) norm of the Gauss coefficients in (2) is of size \(S^{1/2+o(1)}\) for squarefree \(s\) with two polynomial primes as above: the proportion of primitive characters tends to 1, and every primitive Gauss sum has modulus \(\sqrt s\). Taking absolute values over characters provides no saving at this stage. A useful application of (2) needs character-averaged cancellation or a joint estimate for the two reciprocal prime-local traces; it cannot be deduced merely from the otherwise genuine factorization of the phase. The \((\ell,s)>1\) classes need not be modeled by this unit formula and make no difference to the saturation conclusion.

For the .06 crossing example, current first-error exponent \(t+v+1/4=.518\) would need a gain greater than .018 in the original physical remainder, i.e. a gain greater than .036 in the off-diagonal completed energy before the physical Cauchy factor. To make the first constraint disappear on the full desired strip one needs true coupled cancellation at least at this scale; a separate improvement of either of the saturated norms cannot supply it. No claim is made about whether the joint signed angle meets that threshold.