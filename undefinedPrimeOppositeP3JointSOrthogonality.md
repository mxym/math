# Joint \(s\)-orthogonality and prime-local short correlations in the true middle remainder

Written research note, 2026-11-24. This proves two genuinely beyond-affine and beyond-the-old-Poisson–Weil ranges for the actual middle q-remainder. It does not yield an improvement in the .06 or .07 cutoff square's leading constant by unsigned support certification, and is not a P3 theorem.

Keep \(H=\sqrt N\), \(q\asymp Q\) true prime, \(r\asymp R\), \(s\asymp S\) squarefree and \((s,N)=1\), \(S<Q\) with fixed margin, and true \((r,qs)=1\). Put \(A_0=RQS/H\), \(B_0=SQ^2/R\). The parameterized conclusions below apply on the full-size blocks \(A_0,B_0\ge1\) with \(A_0\ll QN^{-c}\) for a fixed \(c>0\). For the stronger estimate assume additionally \(B_0\ll QN^{-c}\). The relevant new beyond-affine domain automatically has that property whenever it has the fixed exponent margins used to power-save. Use exact \(N\) in the CRT phases; there is no small-residue hypothesis.

## Signed completion

Use the [previously proved two-frequency completion](PrimeOppositeP3SignedTwoFrequencyCompletion.md) with \(m=sq_1q_2\), \(q_1\ne q_2\), and \(A=N(h_1q_2-h_2q_1)\). The two prime-local complete factors have form \(\mathrm{Kl}_{q_i}(c_i h_i,d_i\ell)\) with \(c_i,d_i\) units modulo the corresponding prime. The \(s\)-local complete factor is
\[
 \sum_{x\bmod s}^{*} e_s(bx\ell)
              e_s(a_1\overline x h_1)e_s(a_2\overline x h_2).
\]
Both \(a_i\) are units modulo \(s\), directly from \((s,Nq_1q_2)=1\). The actual Fourier weight has normalization \(A_0^{-2}(m/R)^{-1}\) times a Schwartz function in \((h_1/A_0,h_2/A_0,\ell R/m)\), with fixed seminorms bounded by powers of \(\log N\). This is the [previously checked](PrimeOppositeP3PrimeLocalFourierContraction.md) compact \(r/R\) integration and mixed integration-by-parts argument. Decompose normalized coordinates into central and signed dyadic boxes, apply three successive Abel summations, and bound the resulting clipped rectangular sums. Outer box growth is absorbed by arbitrary-order variation decay: losses are only \(N^{o(1)}\). In the stronger regime we may discard arbitrarily small tails beyond \(Q/3\) in absolute \(h_i,\ell\), by the assumed fixed margin; thus no residue repetition occurs modulo either \(q_i\) in retained coordinates. The direct estimate only needs this on \(h_i\), not on \(\ell\).

Fix \(s,q_1,q_2\) and one rectangle after this separation. Let \(A\) and \(B\) denote the comparable upper interval lengths in \(h_i\) and \(\ell\) on an active full-scale rectangle (dyadic growth is treated by the same rapid variation). Form
\[
  F_i(x,\ell)=\sum_{h\text{ in its clipped interval}} a_{i,h}
                 e_s(a_i\overline x h)\mathrm{Kl}_{q_i}(c_i h,d_i\ell),
 \qquad |a_{i,h}|\le1 .
\]
Use Cauchy jointly over \((x,\ell)\) on \(\sum_{x\in(\mathbf Z/s)^*,\ell} b_\ell e_s(bx\ell)F_1(x,\ell)F_2(x,\ell)\), not separately for each \(x\). Since \(x\mapsto\overline x\) permutes the units and the two norm summands are nonnegative, extend the squared norms to the full inverse variable \(y\bmod s\). Orthogonality and the unit \(a_i\) give the upper squared norm
\[
  s\sum_{a\bmod s}\sum_{\ell}
      \left|\sum_{h\equiv a\bmod s}a_{i,h}
                  \mathrm{Kl}_{q_i}(c_i h,d_i\ell)\right|^2.
 \tag{1}
\]

## Direct consequence

Each residue class of \(h\) has at most \(O(1+A/s)\) terms. Pointwise Weil for each true prime applies uniformly in \(\ell\), since \(h\ne0\bmod q_i\); for \(\ell=0\bmod q_i\) the value is just \(-1\). Hence (1) is at most
\[
   O\bigl(s(1+A/s)ABQ\bigr).
\]
Applying both norms, restoring \(A_0^{-2}B_0^{-1}\), summing \(O(SQ^2)\) actual triples \(s,q_1,q_2\), and using \(A\asymp A_0,B\asymp B_0\) up to paid dyadic weights gives a signed off-diagonal energy bound
\[
 N^{o(1)}(S Q^2 H/R+S Q^3).
\]
The original physical Cauchy factor \(\sqrt{RS}\) converts the two terms to
\[
 N^{o(1)}(QS\sqrt H+Q^{3/2}S\sqrt R).
 \tag{2}
\]
As in the originating signed-completion proof, the \(q_1=q_2\) part adds \(N^{o(1)}RSQ^{1/2}\); the zero mode can either be included or bounded separately, as there. In particular at \(Q=N^{.20},S=N^{.04},R=N^{.31}\) the two exponents in (2) are .49 and .495 and the same-prime exponent is .45. The old pointwise affine threshold requires \(u+v+t<.5\) (here .55), and the old Poisson–Weil condition requires \(u+3t+2.5v<1\) (here 1.01). The gain is on full-size modes and uses the real \(S\)-orthogonality.

## Stronger beyond-affine block via actual prime local correlation

In (1) separate \(h=h'\) from the pairs \(h\ne h'\) in the same residue modulo \(s\). The first terms contribute \(O(sABQ)\). The number of the second pairs is \(O(A^2/s)\) for an interval, even if \(A<s\) (there are then no such pairs). For each pair the prime modulus \(q=q_i\) sees distinct nonzero numerators \(a=c_i h\), \(a'=c_i h'\); the h-tail removal described above makes this a literal assertion for all kept h. The complete \(\ell\)-correlation with twist \(k\) is
\[
 \sum_{\ell\bmod q}\mathrm{Kl}_q(a,d\ell)
             \overline{\mathrm{Kl}_q(a',d\ell)}\,e_q(k\ell)
 =q\sum_{u\ne0,-k/d} e_q(a/u-a'/(u+k/d)),
 \tag{3}
\]
with the sign of \(k/d\) immaterial for the bounds (with this convention it is \(u+k/d\)). At \(k=0\) the value is \(-q\), since \(a\ne a'\). For \(k\ne0\) put \(b=k/d\); the Möbius change \(z=u/(u+b)\) takes the allowed \(u\)'s bijectively to \(z\ne0,1\), and
\[
 \frac a u-\frac{a'}{u+b}
 =\frac{a z^{-1}+a' z-a-a'}{b}.
\]
Thus the inner sum is exactly one complete classical Kloosterman sum minus its \(z=1\) term, times a phase. Weil gives \(O(\sqrt q)\) for the inner sum. Completing a clipped non-wrap \(\ell\)-interval at \(q\) has normalized Fourier \(\ell^1\) norm \(O(\log q)\), so the incomplete distinct-h correlation is \(O(Q^{3/2}\log Q)\) uniformly. This uses the actual \(d\ell\) in the prime trace, not a model correlation.

Consequently (1) is \(O(sABQ+A^2 Q^{3/2}\log Q)\). Applying the same two norms and true normalization gives the improved signed off-diagonal energy and physical error, respectively,
\[
 N^{o(1)}(S Q^2H/R+R Q^{3/2}),\qquad
 N^{o(1)}(QS\sqrt H+R S^{1/2}Q^{3/4}).
 \tag{4}
\]
Here the identity \(SQ^{7/2}/B_0=R Q^{3/2}\) explains the second change. The actual signed energy is bounded after the two h-sums and an oscillatory correlation in \(\ell\); this is not an absolute bound on the \(\ell\) summand. For \((t,v,u)=(.20,.04,.325)\), one has \(A_0=N^{.065}\), \(B_0=N^{.115}\) and (4) yields exponents .49, .495; the direct (2) second exponent is .5025. This strictly enlarges the new beyond-affine block from (2). In exponent notation the new domain asks \(t+v<.25\) and \(u+v/2+3t/4<.5\), as well as the same-q error condition \(u+v+t/2<.5\). For the genuinely beyond-affine part \(u+v+t>.5\), the first condition gives \(2t+v-u<3t+2v-.5<t\). Thus the extra non-wrap hypothesis \(B_0\ll QN^{-c}\) holds with fixed margin when the domain is used with strict exponent shaves. The needed \(A_0\ll Q\) follows from \(u+v<.5\); it holds throughout the relevant fixed-margin domain (and explicitly in the examples). For the older absolute or affine regions their already established estimates may instead be retained in the union.

## No improved ordinary leading square constant in the .06/.07 regime

Even adding both (2) and (4) to the existing admissible union does not improve the ordinary affine leading coefficient if one certifies a downward generator shape only by compatible supports, exponent sums, or negligible unsafe-pair exceptions in the harmonic sense. The analytic ranges are real, but that geometric ceiling survives.

Indeed set \(\delta=.25-t\), \(T=(.5-t)/2\), \(V=2\delta/3\). The old Poisson–Weil half-plane can extend beyond the affine region only for expanded cofactor exponent \(v<2V=4\delta/3\); either new domain has \(v<\delta<2V\). Thus at any \(v\ge 2V\) the union still enforces the affine inequality. Let a downward feasible generator shape have height \(F(y)\) and positive excess \(d(y)=F(y)-(T-y)\). An active positive-excess slice is possible only at \(y\le V\), by self-pairing. For the old and direct domains such a self-excess satisfies \(d(y)\le\delta\): for old Poisson–Weil this is \(d\le\delta-1.5y\); for (2) it is \(d\le\delta-y\) when that domain applies. For (4), \(2F(y)+y+.75t\le.5\) implies \(d(y)\le .125t+y/2\). Its own expanded cofactor ceiling requires \(2y\le \delta\). This need not be at most \(\delta\) throughout the strip. The useful estimate is instead
\[
 T-d(y)\ \ge\ .25-.625t-y/2
           \ \ge\ .1875-.375t\ \ge\ .10125
           \qquad (.20\le t\le.23),
\]
where \(y\le\delta/2\) was used. Thus *in every case*, the exact property needed in the existing tail proof is \(T-h\ge .10\) at any positive layer height \(h\), even though the stronger convenient bound \(h\le\delta\) is only used for the old and direct (2) regions.

For completeness, for surplus layer \(G_h=\{y:d(y)>h\}\) and \(y_h=\sup G_h\le V\le1/30\), actual pairing forces a deficit \(<-h\) at each \(y'\in(2V-y_h,T-h)\) by pairing \(y'\) with a point of \(G_h\) near its supremum. This covers the fixed subinterval \((1/15-y_h,1/10)\), whose Dickman-weighted mass for every \(\mu\ge.05\) is at least \(y_h+1/120\), by the same calculation as the [prior safe-shape barrier](PrimeOppositeP3SafeShapeBarrier.md). The positive layer mass is at most \(y_h\). Layer-cake therefore retains its \(-\Delta/120\) bound. The [harmonic compactness proof for actual LCM support](PrimeOppositeActualLCMSupportBarrier.md) applies verbatim with the new closed union, since it remains downward and the forbidden sum has interior open complement. In short, (4) improves some real middle remainder blocks but does not overcome the non-negligible signed unsafe expanded terms needed for a larger optimized square denominator.