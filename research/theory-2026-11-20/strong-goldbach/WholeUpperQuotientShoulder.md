# A reflected super-square-root shoulder against every centered large quotient

Keep the original Goldbach semiprime-cell setup, exact physical weight \(\kappa_s W_s(r k j)/\log(r k j)\), and cuts from [UniformResidueDoubleShoulder.md](UniformResidueDoubleShoulder.md). Put \(x=N/2\), \(I=(x/2,x]\), and take a label dyad \(s\sim S=x^\alpha\) with
\[
                         .114\le\alpha\le.14 .
\]
Fix \(0<\delta_0<.005\) and set \(B=x^{1/2+\delta_0}\). Replace the genuine quotient factors \(\mu(r),\Lambda(k)\) by their exact centered factors
\[
                    \mu(r)-P_B(r),\qquad \Lambda(k)-H_B(k)
\tag{1}
\]
from [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). We keep the literal quotient modulus \(A=s r k\); no factorability or convenient-size grouping of its **original** components is now assumed.

Consider the reflected divisor family
\[
 \begin{gathered}
 d=p\,P\,t,\qquad p,P\text{ actual primes},\\
 .067\le\log_x p\le .077,\qquad
 .350\le\log_x P\le .365,\\
 .4028\le\log_x(Pt)\le.4031,\qquad
 .5003\le\log_x(d\ell)\le.5011.
 \end{gathered}
\tag{2}
\]
Here \(\ell\) has its genuine \(\Lambda(\ell)\); \(t\) is not replaced by primes or by a positive surrogate. Every nonzero original \(\mu(d)\) is \(\mu(t)\), since \(t<p<P\) and \(p,P\) are distinct. In particular the original marks are unique, even in the presence of prime factors of \(t\): their size bounds follow from (2) and no prime of \(t\) can be in either marked band. The statement is also literal for nonsquarefree \(t\), with its zero Möbius coefficient. The inequalities imply
\[
 .0378\le\log_x t\le.0531,\qquad
 .0202\le\log_x\ell\le.0313,\qquad
 .4698\le\log_x d\le.4801 ,
\]
so this is within the actual original \(d>U,\ell>V,d\ell>Q\) branch.

Then the signed double-Vaughan sum on (2), in the original physical equation
\[
       d\ell h+s r k j=N,\quad n=s r k j\in I,\quad (n,N)=1,\quad A\ge x^{1/2},
\]
and using (1), is \(O_D(x(\log x)^{-D})\) for every fixed \(D>0\), uniformly at each target and for arbitrary fixed log-power bounded \(\kappa_s\). Arbitrary additional ordinary intervals on \(A,r,k,j\) can be included. In particular the estimate is not restricted to any A-profile and is valid up to the actual physical maximum \(A\le x\). The prime-only concern is not addressed by any such distribution result: the remaining other reflected divisors are untouched.

## 1. The quotient coefficients now have a genuinely bounded free length

Expand both (1) in their exact reciprocal Heath--Brown identities of order 10, with the truncated \(\mu\) cutoff \(x^{.1}\), as in [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). The index \(r\) expands into at most \(10\) short \(\mu\)-slots and \(9\) free \(\mathbf1\)-slots. For \(k\) include one additional free \(\log\)-slot. All terms are exact on \(r,k\le x/S\). That note proved that \(P_B,H_B\) are exactly the sums of tuples with a free slot \(>B\), including both ordinary and log slots. Thus the surviving identities here retain **every** tuple with all free slots \(\le B\), with their binomial coefficients and true original signs, with no assertion of prime-factorability of \(r\) or \(k\).

In the physical \(A\ge x^{1/2}\) sector, \(j=n/A\le x^{1/2}\) is an independent allowed interval cutoff. Consequently every elementary factor in this expanded \(n\) product, other than the separately named \(s\), has scale at most \(x^{.505}\), and \(s\le 2x^{.14}\). This is the new property that was unavailable in the actual unexpanded no-group example in [UniformResidueDoubleShoulder.md](UniformResidueDoubleShoulder.md). It holds at every original \(A\) in this sector because of the exact long switch, not because \(A\) is well-factorable.

## 2. Uniformly available intermediate grouped exponent

Here is the elementary grouping argument. Let \(a_s\in[.114,.141]\) be the exponent of the \(s\) atom; all atoms are nonnegative, their sum is \(1+O(1/\log x)\), and their maximum is \(\le.505+O(1/\log x)\). Use the band \([L_0,H_0]=[.406,.594]\). If any atom belongs to this band, use it. Otherwise every atom is \(<L_0\) for sufficiently large \(x\). Let \(b_1,b_2\) be the two largest atoms other than ignoring any zero-length factors (the argument allows \(s\) among them except in the two cases where the size already forces it to be distinct).
* If \(b_1\ge .297=H_0/2\), use \(b_1+a_s\). That atom is distinct from \(s\), and its sum with \(s\) lies in \([.411,.547)\).
* Otherwise, if \(b_1+b_2\ge L_0\), their sum is \(<H_0\).
* If \(b_1+b_2<L_0\) but \(b_2>.188=H_0-L_0\), both are distinct from \(s\). Their sum with \(s\) is between \(.490\) and \(.547\).
* In the remaining case start with \(b_1<L_0\) and successively add atoms of size at most \(.188\) until first reaching \(L_0\), which is possible because the total is \(1+O(1/\log x)\). The first crossing is \(<L_0+.188=H_0\).

This proves the desired group at every nonempty dyadic product box. The choice uses box scale exponents only; their \(O(1/\log x)\) errors are absorbed by the source margins below. The selected group cannot consist just of \(s\) and subpower slots: there are at most 40 other slots, the product exponent is at least .406 and the \(s\) exponent is at most .141. It therefore contains some polynomial-length free \(\mathbf1,\log\) or genuine short \(\mu\) factor (one may take exponent at least .006). This is the factor used for grouped SW, not the possibly arbitrary \(\kappa_s\).

## 3. True progression estimate with physical cuts and weights

Retain the \(N\)-unit condition on all independent atoms. The grouped coefficients are divisor-bounded after a fixed log normalization. The SW argument is the unrough version in §1 of [UniformResidueDoubleShoulder.md](UniformResidueDoubleShoulder.md): one polynomial-length primitive true \(\mu\), free interval, or free logarithm, with all other group factors held fixed and with the exact auxiliary coprimality. A free logarithm is handled by partial summation. This is an SW estimate on ordinary intervals, not a uniform result for arbitrary fast Mellin twists.

All original products \(r,k,A,n\) can carry their sharp intervals without compromising these primitive SW estimates. Partition the finitely many independent atom boxes into relative log meshes, keeping whole rectangles inside each original product restriction, and account for the boundary. A boundary around a product \(w\mid n\), at endpoint \(W\), can only affect \(n\le x\) divisible by some \(|w/W-1|\ll(\log x)^{-F}\), hence at most \(O(x((\log x)^{-F}+1/W))\) such \(n\). In the active large cutoffs \(U_q,V_q,A\ge x^{1/2}\) or \(n\in I\), the endpoint is polynomial, giving arbitrary log precision after Cauchy and physical divisor moments. For optional smaller \(r,k,j\) endpoints, \(r,k\) are already polynomially long; a small \(j\)-interval is imposed directly on its single free factor, with no product boundary. Product restrictions on the separate \(nr\)- or \(d\ell\)-side are not silently added. Any error is measured with the total unfolded tuple envelope \(L^C\tau(n)^C\tau(N-n)^C\), so the bound just on the set of contaminated \(n\) suffices. The principal terms use the same harmonic moduli bound as in the earlier two-factor shoulder. The original \(1/\log(r k j)\) is finitely expanded on the central band as in that note, along with the exact \(W_s\), and the smooth product weight is frozen on the same mesh with arbitrary log reserve. Individual dyads and accepted meshes put independent intervals on all real atoms before invoking the grouped estimate.

For the reflected modulus \(d\ell\) choose the two true source slots
\[
                        Q_1=Pt,\qquad Q_2=p\ell .
\]
Write \(u=\log_x Q_1,\ c=\log_x(Q_1Q_2)\); then \(u\in[.4028,.4031]\), \(c\in[.5003,.5011]\). Maynard III Proposition 5.3 has the following uniform strict margins under (2) and the grouping of §2:
\[
\begin{split}
      7u+12(c-u)&=12c-5u\le 3.9992<4,\\
      u+2(c-.5)&\le .4053<.406\le\beta,\\
      \beta&\le .594<.5969\le 1-u .
\end{split}
\tag{3}
\]
One may take a sufficiently small fixed analytic \(\varepsilon>0\) in the source; ordinary dyadic upper sizing adds only \(o(1)\). The explicit residues are \(N\bmod Q_1\) common in the \(Q_2\)-sum and \(N\bmod Q_1Q_2\) in the original reduced class. The proposition takes absolute values across these modulus slots and hence accepts the original separate coefficients. Their multiplicity is bounded: \(P\) is the unique possible prime of its band in \(Pt\) because \(P>\sqrt{Pt}\), and \(p\) is similarly the unique possible marked prime in \(p\ell\), since \(\ell<p\). Thus at fixed \(Q_1,Q_2\), \(p,P,t,\ell\) are determined whenever an allowed representation exists. Arbitrary intervals on the outer reflected labels in (2) are enforced without frequency twists of any sequence declared SW. In particular the sharp \(u,c\) restrictions can be applied outside the absolute discrepancy bound on any dyads that contain an eligible slot pair, with the fixed margins (3). Multiplying by \(\Lambda(\ell)\) costs just a log. We obtain the genuine centered discrepancy for the entire unfolded signed quotient convolution uniformly over these true modulus pairs.

Now evaluate the actual reduced principal part. For each physical \(n\) and fixed \(p,P,\ell\), all of these three labels must be coprime to \(Nn\), or there is no term. The remaining \(t\)-range from (2) is an ordinary interval, with both nonempty endpoints at polynomial scales \(.0378\) to \(.0531\). Because \(t,\ell<p<P\), \(p,P\) are coprime to \(t\ell\) and the denominator \(\phi(d\ell)\) separates them multiplicatively. The genuine \(\mu(t)/\phi(t\ell)\) sum on this interval is \(O_D(\phi(\ell)^{-1}L^{-D})\), by the two exact coprime \(\mu/\phi\) tails and the actual prime-power overlap for \(\ell\) in §3 of [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), with mask \(Nn\). The remaining \(p,P,\ell\) are summed harmonically with log costs. The exact signs of the unfolded \(n\) weights are still retained; their absolute masses are \(O(x L^C)\). This makes the true principal part negligible by a fixed log reserve. It proves the asserted cancellation of the full centered large-quotient side on this actual reflected family.

## 4. Relation to the complete residual

The \(A\)-cut here is chronological: below the ordinary square-root \(A\) range the earlier whole-column cancellations apply without modification from the reverse switch, because a long marked reverse slot cannot occur on small \(A\). This result treats the centered \(A\ge x^{1/2}\) side; it does not claim the underlying ordinary BV logarithmic seam is closed by an unmodified threshold. Likewise this reflected family lies strictly below the forward long-free cut length \(B_m\) of [DoubleSwitchedMain.md](DoubleSwitchedMain.md), so no forward long-free tuple in \(d\) can appear in this family. No mixed overlap with that forward term is being assumed away.

The new grouping works even for original bland quotient profiles with no convenient grouping near half, including the .12/.28/.27/.33 example of the earlier shoulder. The new price is different and explicit: a genuine reflected divisor admitting the canonical two-prime configuration (2) and the slightly larger \(s\)-exponent band. Reflected moduli without that factor configuration, most notably unstructured prime-sized \(d\), remain beyond this result. There is no required uniform upper on the fully centered double sum and no binary Goldbach proof.

[Lichtman’s source prime-distribution proofs](https://arxiv.org/html/2309.08522v1) and [Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also group exact Heath–Brown factors, for different prime progression and sieve coefficients. The splitting here is applied to the globally switched reverse-high coefficient, with the original large quotient unrestricted within the stated reflected family. See the [previous shoulder](UniformResidueDoubleShoulder.md) for the separate AMRAL parallel-work comparison. No general advance for the underlying distribution theorems is claimed.
