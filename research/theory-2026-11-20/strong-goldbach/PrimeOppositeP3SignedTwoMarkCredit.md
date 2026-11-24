# A genuine two-prime marked CRT block and a legal signed pair credit for short-root \(P_3\)

Written research note. The exact two-product switch gives a signed Type-I remainder and a specific pair lower-credit target at cutoff \(.07\). The last section proves a positive true credit at cutoff \(.055\). Neither statement settles the corresponding total signed estimate or proves \(P_3\).

## 1. Exact two-prime marked progression

Let \(N\) be a sufficiently large even integer, \(H=N^{1/2}\), \(L=\log N\). On the actual square-root source window use a fixed smooth bounded compactly supported test \(W(p/H)\), with its log-loss derivatives allowed. Use genuine prime marks
\[
 p_1\in [N^{.07},N^{.085}],\qquad
 p_2\in [N^{.09},N^{.10}],
\]
neither dividing \(N\). These intervals are disjoint: every marked product \(M=p_1p_2\) determines its two primes uniquely, so no multiplicity or \(2!\) enters. On a dyadic mark block write \(X\asymp p_1,Y\asymp p_2,Q=XY\), and \(r\asymp R\), \(s\asymp S\), where \(r\le N^{.33}\), \(s\le N^{.04}\) is squarefree and \((s,N)=1\). The labels \(r,s\) are physical sieve divisors, not the two marked primes. In particular \((s,M)=1\) automatically. On retained \((r,sM)=1\), the exact switch \(s\mid j,\ p=N-Mj=rk\) is \(k\equiv N\bar r\bmod sM\), with Poisson discrepancy
\[
 D(r,s;M)=\frac H{rsM}\sum_{h\ne0}
       \widehat W(Hh/(rsM))\,e(hN\bar r/(sM)).
\]
The \(h=0\) principal term is exactly \(H(rsM)^{-1}\int W\). The marks and residue are genuine; the estimate does not replace \(p\) by an actual prime after counting \(r\mid p\) in the wrong direction.

For arbitrary bounded \(\beta_{p_1,p_2,s}\) independent of \(r\), with exact unit exclusion \((r,sM)=1\), the two-mark remainder satisfies
\[
 \sum_{r\asymp R}\sum_{s\asymp S}
  \left|\sum_{p_1,p_2}\beta_{p_1,p_2,s}D(r,s;M)\right|
 \ll N^{o(1)}\bigl(RS\sqrt Q+QS\sqrt H+Q^{3/2}S\sqrt R\bigr).
 \tag{1}
\]
This is a signed aggregated estimate: no claim is made for the absolute sum over all marked pairs separately. Fixed divisor powers outside the mark sum are absorbed into \(N^{o(1)}\). With \(Q\le N^{.185}\), \(R\le N^{.33}\), \(S\le N^{.04}\) the three right-hand exponents are at most .4625, .475, .4825 respectively, before \(o(1)\).

## 2. Complete all actual overlap types

Cauchy in physical \((r,s)\), with an \(r/R\) smooth positive majorant for the remaining square, gives the factor \((RS)^{1/2}\) times the square root of the completed energy. Keep both frequencies \(h_1,h_2\) within this square. Their physical length is \(A_0=RSQ/H\le N^{.055+o(1)}\). Truncate at \(|h_i|\le N^{.06}\) with arbitrary power error by rapid Fourier decay and its compact-scale derivatives (the margin is .005); hence all retained nonzero \(h_i\) are units at every true marked prime, whose minimum is \(N^{.07}\). No analogous truncation is needed on \(r\) beyond its dyadic clip. When the two products coincide, bound the entire sum over each retained \(h_i\) using normalized rapid decay; the energy cost is \(O(RSQ)\).

For unequal \(M_1,M_2\), put \(d=(M_1,M_2)\). It is either 1, a shared first mark, or a shared second mark; there is no cross-band shared prime. Set \(M_i=d m_i\), so \(m_1,m_2\) are coprime, and the exact completion modulus for \(r\) is \(s d m_1m_2\). The actual phase is
\[
 e_{s d m_1m_2}\!\big(N(h_1m_2-h_2m_1)\bar r\big).
\]
The three local moduli are \(s'=sd,m_1,m_2\), pairwise coprime. The first one is squarefree even if \(d>1\), since all primes of \(s\) are smaller than either mark, and coprime to \(N\) by the exclusion. At each prime of \(m_i\) the numerator reduces to a unit times \(h_i\). At the cofactor \(s'\) the local inverse phase is \(e_{s'}((a_1h_1+a_2h_2)\bar x)\) with \(a_i\) units, times the local dual additive phase \(e_{s'}(b x\ell)\). These are the exact CRT factors, with the literal \(N\). Unit exclusions in \(r\) become exactly complete unit sums and introduce no missing or extra row.

The direct joint orthogonality calculation from the [signed single-mark proof](PrimeOppositeP3JointSOrthogonality.md) works even for composite \(m_i\), with no deeper prime-local short-correlation input: each \(m_i\) is squarefree with at most two prime factors, and CRT plus prime Weil (or a unit-numerator Ramanujan factor when the dual argument vanishes locally) gives
\[
 |\mathrm{Kl}_{m_i}(c_i h_i,d_i\ell)| \ll \sqrt{m_i}
\]
uniformly on the actual \(h_i\) support and all \(\ell\), with an absolute fixed constant. At fixed \(s',m_1,m_2\), expand the \(s'\) complete sum in \(x\), use Cauchy over actual \((x,\ell)\), extend the positive norms by inversion to all \(y\bmod s'\), and apply exact additive orthogonality in \(h\bmod s'\). For a clipped interval in \(h\) of length \(A\) and clipped dual interval of length \(B'\), each resulting squared norm is bounded by
\[
 s' (1+A/s') A B' \sqrt{m_1m_2}
\]
(up to the fixed dyadic constants; each m_i has the same dyadic size). Nonseparable true weights are handled as previously: completion in \(r\) gives a Schwartz function of \((h_1/A_0,h_2/A_0,\ell/\Lambda)\) with weights \(A_0^{-2}\Lambda^{-1}\), where \(\Lambda=sdm_1m_2/R\). Three Abel summations on central and expanding dyadic rectangles retain that normalization and their mixed variation decays to arbitrary order. Nonzero frequencies in rectangles of physical size below 1 are empty, and in any other such rectangle counts are bounded by its size. Therefore no extra factor is lost even on dyadic subblocks with \(A_0<1\) or \(\Lambda<1\); their zero-\(\ell\) terms are handled separately below. This is also a reproof of the signed abs-summed estimate after arbitrary \(r,s\)-dependent conjugate signs outside the q-sum.

For disjoint products \(d=1\), \(s'\asymp S\) and \(m_i\asymp Q\). The resulting energy per \(s,M_1,M_2\) is
\[
 N^{o(1)}(S Q/A_0+Q).
\]
There are \(O(SQ^2)\) choices, giving energy \(N^{o(1)}(SQ^2H/R+SQ^3)\). If a first-prime mark \(a\asymp X\) is shared, \(s'=as\asymp XS\), \(m_i\asymp Y\); the same per-tuple expression is \(N^{o(1)}(XSY/A_0+Y)\), but now there are only \(O(XSY^2)\) choices including the shared mark. Thus this energy is \(N^{o(1)}(SQ^2H/(RX)+SQ^3/X^2)\), no worse than disjoint. A shared second mark has the same bound with \(X,Y\) interchanged. The \(\ell=0\) complete factors at the coprime \(m_i\) are unit-numerator Ramanujan sums of absolute value 1. Sequence normalization and the remaining factor of magnitude at most \(s'\) yield \(O(RS)\) energy for disjoint products and \(O(RSX)\) or \(O(RSY)\) for shared types. All are bounded by the same-product diagonal. This exhausts the literal collision types. Taking square roots proves (1), and arbitrary fixed dyadic partitions add only log powers.

The main term for each admissible \(s,r,M\) above is a CRT integer main term at the actual source length. Inserting convolutional sieve weights on the allowed \(r,s\) thus has a genuine normalized main term plus the absolute power-saving (1). It is not a claim that any particular choice of these weights gives a positive lower for *both* true primality of \(p\) and full \(N^{.07}\)-roughness of \(j\). In particular a direct lower prime sieve would test \(p\) up to its own square-root size \(N^{.25}\) and available level .33 gives parameter .33/.25<2. The ordinary prime-source BV lower for the cofactor after the marked product also fails its positive threshold: residual exponent \(.25-t_1-t_2\le.09<2(.07)\). Thus the true lower credit below is not booked by (1).

## 3. Legal negative two-mark charge and exact missing average

Keep the original square-root \(P_3\) parameters \(\mu=.07,\ \beta=.4,\ \eta=3/2\) and its normalized \(B\). For a true squarefree \(N^{.07}\)-rough complement define
\[
 W_1=\sum_{q\mid N-p}(1-t/.4)_+,\qquad
 V=\sum_{\substack{p_1,p_2\text{ in the two bands above}\\p_1p_2\mid N-p}}
                 \frac{.5-2.5(t_1+t_2)}{3},
 \quad t_i=\frac{\log p_i}{L}.
\]
In the signed score \(1-(W_1-V)/\eta\) the true pair term is a *credit* and would require a lower estimate, not another separate positive upper cap. The credit is safe pointwise. For rank four let \(U=\sum t_i=\log(N-p)/L\le1\). Then \(W_1-\eta=(1-U)/.4+\sum_{t_i>.4}(t_i/.4-1)\). For each marked pair of sum \(m\le.185<.2\), the complementary pair alone gives
\[
 W_1-\eta\ \ge (1-U)/.4+(U-m)/.4-2=.5-2.5m.
\]
Any two cheap edges on the 4 factors must intersect: two disjoint ones would give \(U<.4\), impossible on the actual central scale. A pairwise intersecting edge family on 4 vertices has at most 3 edges, so their thirds sum to at most the slack \(W_1-\eta\). For rank \(k\ge5\), \(k\le14\) by the actual cutoff, baseline slack is at least \(k-4\) and credits are at most \(\binom{k}{2}/30\le k-4\) (the convex quadratic check at the two endpoints suffices). The usual squareful exceptions are removed as in the original result and the full new weight is still uniformly bounded on survivors.

Write \(C_N=\sum_{\text{actual squarefree, .07-rough prime rows}}V\). Then the earlier criterion remains valid in the genuinely signed form
\[
               M_N-C_N\le(2.95+o(1))B.
\]
For example, the exact lower target for a first non-booked gain can be stated as
\[
 \sum_{p_1,p_2}\frac{.5-2.5(t_1+t_2)}3
   \#\{p\text{ true input prime}: p_1p_2\mid N-p,\ 
                     N-p\text{ squarefree and }N^{.07}\text{-rough}\}
 \ \ge\ (3-o(1)) B\sum_{p_1,p_2}
               \frac{.5-2.5(t_1+t_2)}{3p_1p_2}.
\]
All marks here are actual primes, omitting those dividing \(N\), and the larger statement could be weakened to this one weighted sum. It would give \(C_N>.0007 B\): the pair weight is at least .0125 and the product of harmonic exponent masses is \(\log(17/14)\log(10/9)>.19\cdot.1\) by the first atanh lower. This would allow \(M_N\le(2.9507+o(1))B\) while retaining the stated positive margin. No model of the marked pairs or separate positive upper was used to get the safe signed condition; the actual lower estimate in this display is open. Its scale is only a first explicit gain, not by itself a way to close the currently unpaid middle cost.


## 4. A genuinely paid two-mark lower credit at cutoff .055

Instead take \(\mu=.055,\ z=N^\mu\), keeping the same \(\beta=.4,\ \eta=3/2\) and root interval. Let the true prime marks be \(q\in(N^{.055},N^{.058}]\) and \(r\in(N^{.060},N^{.065}]\), omitting target divisors, and set \(m=(\log q+\log r)/L\in[.115,.123]\). Apply the same pointwise credit \((.5-2.5m)/3\) to each true marked pair. Rank four is handled exactly as above (two disjoint cheap edges are impossible). For ranks \(5\le k\le18\) the total credit is at most \(\binom{k}{2}17/240\le k-4\); the difference between the two sides is convex in \(k\), so it suffices to check 5 and 18. Thus the modified weight is nonpositive at every squarefree rank \(\ge4\).

For these lower-cutoff pairs, ordinary maximal-residue Bombieri–Vinogradov at the actual prime source length \(H\) is sufficient. The residual linear sieve level \(D=N^{.249}/(qr)\) has exponent in \([.126,.134]\), and \(s=\log D/\log z\ge126/55>2\), so the standard lower function is positive. Its coefficient in the original square-root normalization \(B/((q-1)(r-1))\), as evaluated for the [base signed target](PrimeOppositeSquareRootP3Target.md), is
\[
 \frac{\log(s-1)}{.249-m}\ \ge\
 \frac{\log(71/55)}{.134}\ \ge\ \frac{16/63}{.134}>1.89 .
\]
This is an aggregate lower estimate with summable individual residual errors, not a uniform prime theorem modulo each \(qr\) with no error. Indeed the sieve uses only actual moduli \(qrd\le N^{.249}\) with every prime factor of \(d<z\); the named tags are uniquely recovered from their disjoint prime bands. Their progression residue is literally \(N\), and dividing primes of \(N\) can be dropped with total reciprocal cost \(o(1)\). Maximal BV and the usual divisor-weight conversion pay the entire signed residual error by \(o(B)\). The linear sieve asymptotic error is uniform on this compact \(s\)-range. The usual squareful deletion contributes \(o(B)\) after summing pairs, since the number of pairs in any \(.055\)-rough complement is bounded by \(\binom{18}{2}\).

The weight is at least \((.5-2.5(.123))/3=.064166\ldots\) on these pairs. Their actual reciprocal mass is asymptotic to \(\log(58/55)\log(65/60)\), each term bounded below respectively by \(6/113\) and \(10/125\) from the first atanh term. Thus the true total lower credit is
\[
  \bigl(1.89\cdot .064166\ldots\cdot(6/113)(10/125)+o(1)\bigr)B
     >.00051B .
\]
This is a positive signed two-factor payment on actual prime roots and genuine squarefree rough complements. It is a partial contribution at \(\mu=.055\), not a saving valid at \(\mu=.07\), and no total P3 positivity is asserted.
