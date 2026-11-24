# A true asymmetric positive strip pays for the dominant-prime rank-six sector

Same literal sharp CQ \(H\), even target \(N\), reflected actual pairs \(x+y=N,\ (x,N)=1,\ x/N\in J\Subset(1/3,2/3)\), \(M=|J|N\mathfrak S(N)\), and \(L=\log N\). Keep the existing canonical \(R_J=\langle H,H\rangle+o(M)\) and the book-accounted sets \(\mathcal P,\mathcal A,\mathcal I,\mathcal W,\mathcal S,\mathcal Z\) of [the independent positive shell/rank-8 payment](CQIndependentPositiveShellRankEight.md), with the already established \(+.0370M\) reserve. No no-pair assumption is made.

Let \(\mathcal D\) be the new actual positive strip: both physical arms have squarefree rank 2/3 and \(H>0\); exactly one arm has true least factor in \((N^{.080},N^{.095}]\), the other has true least factor \(>N^{.113}\). The two orientations of this test do not intersect. This is disjoint from \(\mathcal P\) and \(\mathcal S\), which each require both genuine least factors \(>N^{.095}\) (strictly \(>N^{.123}\) for \(\mathcal P\)). It has neither a prime arm nor any tiny arm, and is disjoint from the three old negative sets by literal positivity. It does not reuse the symmetric tentative \(.086,.095\) shell: that may overlap \(\mathcal D\), was not paid, and is not added.

Define \(G\ge0\) to be \(-H\) on actual squarefree rank-6 arguments with true least \(>N^{.04}\) and largest own angle \(w=\max_{p\mid n}\log p/\log n\ge.54\), and zero elsewhere. Let \(\mathcal G_6\) be the corresponding actual pair union where either \(G>0\). The types defining \(\mathcal A,\mathcal I,\mathcal W,\mathcal Z,\mathcal G_6\) are pairwise disjoint on **one arm**: in \(G\) one of the other five own angles is at most \(.46/5=.092<.105\), so it misses the old high negative arm; it is non-tiny, and its rank differs from all old high-rank removals. The three positive pair sets \(\mathcal P,\mathcal S,\mathcal D\) cannot meet \(\mathcal G_6\) at all by signs.

**Result.** The actual \(\mathcal D\) positive contribution is \(>.00663M+o(M)\). The genuinely new adverse union \(\mathcal G_6\setminus(\mathcal A\cup\mathcal I\cup\mathcal W\cup\mathcal Z)\) has complete signed contribution \(>-.00573M+o(M)\), with all literal pair intersections paid. Thus the new positive strip covers the new sector independently, leaving fresh reserve \(>.0009M\), without using any of the previous reserve. For instance an outward-safe canonical conclusion is
\[
 R_J\ge .0378M +\sum_{(x,y)\notin \mathcal P\cup\mathcal A\cup\mathcal I\cup\mathcal W\cup\mathcal S\cup\mathcal Z\cup\mathcal D\cup\mathcal G_6}H(x)H(y)+o(M).
\]
No sign/bound on this literal remaining sum is asserted. The further rank-six diagnosis is that there is **no support break** at \(w=1/2\) (and no angular sign change at all for this rank), but there is an exact kernel plateau above half giving a substantially sharper true receiver than the rough-band/Cauchy budget.

## 1. Actual asymmetric DHR, without applying a different profile

Take \(a=.080,c=.095,h=.113\). Let \(\Omega_{\ell,h}\) denote the oriented true ambient where the first argument is squarefree \(\ell\)-rough and the second is squarefree \(h\)-rough, with actual target units and the fixed central interval. The prime-dependent discarded residues in the first variable are:
- for primes \(p\le N^\ell\), discard \(x\equiv0,N\pmod p\), two roots except one at \(p\mid N\) (including \(p=2\));
- for \(N^\ell<p\le N^h\), discard only \(x\equiv N\pmod p\), one root.
This defines a sifted sequence by recording for each \(x\) the product of sieving primes for which the corresponding bad condition holds. For every squarefree product of such primes, the exact bad residue count is the product of the respective one/two-root counts, by CRT, and each residue floor contributes \(O(1)\). Thus the remainder rails and the same level \(N^{.999}\) of the pinned symmetric DHR theorem remain valid. The dimension-two upper product condition holds with the same uniform constant: each local bad-root count is no larger than in the two-root comparison used in the symmetric proof, and \(p=2\) still has one root. There is no claim of joint distribution of the two ranks.

The true sieve product now is
\[
 \prod_{p\le N^\ell}(1-\nu_2(p)/p)
 \prod_{N^\ell<p\le N^h}(1-1/p)
  =(1+o(1))\frac{e^{-2\gamma}\mathfrak S(N)}{\ell h L^2},
\]
where \(\nu_2(p)=1\) for \(p\mid N\) and \(2\) otherwise. To see the tail is uniform, replacing the truncated two-root singular product by the full one costs \(O(N^{-\ell})\) from the quadratic generic factors and \(O((\log N)N^{-\ell})\) from primes dividing \(N\) above the cutoff. The ordinary Mertens factors give one \(1/(\ell L)\) and one \(1/(hL)\). The DHR sifting argument is \(.999/h\), the **same** for both \(\ell=a\) and \(\ell=c\), because the second prime bank ends at \(N^h\) each time. Deleting actual squareful or nonunit arguments above \(N^a\) costs \(O(N^{1-a+o(1)}+N^{1/2})\) rows, just as in the pinned proof. The upper may keep these contaminants without invalidating it.

Let \(B_h=e^{-2\gamma}f_2(.999/h)/h^2\), \(C_h=e^{-2\gamma}F_2(.999/h)/h^2\) as in the usual symmetric DHR. The two nested **oriented** ambient sets therefore satisfy the true difference lower, in \(M/L^2\) units:
\[
 |\Omega_{a,h}\setminus\Omega_{c,h}|\ \ge\
 h(B_h/a-C_h/c)+o(1).
\]
This difference consists exactly of the actual low band on the first arm and high rough on the second. No further \(\Omega\) difference is added.

For amplitude levels \(t,s>0\), \(E_{\ell,t}\) denotes the true squarefree rank-2/3 source above the \(\ell\) least factor and with original normalized \(H/\log n>t\). On the **first** arm of this oriented difference, a bad amplitude \(t\) means the source in the actual low band, with ordinary mass
\[
 m_\ell(t)=m(R_a)-m(R_c)-m(E_{a,t}\setminus E_{c,t}),
\]
where \(R_d\) is the true one-arm squarefree rough support. Its opposite is genuinely \(h\)-rough, so cost is at most \(U_h m_\ell(t)\) by the true compact linear upper at level \(N^{.499}\). On the **second** arm, bad \(s\) has ordinary mass \(m_h(s)=m(R_h)-m(E_{h,s})\). Its opponent is in the **actual** low band \(R_a\setminus R_c\), so the same-source \(a\)-rough upper minus \(c\)-rough lower costs at most \((U_a-K_c)m_h(s)\). Here \(U_j=e^{-\gamma}F_1(.499/j)/j\), \(K_c=e^{-\gamma}f_1(.499/c)/c\). The argument includes true primes only as bad high receivers, priced against the real low band; there are no primes in qualifying paired counts.

Subtract those two bad sets from the one physical ambient. The oriented positive layer count is at least
\[
 \left[h(B_h/a-C_h/c)-U_hm_\ell(t)-(U_a-K_c)m_h(s)\right]_+ + o(1).
\]
Reflect \(J\) to price the other orientation by the same constants with the low-to-high roles exchanged. The two row domains are disjoint by the low arm's least \(\le N^c<N^h\); thus double the final oriented integrated lower without double counting. The \(200\)-layer lower, true \(.001\) angular rank-2/3 boxes with strictly qualifying amplitudes, two-sided ordinary rough \(1/20000\) recurrence, and DHR/linear delay outward \(1/10000\) mesh are exactly the methods of the previous independent shell, here with separate \(\ell,h\) inputs. The ordinary low mass uses a rough upper minus rough lower minus genuine angular good lower on precisely \([a,c]\). It does not replace a difference by a product or model. The exact checker yields:
\[
 h(\underline B_h/a-\overline C_h/c)=5.472332519246\ldots,\quad
 \overline U_a=7.018847785546\ldots,\quad
 \overline U_h=5.008557923737\ldots,\quad
 \underline K_c=5.904672017570\ldots .
\]
The summed two-orientation lower on \(H(x)H(y)/M\) in \(\mathcal D\) is \(0.006636183461\ldots>.00663\). The comparison uses exact rationals before decimal display. Near own-vs-target logarithm boundaries, the same finite fixed-rank angular collars as in the previous shell justify applying genuine physical floors; layers are indicators of the canonical score, not of a softened profile.

## 2. Rank-six strict genuine support, and exact plateau amplitude

Write \(u_1,\ldots,u_6\) for positive genuine own angles summing to 1. Using the distributional-derivative finite difference already proved in the high-rank removal, the complete canonical squarefree rank-six score is
\[
 H(n)/\log n=\left(\prod_{i=1}^6 u_i\right)[96b_6''(0)-3840b_6(0)],
\]
where \(b_6\) is the analytic density of the sum of centered uniforms of the given widths. It is \(C^4\), symmetric unimodal (convolution of centered interval densities), and strictly positive at zero: any sufficiently small central interval in each of the first five widths has the final residual sum in the interior of the sixth, yielding a positive density integral. Therefore \(b_6''(0)\le0\) and \(H<0\) on every true squarefree rank-six argument. This rules out a sign-support disconnection anywhere in the rank-six simplex.

If the largest \(w>1/2\), convolve its uniform interval with the sum of the other five, whose entire support is \([-(1-w)/2,(1-w)/2]\). In a neighborhood of zero this shorter support lies wholly inside the translated largest interval, so \(b_6(0)=1/w,\ b_6''(0)=0\). Thus on \(\mathcal G_6\)'s actual source the normalized magnitude is the exact
\[
 G/\log n=3840\prod_{i=1}^5 u_i .
\]
The five factors really are the five smallest; the sixth is uniquely largest. Let \(s=u_1+\cdots+u_5\le .46\). In ordinary harmonic \(du_1\cdots du_5/(\prod_i u_i(1-s))\), the small-angle product cancels completely. By integrating over simplex slices of the five small widths in \([.04,\infty)\) and dividing by \(5!\) for their permutations (not \(6!\), since the largest is marked), the outgoing score has
\[
 m(G)\le \frac{3840}{5!\,4!}\int_{.20}^{.46}\frac{(s-.20)^4}{1-s}\,ds
        < .000546 .
\]
Using own floor .04 here can only enlarge actual true target floor; uniform asymptotic normalized ordinary score is a genuine compact angular measure in fixed rank. The runner evaluates this via a positive geometric series and rational tail.

### True upper for this rank-six receiver from the five named genuine labels

For any nonnegative genuine compact product source \(D\), on the *opposite actual arm* \(y=N-x\) open the unique literal five smaller prime labels \(p_1<\cdots<p_5\), \(P_5=\prod p_i\), and \(\sigma=\log P_5/L\in(.20,.46]\). They are all \(>N^{.04}\), coprime to \(N\) on actual target units, and the residual \(q=y/P_5\) is a true prime on the sector, \(q\ge N^{.54+o(1)}\). At fixed fine bins for \(\sigma\), let the upper endpoint be \(\sigma_+\). On the quotient upper-sieve to cutoff \(N^{(.499-\sigma_+)/3}\) at literal level \(N^{.499-\sigma_+}\), ratio \(3\); the actual \(q\) exceeds that cutoff. This uses the normalized linear upper coefficient \(2/(.499-\sigma_+)\) with respect to \(\mathfrak S(N)/L\). The distribution is examined on the **source of length \(N\)** at actual modulus \(P_5 d\le N^{.499}\), not by reusing an \(N\)-length theorem at the quotient length \(N/P_5\). True compact product BV absorbs the grouped coefficient multiplicities, bounded by a fixed divisor power for five prime labels. All label primes are \(>N^{.04}\), so omitting their repetitions from the quotient sieve and omitting shared/source unit primes changes its local model only by \(1+o(1)\) uniformly, exactly as in the previously opened one/two-label receivers. No independence of the real \(p_i\) and \(q\) is assumed.

The conditional true progression for the five labels contributes the reciprocal prime harmonic \(1/\varphi(P_5)\) off actual \(N\)-units (no residue if a label divides \(N\)). Insert the exact score amplitude above before summing labels: \(\prod \log p_i/\log n=(1+O_J(1/L))\prod \log p_i/L\), so it cancels the **five** reciprocal angular denominators. At each fixed bin, genuine Mertens/PNT harmonics apply to those named primes; let bin widths tend to zero after the fixed-target limit. There is no endpoint singularity because \(.499-.46=.039>0\). Thus both oriented upper bounds of this real receiver are
\[
 \langle D,G\rangle,\ \langle G,D\rangle
 \le U_G\,m(D)M+o(M),\qquad
 U_G\le\frac{7680}{5!\,4!}\int_{.20}^{.46}
       \frac{(s-.20)^4}{.499-s}\,ds < .009105.
\]
Only the \(*count\)* of residual primes was upper-sieved; rank-six and positive-product amplitude tied to this chamber were used pointwise on each genuinely covered integer. The fixed fine bin outer approximation and positive conditional error do not restore any false actual tuple; widening occurs only after a valid upper.

## 3. All actual incremental signed intersections, with no old positive reuse

Since \(H=-G\) on the defining source, the exact contribution of its full union is \(-\langle G,H\rangle-\langle H,G\rangle-\langle G,G\rangle\). The genuine signed compact transfer and nonnegative true prime rebates imply its cost at most \(4m(G)+U_Gm(G)\), using the new receiver upper on \(G\) itself, not the larger rough AM–GM cap. This is the canonical signed identity on the same actual \(N\).

Only four kinds of existing intersections must be additionally subtracted. For any two of those older one-arm types, the intersection of both with a \(\mathcal G_6\) row is empty (it would require three distinct one-arm types on two arms). Each overlap involves both actual orientations, with opposite arms in two disjoint types.

* With \(\mathcal A,\mathcal W,\mathcal Z\) the sign is positive, since both arms are negative. For old source weights \(A,W,Z\), the exact overlaps are the respective sums \(\langle F,G\rangle+\langle G,F\rangle\). The real receiver just proved upper-bounds their sum by \(2U_G[m(A)+m(W)+m(Z)]M+o(M)\), using the already frozen \(m(A)<.08472,\ m(W)<.002380,\ m(Z)<.001441\). None of the old overlaps with each other is charged again.
* With \(\mathcal I\), the exact signed overlap is \(-\langle G,T\rangle-\langle T,G\rangle\), \(T\) the original true tiny signed arm. Its real \(T=C+E+V_{\rm tiny}-D_{\rm tiny}\) transfer bounds each orientation by \((-m_\beta+U_D)m(G)M+\langle |V_{\rm tiny}|,G\rangle+o(M)\), with \(-m_\beta<.0063885,\ U_D<.0111568\). Apply the **five-label** real receiver to the compact artificial-positive-floor/rank truncations of \(|V_{\rm tiny}|\), before releasing the tiny floor: for each truncation this is a genuine nonnegative fixed-rank angular source, with uniform ordinary mass upper \(B_V\) from the original explicit tiny argument. The phase/tail order of the original tiny signed decomposition justifies passage to the limit against this \(G\le |H|\) compact source. Equivalently apply the triangle and the new upper at each truncated \(V_{\rm tiny}\), then pass only the original signed overlap to the limit; no convergence of an independently redefined absolute weight is needed. The original \(B_V\) formula and the rational replay give \(B_V<.1044\) (directed \(\beta^{69/40}<416176/10^{12}\) by raising to power 40). This costs at most \(2[(.0063885+.0111568)m(G)+.1044 U_G]M+o(M)\), avoiding the more expensive previous general tiny Cauchy slot.

The new total debit in \(M\) units is therefore at most
\[
 (4+2(.0063885+.0111568))m(G)
 +[m(G)+2(.08472+.002380+.001441+.1044)]U_G<.00573,
\]
with exact proof using the outward mass and receiver bounds. No overlap with positive sets exists; the old \(.0370M\) reserve remains intact even if slack in old estimates was zero. Subtract only this realized incremental cost from the new independent strip \(>.00663M\), then add the new remainder to the unchanged old canonical proof. This establishes the stated result and leaves the balanced/ordinary rank-six chamber (and deeper small-factor sectors) genuinely open.

Replay: run `node check_cq_asym_strip_dominant_rank6.js` using the [exact arithmetic checker](check_cq_asym_strip_dominant_rank6.js). Its two emitted records are directed rational results before decimal display. In the integrals, use \(I(D,B)= D^5 B^{-1}\sum_{j\ge0}(D/B)^j/(5+j)\), \(D=.26\). The mass integral after translation uses \(B=.8\) and coefficient \(4/3\); the receiver integral uses \(B=.299\) and coefficient \(8/3\). The positive geometric tail after 120 terms is outward-bounded by \((D/B)^{120}/(125(1-D/B))\), then multiplied by \(D^5/B\).
