# A concrete over-root prime tag test and the obstruction in the current direct Heath–Brown treatment

Written research note, 2026-11-24. We give a specific true two-tag rough statistic that detects the [balanced rank-three angular transport](CQTagInvisibleBalancedRankTransport.md) **if** the corresponding actual large-residue prime remainder is controlled. We do not prove that remainder or a real theorem above root. We prove instead a factorization obstruction to obtaining it by applying the three current Lichtman rails directly to every individual canonical Heath–Brown atom. The obstruction holds even if all groupings of the atom's original source coordinates are permitted and Siegel–Walfisz is granted whenever needed. It does not exclude cancellation between Heath–Brown atoms, new Type III bounds, switching, or other estimates.

## 1. The concrete missing test

Use the original actual \(x+y=N\), fixed compact central interval \(J\), target units, prime log score \(\Pi\), \(L=\log N\), \(M_N=|J|N\mathfrak S(N)\). Put \(\eta=.0002\) and test the real rough two-tag count score
\[
 Z(n)=L\,1_{\{n\ {\rm squarefree},\,P^-(n)>N^\eta\}}
       \sum_{\substack{q\mid n,\ q\ {\rm prime}\\N^{.246}<q\le N^{.249}}}
       \sum_{\substack{r\mid n,\ r\ {\rm prime}\\N^{.255}<r\le N^{.258}}}1 .
\]
The true tag product has exponent \(>.501>.5\). The genuine sieve divisor \(d\) for the true quotient can be tested at \(N^{10\eta}=N^{.002}\), giving physical moduli \(qrd\) of exponent at most \(.509\) and literal residue \(N\). The sufficient missing estimate, in either actual orientation, is a log-power saving for the remainder summed with the standard ratio-10 upper and lower sieve weights \(\widetilde\lambda_d^\pm\) (absolute weighted error would also suffice):
\[
 \sum_{q,r\ {\rm in\ the\ stated\ prime\ bands}}
 \sum_{\substack{d\ \mathrm{in\ the\ actual\ sieve}\\(qrd,N)=1}} \widetilde\lambda_d^\pm
 \left[
   \sum_{\substack{p\in NJ,\ p\equiv N\bmod qrd\\p\ {\rm prime}}}\log p
  -\frac1{\varphi(qrd)}
    \sum_{\substack{p\in NJ,\ (p,qrd)=1\\p\ {\rm prime}}}\log p
 \right]\ll_A N(\log N)^{-A}.
\]
For the opposite orientation use \((1-J)\). Given both genuine sieve remainders, the usual local density and true weighted dyadic center argument gives a tolerance about the ordinary tagged center at most
\[
  \frac{.000002085}{.0002}
        \log(.249/.246)\log(.258/.255)+o(1)<.0000015+o(1).
\]
The strict rational upper follows on replacing the logs by \(.003/.246\), \(.003/.255\). Squareful trimming is harmless on the fixed rough floor as before; the two bands are disjoint and larger than \(d\)'s prime cutoff, so there is no multiplicity or local-root ambiguity.

This test is sensitive to the specific repaired marginal. On the actual donor rank-three rectangle with \(u=q\)-width in \((.246,.249]\) and \(v=r\)-width in \((.255,.258]\), the largest width \(1-u-v\) lies in \([.493,.499)\). All widths are genuine, sorted, above \(1/8\), and below \(1/2\); the whole rectangle belongs to the donor. The transported rank-two daughters have only one width below \(1/2\), so contribute zero to this two-tag moment. The exact deficit of the relaxed model is at least
\[
 \lambda\int_{.246}^{.249}\int_{.255}^{.258}
      \frac{du\,dv}{uv(1-u-v)}
 > \frac{.925\cdot .003^2}{.249\cdot .258\cdot .499}>.00025 ,
\]
where the previously certified \(m_{\rm donor}\le .54049918606245\) implies \(\lambda=1/(2m_{\rm donor})>.925\). Here \(u,v\) already specify the first two sorted angles and exactly one tag pair; the expression is a change in the **relaxed** marginal, not an actual same-target deficit. Thus the missing remainder would give an actual statistic refuting this repaired relaxation by a finite margin, and not a proof of Goldbach.

## 2. Why the direct large-residue prime-source factorization fails

Use [Lichtman, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5), at physical source length comparable to \(N\) and residue \(a=N\). Write \(h=\log H_0/L\) for the input Siegel–Walfisz factor size and \(A,b,c\) for the three slot exponents. Ignoring strict spectral margins (which can only relax necessary constraints), the first three tests require
\[
 A\le h,\qquad 2h+b+2c\le1,\qquad \theta+h+A+5b+2c\le2,\qquad \theta=7/32.
\]
The use of \(\theta\) here is the actual \(|a|^\theta\) term. These are upper-scale tests; failure for an actual product assignment already rules out any larger independently bounded slots. We test the true \(d=1\) term of the standard sieve, where the physical modulus has exactly its two indivisible primes. Denote their exponents by \(q\le r\), \(s=q+r>.5\). The following obstruction in fact works over every fixed donor pair with \(1/8\le q\le r<.5\), not only the displayed narrow test. Each of the \(d=1\) lower and upper sieve coefficients is 1 (empty rough block and empty smooth divisor). It is not legitimate to assume the missing divisor helps the packing of this term.

Use the **actual original prime-source decomposition** in [Lichtman's proof of Theorem 1.7, arXiv:2309.08522 §3](https://arxiv.org/html/2309.08522v1#S3), namely the rough \(k=3\) Heath–Brown convolution identity. The relevant atoms below are the individual nonzero convolution-support rectangles of that identity; they are not factorizations of primes. All exponent centers can be thickened to fixed sufficiently small open angular boxes, or realized by dyadic boxes of fixed-ratio lengths at those centers; the \(\mu(m_i)\) coordinates admit actual squarefree rough numbers, and the other coordinates are actual rough integers (one with log factor). The support has nonzero weighted tuples, since one may choose each actual coordinate prime in disjoint intervals of fixed ratio at its center. Their cancellation in the final \(\Lambda\) is precisely why a cross-atom route is not excluded. Let a putative SW factor be **any** grouping of these original irreducible coordinate variables; we overgrant the SW property for each grouping.

* If \(r\ge.2585\), use the genuine \(j=2\) summand, with its four source coordinates all of size \(N^{1/4}\). Any group has exponent \(h\) equal to \(1/4,1/2,3/4\) up to collars. For \(h\ge1/2\), the first two rails already fail: if \(h=1/2+o(1)\), the two primes of total \(>.5\) cannot both go in \(Q_1\), and every nonzero \(b\) or \(c\) exceeds a fixed positive constant; for larger \(h\) the failure is stronger. For \(h=1/4\), \(r\) cannot fit \(Q_1\) and cannot go in \(Q_3\) since \(2h+2r>1\), so it must go in \(Q_2\). The other prime in \(Q_2\) makes \(5b>2.5\); in \(Q_3\) it gives \(2h+r+2q=.5+s+q>1\). In \(Q_1\) it gives the last rail \(\theta+1/4+s+4r>2.00275\). All placements fail.
* If \(r\le.2585\), then \(q>.2415\). Use the genuine \(j=3\) summand, six source coordinates all of size \(N^{1/6}\). Grants \(h=1/6,1/3\) and any \(h\ge1/2\) (the latter already fails as above). At \(h=1/6\) neither named prime fits \(Q_1\); putting both in \(Q_2\) fails \(5b\), and every other distribution has \(2h+b+2c\ge 1/3+s+.2415>1\). At \(h=1/3\), no positive named factor can occupy \(Q_3\) because \(2h+2(.2415)>1\); both together exceed \(Q_1\) and both together overload \(Q_2\). Splitting the two between \(Q_1,Q_2\) incurs \(\theta+1/3+s+4b\) with \(b>.2415\), which is \(>2.01808\).

These margins leave open-sized coordinate neighborhoods: e.g. widths sufficiently close to \(1/4\) or \(1/6\) within \(10^{-5}\), in addition to the fixed strict \(s>.5\) condition. For a fixed box with \(s\ge.501\) there is ample uniform margin in every case.

The direct backup branches in the published HB reduction do not cover these particular rectangles. No individual rough unweighted \(n_i\) has length \(>N^{1/3+\varepsilon}\), and the \(\mu\)-coordinate mass is fixed polynomial, not \(N^{O(\varepsilon)}\). If one tries Proposition 3.2 with the two actual unweighted rough variables, their product is at most \(N^{1/2+o(1)}\) in these rectangles, so its condition \(Q\le (N/M)^{2/3-3\varepsilon}\) is far below the tested moduli. Combining several such variables into one weighted convolution no longer gives the two plain rough unweighted variables required in that estimate. The single-long-variable fundamental lemma likewise is not available at modulus \(>.5\) with each individual variable at most \(.25+o(1)\). No prime source has been artificially split into true prime factors.

## 3. Primary comparisons and the precise scope

[Maynard III, Theorems 1.1–1.3](https://arxiv.org/html/2006.08250#S1) allow the needed varying residue, but do not include even our bare \(qr\) support: the full-prime weak bound and the minorant need an appropriate small factor of width at most approximately \(1/10\), absent here; his almost-uniform full-prime result has two genuine required small slots (one \(<1/20\), the other \(<1/10\)) with positive-power lower levels, unavailable for two primes of widths \(\ge1/8\). [Maynard I](https://arxiv.org/abs/2006.06572), [Runbo Li's two-factor bilinear Theorem 1.1](https://arxiv.org/abs/2602.20917) and [Pascadi's Theorem 1.3](https://arxiv.org/html/2505.00653#S1) do not authorize substituting the varying residue \(a=N\) into a fixed-\(a\) result with constants depending on \(a\). In addition the balanced \(qr\) weight here is not triply well-factorable just because it is a fixed two-box product. In the concrete histogram, every \(qr\) at the top includes primes of widths \(>.246\), bigger than the equal thirds of any level comparable to its actual tested power; even if a larger named level is asserted, each of these two primes must still fit one slot individually. Thus one cannot simply apply a headline weighted prime level to the actual hypothesis.

The obstruction is to the direct full-atom prime treatment with the current physical rails, not to the genuine over-root tag estimate itself. It supplies a concrete next estimate that would defeat the specific repaired prime-axis transport: an actual residue-\(N\) prime-source result on q,r,d in the stated windows, or a different rank-sensitive statistic that controls the missing tagged deficit without these direct atom rails.