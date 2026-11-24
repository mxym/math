# A genuinely exterior rank-five negative arm pays a new fixed-target Y × D block

Research note, 2026-11-24. Keep the same actual even \(N\), literal \(x+y=N,\ x/N\in J\Subset(1/3,2/3),\ (x,N)=1\), \(L=\log N\), \(M=|J|N\mathfrak S(N)\), sharp CQ \(H=V_{\rm raw}-\Pi\) and literal \(R_J=\langle H,H\rangle+o(M)\). Let \(\beta=.0002\), \(Y=B_0+C\), and \(\Gamma_-=A_{\rm old}+W+Z+G\) as in [the compact bilateral result](CQCompactBilateralFavorable.md). Define \(K=H1_{\{P^->N^\beta\}}+\Gamma_-+Y\), the original compact signed receiver with those three one-arm supports removed. The previous .0378 positive paid component and recently isolated literal \(Y\times Y\) block \(>.04456M\) are kept, with no reuse of their rows.

**Result.** There is a genuine remaining rank-five negative weight \(D\le[-K]_+\), defined below, such that
\[
 \frac{\langle Y,D\rangle+\langle D,Y\rangle}{M}
 \ge .0683676835080644+o(1)>.06836+o(1).
\]
These are positive original \(H(x)H(y)\) products on the actual \(Y\times D\) and \(D\times Y\) rows. They are disjoint from \(Y\times Y\) and all the previously paid sets. The paid-sector lower can consequently be written as .15072 \(M\) **plus the still unestimated signed exterior**, not as a lower on \(R_J\) alone. There is no no-pair assumption.

## 1. Exact support and the three excluded true label types

On an actual squarefree rank-five input \(n\) with sorted distinct genuine primes \(p_1<\cdots<p_5\), use target-log angles
\[
 (t,v,w,a,b)=\big(\log p_1/L,\ldots,\log p_5/L\big).
\]
Define \(D(n)=-H(n)\) when \(\beta<t\le .04\) and the input meets **one** of these disjoint tests, and zero elsewhere:

1. \(v\le .005\).
2. \(v>.170\).
3. \(.005<v\le .170\) and \(w\le(1-t-v)/5\).

These are true divisors of the input, not a freely declared label model. In the first two cases the unique genuine second prime is outside the corresponding \(C\) bank. In the third case, if the actual \((p_1,p_2)\) is in some accepted half-open \(C\) cell with lower angular endpoints \(t_0,v_0\), its literal lower cutoff is
\[
 z=\max((1-t_0-v_0)/5,v_1)+.0001
    >(1-t_0-v_0)/5\ge(1-t-v)/5\ge w .
\]
Its quotient is divisible by the actual \(p_3\), so it violates \(P^-(n/(p_1p_2))>N^z\), irrespective of the true other factors. There is no choice of alternative named tags that rescues this: \(C\)'s true two labels are uniquely the two least primes because its quotient rough cutoff exceeds the entire named second bank. The boundaries \(v=.005,.170\) and \(t=.04\) respect the literal half-open rules; the last comparison is strict owing to the \(+.0001\). Thus \(D\) never meets \(C\).

The floor \(\beta<t\le .04\) also exactly excludes the tiny arm (\(t\le\beta\)), the old \(A_{\rm old}\) arm (\(t>.105\)), each of \(W,Z,G\) (all have \(t>.04\)) and \(B_0\) (also \(t>.04\)). This is a physical exclusion from the whole \(\Gamma_-\), \(Y\) and tiny unions on an individual arm; consequently a pair \(Y,D\) has no such earlier arm on either side. All earlier paid positive regions consist of both arguments with positive original \(H\). Here both original scores are strictly negative, so those regions are also disjoint.

To verify the sign and value of \(D\), let \(u_i=\log p_i/\log n\) be the true own-log widths, so \(\sum u_i=1\). Write \(F(s)=2(1-2s)_+^3-(1-2s)_+^5\) and \(\phi(s)=2(1-2s)^3-(1-2s)^5\). In odd rank the complement of an actual subset reverses the Möbius sign, and \(F(s)-F(1-s)=\phi(s)\); hence the rank-five detector divided by \(\log n\) is
\[
 \tfrac12\prod_{i=1}^5(1-\mathcal T_{u_i})\phi(0)
 =-\tfrac12\cdot32\cdot5!\prod_i u_i=-1920\prod_i u_i .
\]
All lower monomials disappear under five differences; the degree-five coefficient of \(\phi\) is \(+32\). There is no prime-term subtraction on a rank-five argument. Thus on the selected compact set \(D>0\) and \(K=H=-D\), as required.

## 2. Exact ordinary angular mass, not a paired density assertion

For true sorted fixed-rank squarefree log angles the ordinary prime-product PNT gives harmonic density \(dt\,dv\,dw\,da/(tvwab)\), where \(b=1-t-v-w-a\). There is no extra factorial in the sorted chamber: each product has exactly one sorted tuple. The factor \(1920tvwab\) of the **actual** normalized score cancels the harmonic product exactly. As usual the own-log and target-log vectors differ by \(O_J(1/L)\) on the fixed spatial interval. For ordinary mass the boundaries above have measure zero and all factors have a fixed positive floor, so compact inner/outer collars give the literal target-angle mass by the own-log simplex integral. This applies to this one-arm ordinary computation only; no product angular coupling is used on a fixed target.

For fixed \(t,v\), write \(X=1-t-v\), \(v\le w\le X/3\) and \(w\le a\le (X-w)/2\). Integrating the last free interval gives \((X-3w)/2\). The area after integrating over the full allowed \(w\) range is
\[
 F_0(t,v)=\frac{(1-t-4v)^2}{12}.
\]
Under \(w\le X/5\), the allowed area is
\[
 F_1(t,v)=\frac{(1-t-4v)^2}{12}-\frac{(1-t-v)^2}{75}
 \quad\text{if }v\le(1-t)/6,\qquad 0\text{ otherwise}.
\]
Indeed the ignored upper \(w\)-tail has \(X-3(X/5)=2X/5\). Let \(d=.005,\ h=.170,\ T=.04\), and define
\[
 I_0(t;\ell,r)=\frac{(1-t-4\ell)^3-(1-t-4r)^3}{144},\quad
 I_1(t;\ell,r)=I_0(t;\ell,r)
  -\frac{(1-t-\ell)^3-(1-t-r)^3}{225}.
\]
These are the two exact integrals over \(v\in[\ell,r]\). The three disjoint masses are respectively
\[
\begin{aligned}
 m_1/1920&=\int_\beta^d I_0(t;t,d)\,dt,\\
 m_2/1920&=\int_\beta^T I_0(t;h,(1-t)/4)\,dt,\\
 m_3/1920&=\int_\beta^d I_1(t;d,(1-t)/6)\,dt
                    +\int_d^T I_1(t;t,(1-t)/6)\,dt .
\end{aligned}
\]
There are no omitted \(t\)-cuts: \(t\le.04<h\), \(h<(1-t)/4\), and \(\max(t,d)<(1-t)/6<.170\) throughout the third range. The third branch auto-satisfies the upper second-bank bound in the ordinary limit. These polynomial integrals give exactly
\[
 \begin{array}{c|c|c}
 &\text{exact}&\text{decimal}\\
 1&218129409/122070312500& .001786916118528\\
 2&2695631353601/187500000000000&.0143767005525386\\
 3&448484456889719/1757812500000000&.2551378243639290\\ \hline
 \mathrm{total}&3815176514554627/14062500000000000&.2713014410349956 .
 \end{array}
\]
In particular the bulk of the removed rank-five mass comes from the *third-true-factor* quotient failure, not a narrow artificial endpoint.

## 3. Use the existing analytic receiver once and keep the exact residual

Apply the already independently checked compact-bilateral estimate (1) to \(U=D\). It fits all hypotheses: nonnegative bounded true angular function, rank exactly five, fixed polynomial least-factor floor \(\beta\), and only fixed angular inequalities. In the genuine over-root proof the source's actual unique least prime is the Siegel–Walfisz factor; the opposite \(Y\) receiver still uses its actual two tags and physical \(pqd\) moduli. No new sieve theorem, no equality of source/receiver tags and no same-target factor-angle independence are being assumed here. With \(c_Y=.125999484645652\), it follows in each orientation that
\[
 \langle D,Y\rangle/M,\quad\langle Y,D\rangle/M
 \ge c_Ym(D)+o(1)\ge .0341838417540322+o(1).
\]
The orientations may actually differ for nonsymmetric \(J\); both are proved. Since \(D\cap Y=\varnothing\), the two orientation supports \(D(x)Y(y)>0\) and \(Y(x)D(y)>0\) are physically disjoint and are both wholly within the old exterior. Unlike the \(Y\times Y\) calculation, *both* of these orientation pairings belong to the literal selected union. Their total is \(>.06836M+o(M)\).

The old residual exactly-one-Y contribution after removing both-Y was \(-2B_N(Y,K)M\), with \(B_N(U,V)=(\langle U,V\rangle+\langle V,U\rangle)/(2M)\). Since \(K+D\) now vanishes both on original removed arms and on D, this splits **exactly** as
\[
 -2B_N(Y,K)M
 =2B_N(Y,D)M-2B_N(Y,K+D)M .
\]
Book the first term just once; the new residual exactly-one-Y sum is \(-2B_N(Y,K+D)M\). It contains the true other receivers not in \(Y\) or \(D\). The raw-transfer formula with \(-2v\) after the earlier both-Y removal is not unchanged if the new booked block is pulled out; its right side must also subtract \(2B_N(Y,D)\). In the older centered test \(\widetilde B=B-m(B)R_{.04}/m(R_{.04})\), the restriction to this D support is **literally** \(-D\), because both \(Y\) and \(R_{.04}\) vanish there. Consequently this is a new measured strictly negative centered-receiver slice \(B_N(Y,\widetilde B\,1_{\{D>0\}})<-.03418+o(1)\), not a statement of sign for the entire centered test.

Since the old .0378 block, \(Y\times Y>.04456M\), and this \(Y,D\) union are physically disjoint, the same canonical identity yields
\[
 R_J\ge .15072M+
 \sum_{\substack{\text{formerly unpaid actual rows}\\
                 \text{excluding both-Y and the two }Y,D\text{ orientations}}}
        H(x)H(y)+o(M).
\]
The remaining sum is still signed; in particular neither the rest of exactly-one-Y nor the entire exterior is proved paid. The new bound remains an unconditional paired subchamber, not a claim about a hypothetical exceptional target or a whole Goldbach inequality.

Replay: run the standalone Node BigInt rational [check_cq_external_rank5_Y_block.js](check_cq_external_rank5_Y_block.js). It verifies every integration range sign, the closed fractions and the strict numerical lower with the independently validated \(c_Y\).
