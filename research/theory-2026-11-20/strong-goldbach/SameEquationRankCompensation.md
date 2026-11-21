# Same-equation compensation between two true short-prime orientations

Work with the original signed reflected statistic of
[ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), not a changed
symmetric detector. Put \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\),
\(m=N-n\in[x,3x/2)\), and retain \((n,N)=1\), equivalently \((m,N)=1\).
The original weight is \(W_s(q)F(m)\), where
\[
 W_s(q)=(1-t)(1-2t)^2,\quad t=\log s/\log n,\qquad F(m)=C^\dagger(m)
\]
at the original **subpower half switch**. This note proves two local
comparisons on identical physical equations after opening disjoint true
rows. In rank four the complement necessarily has a sign debt. In rank six
the true compensating row has favorable sign, so that particular debt is
absent. Neither comparison bounds all remaining rows.

Fix \(0<\eta<.002\), and let all exponent bands below have radius
\(\rho=\eta/10^5\); their centers are log exponents to base \(x\).
Select a six-prime profile \(Q\) with genuine, distinct labels
\[
 n=s_1s_2r_2r_3r_4r_5,\qquad
   (.11600,.10037,.17294,.18971,.19414,.22684).
 \tag{1}
\]
Write \(q_i=n/s_i\), \(W_i=W_{s_i}(q_i)\) on \(Q\).
Both \(s_i\) are legitimate distinct markers in the original band.
We have \(W_2\ge W_1>0\) because \(s_2<s_1\) and the derivative of
\((1-t)(1-2t)^2\) is \(-(1-2t)(5-6t)\).
Fix the band for true \(p\) at \(.442-\eta\), independently of the
actual \(s_i\). On the \(s_1\)-row this is within the old balanced band
since \(.442=(1-.116)/2\) and \(1.5\rho<\eta/1000\); the fixed
band also makes sense on a true \(s_2\)-row where \(s_1\) is not defined.

Define the following contributions to the original statistic. In each
of these five true rows \(s\) is a true prime in the indicated \(s_i\) band,
\(q\) is a true prime, and \(p\) is a true prime in its fixed band:
* \(T_{2,1}\): \(s\) in band 1, \(m=p h\) with \(h\) prime.
* \(T_{4,i}\) (\(i=1,2\)): \(m=p A B C\) with \(A,B,C\) prime at
  \(.137,.141,.280+\eta\).
* \(T_{6,i}\) (\(i=1,2\)): \(m=p A_1 A_2 A_3 D E\) with the five
  true prime exponents \(.027,.028,.029,.074,.400+\eta\).

These are disjoint true row families by the distinct \(s_i\) bands and
reflected ranks. Labels within each prescribed product are unique.
In the opened \(T_{2,1}\) below \(h=m/p\) can be composite.

## 1. Actual whole-q exchanges, before taking the intersection Q

For an \(s\)-row with \(U_q,V_q,B_q\) and \(Z=q/B_q\), use the
Möbius-only centered coefficient
\[
 {\cal C}_s(q)=\frac{1}{\log q}
 \sum_{\substack{r k\mid q\\r>U_q,\ k>V_q}}
    \bigl(\mu(r)-P_{B_q}(r)\bigr)\Lambda(k),\qquad
 P_B(r)=-\sum_{\substack{ab=r\\b>B}}(\mu*\mu)(a).
 \tag{2}
\]
For \(T_{2,1},T_{4,1}\) take the original \(c_s=(1-\log_xs)/2\),
\(U_q=x^{c_s-4\eta},V_q=x^\eta,B_q=x^{c_s+5\eta}\).
For \(T_{4,2}\) use \(U_q=x^{.436},V_q=x^{.001},B_q=x^{.465}\).
For \(T_{6,i}\) use \(U_q=x^{.247},V_q=x^{.001}\),
\(B_q=x^{1-\gamma_i-.244}\), \(\gamma_1=.116,\gamma_2=.10037\).
In all these cases \(B_q^2>q\), \(V_q<Z<U_q\) with \(Z/V_q\)
polynomially large.

For each true row separately, substituting (2) for the prime-\(q\)
indicator preserves the whole sum up to \(O_{A,\eta}(xL^{-A})\) for
every fixed \(A\). In particular **do not** impose that a row's \(q\)
contains the other short marker before making the exchange. To verify
that the earlier semiprime transfer extends to these two composite
reflected inputs, retain the physical progression
\(m\equiv N\bmod s a\), where \(a\le U_qV_q\) or \(a<q/B_q\).
The source for [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5)
has the actual \(p\) in the independent short Siegel–Walfisz slot,
the product of all the other actual reflected prime labels as the
independent other slot, and modulus slots \((a,s,1)\).
The grouped coefficient has multiplicity at most one by its
disjoint factor bands. None of those factor bands depends on \(p\);
only the central product cut is not separated initially.
The true \(N\)-unit condition factors over the source. The third
modulus slot is the single integer 1 in the source's dyadic convention
\((Q_3,2Q_3]\) with \(Q_3=1/2\). The residue is \(N=2x\), not zero
or a fixed proxy.

At \(\beta=\log_xp,\alpha=\log_xs,v=\log_xa\), the four rails with
\(\theta=7/32\) are
\[
 v<\beta,\quad 2\beta+\alpha<1,\quad
 \theta+\beta+v+5\alpha<2,\quad
 (1+2\theta)\beta+v+(5-2\theta)\alpha<2 .
 \tag{3}
\]
On the old \(i=1\) rows \(v\le c_s-3\eta\), so the first two
margins are \(2\eta-O(\rho)\). On the \(i=2\) rank-four row
\(v\le.437+o(1)<\beta-.0029\), \(2\beta+\alpha<.985\).
On either rank-six row \(v\le.248+o(1)\), and the second margin
is at least \(2\eta-O(\rho)\). The final two left sides are always
\(<1.70\) and \(<1.62\), respectively. All margins absorb the true
dyadic scale changes \(O(1/L)\).
As in [BalancedSemiprimeLongFreeDescent.md](BalancedSemiprimeLongFreeDescent.md),
the actual \(p\) satisfies the auxiliary SW condition on each prime
interval, including the physical unit mask. Excluding any of the
at most \(O(1)\) actual \(p\) dividing \(N\) is an independent
restriction; SW truncation by auxiliary polynomial size modulus
removes at most \(O(1)\) true primes in such a band.

Using the exact short identity and the collapsed reciprocal identity
of [BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md),
for each fixed \(s,m\) the two harmonic centers before division by
\(\log q\) are \(+\mathfrak S(Nsm)\) and \(-\mathfrak S(Nsm)\).
They use the same true \((a,Nsm)=1\) mask, and overlap with \(s\mid a\)
can be removed in the harmonic sums for \(O(L^C/s)\).
The finite masked \(\mu/\phi\) moments evaluate these centers exactly
to arbitrary log accuracy; all endpoints \(U_q/k,Z/k\) for the
subtracted prime powers \(k\le V_q\) are polynomially large. No
primality of the grouped long input is used in this calculation.

Specifically, the central shape and all smooth log weights are separated
by the same arbitrarily fine meshes as in the preceding transfer.
The \(F(m)\) on each of the actual input profiles is a smooth linear
combination of log terms, given in §2 below. For an edge \(a<q/B_q\),
first freeze \(s\) and central \(m\) on relative \(L^{-K}\) boxes.
At fixed \(s\), an altered pair of actual divisors has \(q=ab\) and
\(b=B_q(1+O(L^{-K}))\); there are \(O(x/(sB_q))\) possible \(a\)
and \(O(B_qL^{-K}+1)\) possibilities for \(b\).
Summing in the \(s\) dyads, then applying divisor-moment bounds, makes
this \(O_A(xL^{-A})\) for large \(K\), as for the harmonic edge.
The moving \(U_q\) boundary is handled by the same thin divisor and
multiple count. The prime-power error when inserting
\(\Lambda(q)/\log q\) is power-small by summing the number of
proper powers \(q\asymp x/s\). This establishes the transfer on
each of the original five whole rows.

## 2. Coefficients on the same physical labels

In the shape (1), the maximum pair exponent among factors of each
\(q_i\) is at most \(.42098+2\rho\), and the minimum triple exponent
is at least \(.46302-3\rho\). Under the rank-four and \(T_{2,1}\)
cuts, both \(Z\) and \(U_q\) are strictly between every such pair
and triple. The exact squarefree special case of (2) gives
\[
 (\log q){\cal C}_{s}(q) =
 -\sum_{\substack{P\mid q\\P>V_q}}\log P
      \sum_{\substack{d\mid q/P\\Z/P\le d\le U_q}}\mu(d).
 \tag{4}
\]
All outer prime labels exceed \(V_q\). The inner sum contains exactly
the six pairs of the four other prime labels. Thus \({\cal C}_s=-6\)
on the \(Q\)-part of \(T_{2,1}\) and both rank-four rows.
Under the separate rank-six cuts all singletons are below \(U_q\),
all pairs above \(U_q\), all \(P<Z\), and every pair including \(P\)
is above \(Z\). So the inner sum instead contains exactly the four
singletons, and \({\cal C}_s=+4\) on the \(Q\)-part of both rank-six rows.

For each reflected shape all actual divisor thresholds have a fixed
gap around the half of \(\log m\). For the rank-six shape this follows
also from the \(\Delta\)-comparisons below. Hence the correction terms in
formula (10) of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md)
are exactly absent on these inputs. By even-rank complement pairing,
\(F(m)\) is twice \(\sum_{d\mid m,\log d<(\log m)/2}\mu(d)\log d\).
In rank two this is \(-2\log p\). In rank four all short pairs
are exactly the three pairs among \(A,B,C\); the three-label product
has exponent \(>.55\), and any pair containing \(p\) has exponent
\(>.57\). Thus \(F(pABC)=2(\log m-2\log p)>0\).

In rank six put \(h=A_1A_2A_3DE\), of odd rank, and
\(\Delta=(\log h-\log p)/2\).
The short divisors of \(m\) containing \(p\) contribute
\(-\sum_{d\mid h,\log d<\Delta}\mu(d)(\log p+\log d)\)
before doubling. For the other short divisors, complement in
\(h\) and use \(\sum_{d\mid h}\mu(d)\log d=0\).
This gives the contribution
\(\sum_{d\mid h,\log d<\Delta}\mu(d)(\log h-\log d)\).
In this range only the empty divisor, singletons and pairs
of \(A_1,A_2,A_3\) are below \(\Delta\): their largest pair has
exponent .057, while \(\Delta/L=.058+\eta+O(\rho+1/L)\)
and their triple has exponent .084. In particular the gaps are strict
on all possible divisors and the original correction terms really vanish.
Thus
\[
 F(p h)=4\sum_{d\mid h}\mu(d)(\Delta-\log d)_+
       =4\bigl(\Delta-\log(A_1A_2A_3)\bigr)<-.09L.
 \tag{5}
\]
The arithmetic sign applies on the whole true rank-six input, with
no \(Q\)-restriction.

## 3. Open the actual h only on the Q-part of the first row

After opening \(q\) on the whole \(T_{2,1}\), select \(n\in Q\).
Here the weight is \(12W_1(\log p)\Lambda(h)/\log h\), \(p\mid m\),
up to the negligible proper \(h\)-powers (there are at most
\(O(x^{.443+.281}L)\) pairs of candidate \(p\) and proper power \(h\)).
The \(F(m)\) from the initial true rank-two row was \(-2\log p\);
it is this coefficient that stays in the \(h\)-expansion, not the
physical \(F(m)\) for the newly admitted composite \(h\).

Apply the exact \(h\)-Vaughan identity with \(U_h=x^{.1495}\),
\(V_h=x^{.0003}\). The two short pieces give, up to
\(O_{A,\eta}(xL^{-A})\), the usual literal reduced principal term
\[
 {\cal P}_Q=12\sum_{n\in Q}
  \sum_{\substack{p\text{ true in its band}\\p\nmid N}}
      W_1\,\frac{\log p}{\log((N-n)/p)}
                   \frac{\mathfrak S(Nnp)}{p-1}.
 \tag{6}
\]
The short harmonic calculations are those of
[TrueRankFiveReflectedTypeI.md](TrueRankFiveReflectedTypeI.md):
the first finite derivative has the displayed main, the second
piece has zero main. Their source uses the actual progression
\(n\equiv N\bmod p e\) with \(e\le U_hV_h\), not a prime-pair
estimate. To check the applied distribution, the source's first
two labels \((.12000,.09637)\) are now \((.11600,.10037)\).
Those two labels are in *one group in each* of the five independent
allocations of Jain's Proposition 3. Thus their combined exponent
.21637 leaves every rail and their contiguous \(.5934\) modulus
endpoint unchanged. Our \(p e\) exponent is \(<.592\);
the narrower band fits the existing finite margins. The change
in \(W_1\) and \(1/\log((N-n)/p)\) is just their exact smooth
test on the now chosen source. All unit masks are those of (6);
there is no \(p\mid N-n\) restriction in this reduced mean.

The true remaining high coefficient is
\[
 {\cal H}(h)=\sum_{\substack{d k\mid h\\d>U_h,\ k>V_h}}\mu(d)\Lambda(k).
 \tag{7}
\]
For \(h=ABC\), \(A,B<U_h<C\) and \(AB>U_h\).
At \(k=C\) only \(d=AB\) qualifies, contributing \(+\log C\).
At \(k=A\) or \(B\), the two eligible terms each contain \(C\)
in \(d\) and cancel exactly. Thus \({\cal H}(ABC)=\log C\).
At \(h=zE,\ z=A_1A_2A_3D\), the exponent of \(z\) is .158
and each proper divisor has exponent at most .131, up to
the harmless box widths. At \(k=E\), only \(d=z\) qualifies
and \(\mu(z)=1\). For prime \(k\mid z\) the terms are exactly
\(d=E d'\), \(d'\mid z/k\), with signed sum zero.
Thus \({\cal H}(zE)=\log E\). Every term just used actually has
\(d k>x^{.1505}\), so it remains high if the previously removable
initial \(d k\le x^{.1505}\) portion is taken out.

On a fixed \(n\in Q\) with the rank-four physical \(m=N-n=pABC\),
combine its (7) contribution and its two \(T_{4,i}\) contributions
after their own whole exchanges. There is exactly one term per
orientation, from already present distinct original true rows. Their
joint coefficient is
\[
 12W_1\frac{\log p\log C}{\log h}
 -12(W_1+W_2)(\log m-2\log p)\ \le -.09 L W_1 .
 \tag{8}
\]
Indeed \(W_2\ge W_1\), and
\[
 2(1-2(.442+\rho))
   -\frac{(.442+\rho)(.282+\rho)}{.558-\rho}>.0085 .
\]
For the rank-six chamber the \(h\)-high term is
\(12W_1\log p\log E/\log h\le3.83 L W_1\).
The two distinct \(T_{6,i}\) terms give
\(4F(p h)(W_1+W_2)\le-.72 L W_1\).
Consequently at least **18 percent** of the adverse coefficient
of this genuine high subfamily is removed in the joint residual.

This is an exact rewriting of the sum of the five original true
rows: (6), plus the two physical joint contributions above, plus
the high part of the \(Q\)-row of \(T_{2,1}\) outside these two
\(h\)-shapes, plus all five opened \(q\)-rows outside \(Q\), with
the stated small error. No weights are invented and no term is
counted twice. The comparison does not estimate those complements.

## 4. Genuine scale and the difference between the two comparisons

For each of the two chambers separately, its physical matching
contribution has magnitude \(\gg_\eta M_N\),
\(M_N=\mathfrak S(N)x/(2\log x)\), for at least one even \(N\)
in each sufficiently large interval \([1.90X,1.97X]\).
This is not a pointwise lower bound on the population.
Use \(n\in[.70X,.73X]\), \(m\in[1.20X,1.24X]\), products of
the stipulated primes. For each product choose all but one label
in exponent bands of radius \(\rho/20\) at the same centers
relative to \(X\). The final label, by ordinary PNT in a fixed
relative interval at a fixed polynomial scale, has
\(\gg_\eta X/(\log X\prod\text{previous labels})\) choices.
PNT and partial summation give each preceding label a fixed
positive harmonic mass. Thus there are \(\gg_\eta X/\log X\)
distinct integers in each family. Their labels are disjoint
between families, whence \((n,m)=1\); both are odd and
\(N=n+m\) is even. The central condition holds at \(x=N/2\),
and the exponent changes from \(X\) to \(x\) are \(O(1/\log X)\).
The weighted pair sum over actual \(N\) is \(\gg_\eta X^2/\log X\).
Since \(\sum_{N\le 2X}\mathfrak S(N)\ll X\), this implies the
claimed scale for at least one \(N\).
For the latter classical estimate expand
\(\prod_{\ell\mid N,\ell>2}(1+1/(\ell-2))\); its divisor coefficients
summed with reciprocal divisor weight have a convergent Euler product.

In rank four the original \(T_{4,i}\) true sums are nonnegative
because \(F(m)>0\). Their opened \(Q\)-part is negative, so their
complementary opened part **must** pay back at least that magnitude
up to the transfer error. Thus (8) alone gives no aggregate gain.
In rank six the original \(T_{6,i}\) true sums are nonpositive
by (5), so this particular repayment constraint is absent.
Their actual complement can still be positive, and is not estimated
here. The rank-six computation gives a genuine same-equation
decrease on a selected adverse sector against an independently
favorable original row, not a bound on the full signed residual
or a verified Goldbach lower bound.

**Dated comparison.** [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) considers a conditional arithmetic compensation for a different prime filter, and [Jain's November 16 v1](https://arxiv.org/abs/2611.21136) supplies the dispersion input for the short terms. The result here is a local arithmetic pairing in the original signed statistic, with an unbounded complementary term and, for rank four, an explicit sign-forced debit. No global compensation or priority conclusion follows.
