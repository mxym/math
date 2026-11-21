# Full local absorption using three true markers and a favorable rank-six row

This strengthens the rank-six comparison of
[SameEquationRankCompensation.md](SameEquationRankCompensation.md).
The adverse contribution of a specified genuine high \(h\)-Vaughan
chamber is absorbed *entirely* by disjoint original true rows whose
unopened coefficients are negative. Consequently the nonnegativity
obstruction of the rank-four comparison does not apply. It is not a
bound for the compensating rows' actual artificial complements.

Keep \(N=2x,L=\log x,n=sq\in(x/2,x]\), \(m=N-n\), the unit condition
\((n,N)=1\), the original \(W_s(q)=(1-t)(1-2t)^2,\ t=\log s/\log n\),
and \(F(m)=C^\dagger(m)\) of the original subpower half switch
[ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md).
Fix \(0<\eta<.002\) and \(\rho=\eta/10^5\).
An exponent band means the radius-\(\rho\) interval in \(\log_x\).
Use the six true independent prime labels
\[
 Q:\quad n=s_1s_2s_3 R_1R_2R_3,\qquad
           (.139,.101,.106,.155,.190,.309).
 \tag{1}
\]
Thus all three \(s_i\) are valid true short markers. Select the fixed
band for a genuine reflected prime \(p\) at \(.4305-\eta\).
It lies within the balanced \(p\)-band of the first marker's true
semiprime row since \((1-.139)/2=.4305\) and \(1.5\rho<\eta/1000\).

Start with four disjoint **original true-prime rows**:
* \(T_2\): \(s=s_1\) in band 1, \(q\) prime, and \(m=p h\) for genuine prime \(h\).
* \(T_{6,i}\), \(i=1,2,3\): \(s\) in \(s_i\)'s band, \(q\) prime, and
\[
 m=p h,\quad h=A_1 A_2 A_3 D E,\qquad
 (\log_x A_1,\log_x A_2,\log_x A_3,\log_x D,\log_x E)
       \text{ in bands }(.0335,.034,.0345,.073,.3945+\eta).
 \tag{2}
\]
All labels in (2) are true, distinct primes. The \(p\)-band is fixed
on all four inputs; it does not depend on the presence of any other
marker inside a true \(q\). Each row contributes its original
\(W_s(q)F(m)\). Distinct reflected ranks or distinct \(s\)-bands make
these four subsets of the original sum disjoint.

## 1. Independent whole-row q exchanges

Use the exact Möbius-only centered coefficient (2) in
[SameEquationRankCompensation.md](SameEquationRankCompensation.md).
On \(T_2\) keep the original balanced cutoffs
\(c_s=(1-\log_xs)/2,\ U_q=x^{c_s-4\eta}, V_q=x^\eta,
B_q=x^{c_s+5\eta}\).
On \(T_{6,i}\) choose
\[
 U_q=x^{.199},\quad V_q=x^{.001},\quad
 B_q=x^{1-\gamma_i-.197},\qquad
 (\gamma_1,\gamma_2,\gamma_3)=(.139,.101,.106).
 \tag{3}
\]
Then \(Z=q/B_q\) has exponent \(.197+O(\rho+1/L)\) in (3), and in
all four rows \(B_q^2>q,\ V_q<Z<U_q\) with \(Z/V_q\) polynomial.
The whole transfer in §1 of the cited note gives the same sums up
to \(O_{A,\eta}(xL^{-A})\), specifically **before** imposing the
common profile \(Q\).

For clarity, the independent SW slot of [Lichtman, arXiv:2309.08522v1,
Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) is
the true \(p\), with the other slot the independent specified
product \(h\), of labelled multiplicity one by disjoint bands.
The literal modulus slots \((a,s,1)\) have
\(\log_x a\le c_s-3\eta+o(1)\) in \(T_2\) and
\(\log_x a\le.200+o(1)\) in (3); the unit slot is again the
single integer 1. The actual residue is \(N=2x\).
The margins \(v<\beta\), \(2\beta+\alpha<1\), with
\(v=\log_x a,\ \beta=\log_xp,\ \alpha=\log_xs\), follow with
\(2\eta-O(\rho)\) reserve at the tight \(s_1\) band.
The last two rails in (3) of the cited note have left sides
at most \(1.775\) and \(1.69\) for large \(x\), under their
upper bound 2. The same exact masks, divisor-edge freezing,
the \(+\mathfrak S(Nsm),-\mathfrak S(Nsm)\) harmonic cancellation,
and power-small ordinary prime-power errors apply unchanged.
This uses no estimate for primality of the long \(h\)-slot.

On \(Q\) put \(q_i=n/s_i\), \(W_i=W_{s_i}(q_i)\).
For \(T_2\), the five true factors of \(q_1\) have exactly two
pairs above the two close half cutoffs, with exponents \(.464\)
and \(.499\), and the other eight pairs are below both cutoffs
(their maximum exponent is .415). The corresponding two
complementary triples are below both, all other triples above.
All singletons are below and all four-fold products above.
All comparisons are strict for all the stated \(\eta,\rho\);
in particular \(Z\) is at exponent at least \(.4205+o(1)-\rho\).
The two short-divisor sets \(d<Z\) and \(d\le U_q\) therefore
coincide. All \(q_1\) labels exceed \(V_q\). In (4) of the
cited note, switching the \(P\)-sum in each short part gives
\[
 {\cal C}_{s_1}(q_1)
 =-\sum_{d<Z,\ d\mid q_1}\mu(d)=-\{1-5+8-2\}=-2 .
 \tag{4}
\]
In detail the first sum has factor \(-\mu(d)\log(q_1/d)\)
for each \(d\le U_q\); the deleted \(d<Z/P\) portion at \(a=dP\)
gives \(\mu(a/P)\log P\), totaling \(-\mu(a)\log a\) for
each \(a<Z\). This is for the exact composite \(q_1\).

For each \(T_{6,i}\) on the same \(Q\), (3) makes four true
singletons \(<Z<U_q\), the largest singleton \(R_3>U_q\),
and every pair \(>U_q\). In the inner \(d\)-sum of formula (4)
of the cited note, \(P\ne R_3\) then allows precisely the three
*other* short singletons, since every two-factor product exceeds
\(Z\). At \(P=R_3\), it allows \(d=1\) and the four short
singletons. In both cases the inner Möbius sum is exactly \(-3\).
Hence the centered coefficient is \(+3\) for each of the three
separate compensating rows on the same physical equation.

## 2. True h expansion and the strict identical-equation sign

On \(Q\) in opened \(T_2\), \(F\) from the original true
semiprime row is \(-2\log p\) and the \(q_1\)-coefficient is
\(-2\). Insert \(\Lambda(h)/\log h\) on this branch in place
of the \(h\)-prime indicator, with only a power-small error
by the same \(p\)-times-prime-powers count as in the previous note.
This branch is now \(4 W_1(\log p)\Lambda(h)/\log h\).
Use \(U_h=x^{.150},V_h=x^{.0003}\) in the classical
\(h\)-Vaughan identity.

For the actual two short pieces on \(p e\mid m\) use [Jain,
arXiv:2611.21136v1, Proposition 3 and (3.1)](https://arxiv.org/html/2611.21136v1#S3)
in its independent arbitrary triple form, as in
[TrueRankFiveReflectedTypeI.md](TrueRankFiveReflectedTypeI.md).
Here are the **actual independent groups** for the six genuine
labels in (1). In each assignment a digit 0/1/2 means allocation
to source slot \(N/L/M\), respectively; the last column is the
logarithmic modulus range for the actual \(p e\):
\[
\begin{array}{c|c|c}
\text{assignment}&(\log_x N,\log_x L,\log_x M)&\log_x(p e)\\\hline
(2,1,1,1,0,2)&(.190,.362,.448)&[.499,.5515]\\
(2,1,2,0,2,1)&(.155,.410,.435)&[.5405,.5645]\\
(2,2,1,0,2,1)&(.155,.415,.430)&[.5555,.5695]\\
(1,1,2,1,0,2)&(.190,.395,.415)&[.5655,.5845]\\
(1,2,1,1,0,2)&(.190,.400,.410)&[.5805,.5895]
\end{array}
\]
The notation \(N,L,M\) inside the middle column denotes the
source's slot lengths, not the target or its logarithm.
[The rational check](check_full_favorable_rank_six_absorption.py)
verifies every rail with strict reserve at both endpoints of
each chosen interval. The ordinary full-scale convolution BV joins
below .4995. The grouped coefficients are independent, 1-bounded
and unique by disjoint prime bands; changing the scale by a dyadic
factor or the boxing width \(O(\rho)\) fits the reserves. For each
fixed modulus the omitted low nonprincipal characters are absorbed
by ordinary SW on one actual independent prime label, exactly as
in the cited Type I proof. This covers the actual largest
\(\log_x(p U_hV_h)<.581\).
The same finite masked \(\mu/\phi\) centers replace the two short
pieces by their actual reduced main, with factor \(4\) rather than
\(12\) in (6) of the preceding compensation note. The second
short piece has zero center. No \(h\)-prime count is used to
justify these progression estimates.

The high coefficient
\({\cal H}(h)=\sum_{d k\mid h,\ d>U_h,\ k>V_h}\mu(d)\Lambda(k)\)
on the actual shape (2) equals \(+\log E\).
Indeed \(z=A_1A_2A_3D\) has exponent .175 and each of its proper
divisors exponent \(\le.1415\) up to the small band widths, so only
\(d=z\) qualifies at \(k=E\) and its Möbius sign is \(+1\).
For \(k\mid z\) prime the qualifying terms have
\(d=E d'\), \(d'\mid z/k\), whose signed sum is zero.
Every term in this calculation has \(d k>x^{.159}\) for large \(x\),
even if the initially removable low-product section is taken out.

On the **original true** \(T_{6,i}\) profile the exact half coefficient
is given by the same odd-complement derivation as (5) of the previous
note, with \(\Delta=(\log h-\log p)/2\):
\[
 F(p h)=4\sum_{d\mid h}\mu(d)(\Delta-\log d)_+
       =4\bigl(\Delta-\log(A_1A_2A_3)\bigr)
       <-.121 L .
 \tag{5}
\]
The largest tiny pair has exponent .0685, below
\(\Delta/L=.0695+\eta+O(\rho)\), their triple has exponent .102,
and \(D\) at .073 is above \(\Delta\). All half-cut gaps are
strict; since the shapes are polynomially rough the omitted
small-cut correction terms are exactly zero. Thus the true
\(T_{6,i}\) sums are nonpositive prior to any opening.

After their three **separate whole exchanges**, take \(n\in Q\)
in all these rows. On exactly the same physical \(n+m=N\),
the three actual terms add to
\(3 F(p h)(W_1+W_2+W_3)\). Using \(n\asymp x\),
the exact cubic gives \(W_2>1.20 W_1\), \(W_3>1.20 W_1\) for
large \(x\). For example compare \(W(.1011),W(.1061)\) with
\(W(.1389)\) by the monotone cubic. The adverse original
\(T_2\) high term here is \(4W_1(\log p)\log E/\log h <1.200 L W_1\).
Thus their combined coefficient is
\[
 4 W_1\frac{\log p\log E}{\log h}
   +3F(p h)(W_1+W_2+W_3)
                    < - .034 L W_1.
 \tag{6}
\]
The rational check verifies both strict numerical inequalities.
The compensation uses each of the three existing original rows
once, not an artificially duplicated weight.

## 3. Scale and unavoidable limits

Exactly as in §4 of the preceding compensation note, choose the
two product sizes \([.70X,.73X]\), \([1.20X,1.24X]\) in their
independent prime labels. They have mutually disjoint prime bands,
so the unit condition is automatic and every actual target is even.
PNT for the last prime in each product and prime harmonic masses
for the others give \(\gg_\eta X/\log X\) integers in each family.
Thus for at least one actual even \(N\in[1.90X,1.97X]\) in each
large such interval the matched coefficient in (6) has magnitude
\(\gg_\eta \mathfrak S(N)x/L\), using the classical bounded average
of the positive singular series. This is not a uniform lower bound
at each target.

Starting from the four true rows, their exact replacement is
the literal short reduced main on \(Q\) above, the joint physical
part (6), the rest of the high \(h\)-row on \(Q\), and the four
artificial \(q\)-rows outside \(Q\), with arbitrary log-small error.
Unlike rank four, none of the three true compensating inputs has
a **nonnegative** sum forcing its artificial complement to pay back
the whole matched negative part. Their actual outside-\(Q\) part
can still be positive. The result closes a selected high chamber
in this combined signed bookkeeping, not the aggregate signed bound
and not strong Goldbach.

**Dated comparison.** [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) gives a different conditional arithmetic compensation; [Jain, November 16 v1](https://arxiv.org/abs/2611.21136) supplies the existing triple dispersion used here. The local full absorption uses original distinct orientations at the same target and does not bound the unreconciled outside-profile part.
