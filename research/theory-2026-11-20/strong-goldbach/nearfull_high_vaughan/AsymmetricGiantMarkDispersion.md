# A signed asymmetric over-root block of the two genuine giant marks

Use \(N,J,L,x,y=N-x\) and \(M_N=|J|N\mathfrak S(N)\) as in
[the joint giant correlation](JointSharpGiantCorrelation.md).
Let \(F,G\) be fixed real smooth profiles on \([0,\infty)\),
with \(F\) compactly supported and \(G\) supported in \([0,b_G]\)
and constant on a fixed initial interval \([0,a_G]\), \(a_G>0\).
These profiles can be signed. Put
\[
 Q_F(m;x)=\sum_{d\mid m}\mu(d)F\!\left(\frac{\log(dN/x)}L\right)
\]
and analogously for \(Q_G(n;y)\). Every mark below is a literal
prime. On \(x+y=N\), \(x\in NJ\), keep \((x,N)=1\); consequently
\(x,y\) and all their factors are target units.

Fix two positive-width exponent intervals \(I_q,I_r\), and a
fixed margin \(\varepsilon>0\), such that throughout the rectangle
\[
  \alpha\in I_q,\quad \rho\in I_r:\qquad
  \alpha>\tfrac12+\varepsilon,\qquad
  \frac{56\alpha-17}{23}+\varepsilon\le\rho,\qquad
  \rho+b_G\le\alpha-\varepsilon.                                  \tag{1}
\]
The allowed \(q,r\) windows can have arbitrary actual subinterval
endpoints within the corresponding power-scaled ranges \(N^{I_q}\)
and \(N^{I_r}\). When viewing the result in a calibrated giant
remainder, also intersect with its original true lower mark gates.

**Theorem.** For every fixed \(D>0\), the full physical signed block
\[
 \sum_{\substack{x=q m,\ y=r n,\ x+y=N,\ x\in NJ\\(x,N)=1\\
                  q,r\ {\rm prime},\
                  \log q/L\in I_q,\ \log r/L\in I_r}}
         (\log q)(\log r) Q_F(m;x)Q_G(n;y)
                           =O_D(NL^{-D})                         \tag{2}
\]
uniformly for large even \(N\). Both \(m,n>1\) automatically on
this chart. This covers the entire cofactor populations and
does not require either to have bounded rank or to be rough.
The result holds, for example, with both marks above \(N^{.510}\).
It cancels an actual asymmetric signed portion, not the surviving
full giant covariance.

There are also choices on this same chart with a genuine positive
subpopulation of size \(\gg_J M_N/\eta\), at each sufficiently
small fixed \(\eta>0\): \(x\) can be a true squarefree triprime,
and \(y=r n\) with every factor of \(n\) exceeding \(N^\eta\).
This uses flat profiles with \(F(0)=G(0)=1\) and \(b_G<\eta\).
It is a portion of (2), not additional positive credit or a
Goldbach implication.

## 1. The actual signed transfer, including spatial endpoints

Open the \(n\)-score at the genuine short divisor \(e\mid n\).
It imposes the actual progression \(q m\equiv N\bmod r e\),
and has \(e\le N^{b_G}\), since \(y<N\).
The modulus is the product \(r e\).
The inequalities (1) imply \(b_G<\rho\); in particular \(r\)
cannot divide \(e\). To verify this, the region forces
\(\alpha<(17/33)\), \(\rho>(56/23)/2-17/23=11/23\), while
\(b_G<\alpha-\rho<17/33-11/23<.04\).
All moduli used in the actual sum are target units, so the
literal \(N\) residue is reduced.

Freeze the real \(x\)-argument in both profiles with a log-fine
central partition of mesh \(L^{-B}\).
On a cell with representative \(x_0\) the actual \(m\)-coefficient is
\[
  1_{(m,N)=1}\sum_{d\mid m}\mu(d)
             F\!\left(\frac{\log(dN/x_0)}L\right),
\]
which is divisor-bounded. The longer independent coefficient is
the true target-unit prime \(q\) with normalized log weight
\(\log q/L\) and its actual interval endpoints. Its length
scale is \(T\asymp q\), and it satisfies Siegel–Walfisz with
the allowed auxiliary unit mask: ordinary prime Siegel–Walfisz
at small log-power moduli, removal of the finitely many forbidden
prime factors, and the trivial progression bound for larger
moduli. There is no such assumption on the shorter \(m\)-weight.

Apply [Fouvry–Radziwiłł, Theorem 1.1](https://arxiv.org/abs/1812.00562v2)
on independent intervals in \(m,q\), with \(X_0\asymp_J N\).
The modulus dyad \(R\) satisfies
\[
                  T^{56/23}X_0^{-17/23+\delta}\le R
                                     \le T X_0^{-\delta}
\]
for a sufficiently small fixed \(\delta>0\) after \(\varepsilon\),
since the exponent of \(r e\) is between
\(\rho\) and \(\rho+b_G\). All aspect-ratio constants are absorbed
by the fixed margin. The literal residue \(N\) satisfies the
fixed-factor extension \( |N|\le C_J X_0\), verified in
[the balanced semiprime transfer, §1](../balanced_semiprime_giant_cross/Proof.md)
from the primary proof. That same verification uses only the
size and units of the residue and the stated divisor bounds,
not primality of the shorter coefficient.

For completeness the frozen central product interval can be
restored as in that proof. Within each fixed \(x\)-cell use a much
finer log mesh on \(m,q\), chosen after the number of \(x\)-cells,
and discard the touching product boxes. Their actual \(x\)'s
lie in a union of relative strips of arbitrarily small log-power
total size. Since \(q>N^{1/2+\varepsilon}\), at most one such
true \(q\) divides each \(x\). At a strip point the actual
\(r,e\) contribution before log weights has at most fixed
divisor-power multiplicity in \(y=N-x\). Ordinary divisor
moments and Cauchy pay the sum over these strips. The reduced
principal has only \(\sum_{k\le N}\tau(k)^{O(1)}/\varphi(k)\)
in extra harmonic cost, so the same thin strip pays it.
Moving \(x\)-arguments within their first cells costs
\(O(L^{-B})\) per divisor; the real crossed divisor moments again
apply. Exact interval subdivisions in \(q,r\) require no
unsupported short-interval prime asymptotic.

There are only fixed log powers of cells and dyads. The
Fouvry–Radziwiłł error is absolute over the allowed moduli, so
the true weights \(\mu(e)G(\cdot)\), the logs, and the possible
factorizations \(r e\) cost only fixed powers of \(L\) and
divisor powers. Indeed the true congruence sum,
even with \(|\alpha_m|\le\tau(m)\), is bounded in total with
any fixed modulus divisor power by \(NL^{O(1)}\):
each \(k\) divides \(N-x\), and the physical \(x\)-row has
at most the product of fixed divisor powers of \(x,N-x\).
The model is also \(NL^{O(1)}\), by the absolute
modulus harmonic and ordinary moments of \(\tau(m)\).
Cauchy between this bound and the arbitrarily small absolute
distribution sum absorbs the desired divisor weighting.
Thus every error is \(O_D(NL^{-D})\) after choosing accuracies
in this order.

Retain the exact reduced principal:
\[
 \sum_{x=q m\in NJ}(\log q)Q_F(m;x)
     \sum_{\substack{r\ {\rm in\ its\ true\ window}\\
                     (r,Nqm)=1}}\frac{\log r}{\varphi(r)}
     \sum_{\substack{(e,N q m)=1}}\frac{\mu(e)}{\varphi(e)}
                     G\!\left(\frac{\log(eN/y)}L\right).
\]
All original spatial variables have been restored; the
\(r,e\) unit masks used here are precisely those from the
reduced progression. The inner finite harmonic is
\(O_A(L^{-A})\), uniformly in the actual \(x=q m\):
its target-plus-short-factor mask \(N q m=Nx\le N^2\)
is allowed in the uniform signed harmonic estimate of
[the original giant reduction, §1](../giant_prime_divisor_remainder/Proof.md).
The complete zeroth harmonic is zero. Because \(G\) is flat on
\([0,a_G]\), the first modified arguments have \(e\gg_J N^{a_G}\),
and ordinary partial summation pays their signed tail to
arbitrary log accuracy. Summing the remaining genuine \(r\)
harmonic and the absolute \(q,m\) divisor weights retains
arbitrary fixed log saving. This proves (2).

## 2. A genuine positive subset inside the same zero block

For an explicit choice let
\[
 I_q=[.51395,.51405],\qquad I_r=[.51275,.51285],
\]
and use a lower sieve on \(n=y/r\) of support \(e\le N^{.0006}\).
These exponents fit the same fixed strict dispersion rails:
the largest lower rail is
\((56\cdot .51405-17)/23=.51246956\ldots\),
and the largest effective modulus exponent is \(.51345\),
below the smallest long exponent \(.51395\). Thus the proof
of the distribution step applies with this larger short
support for the lower sieve as well. Both true marks are
strictly above \(N^{.510}\). The exponents are illustrative,
not restrictions on the full region in (1).

Take the actual support
\(x=q p_1 p_2\) with \(p_1\) prime in
\([N^{.2395},N^{.2396}]\), \(p_2\) an actual prime in
\(NJ/(q p_1)\), and all factors target units.
The \(p_2\) exponent lies in a fixed band near \(.2465\)
disjoint from the other two. Use \(F(0)=1\) and support
below \(.01\); then \(Q_F(p_1p_2;x)=1\) for large \(N\),
so the actual marked \(x\)-score is \(\log q\).
The source has mass \(\gg_J N\) with this \(q\)-log weight:
apply ordinary PNT on the real fixed-ratio \(p_2\)-interval,
then \(\sum_q\log q/q\asymp L\) and the positive
\(p_1\) reciprocal harmonic. Deleting target-prime factors in
these polynomial slots costs a power. Its shorter coefficient
is now the genuine two-prime product in those disjoint ranges,
a special case of the earlier divisor-bounded coefficient.

For \(0<\eta\ll .0006\) fixed, use the ordinary dimension-one
positive lower sieve on \(P^-(n)>N^\eta\) with that support
\(e\le N^{.0006}\), then the same actual source distribution
on \(r e\). Primes dividing \(N\) are excluded from the
sieve; each tested small prime has conditional density
\(1/(p-1)\), as its modulus is coprime to the actual \(r\).
The tested small primes and \(r\) are disjoint from all
prime factors of this \(x\)-source. Thus the reduced
principal contains the full \(x\)-source mass and the usual
lower sieve density \(\gg \mathfrak S(N)/(\eta L)\), by
the large fixed ratio \(.0006/\eta\) and local Mertens.
The actual \(r\)-log harmonic has size \(\asymp L\).
This gives weighted count \(\gg_J M_N/\eta\) on these
very rows, with the two actual mark logs, after increasing
the \(N\)-threshold depending on \(\eta\).
One may additionally retain squarefree \(y\): \(r^2>y\)
and large repeated factors of \(n\) cost a power by direct
integer multiples at each actual \(r\).
Choose \(G\) flat with \(G(0)=1\) and \(0<b_G<\eta\).
Its marked quotient score is exactly 1 on these rough
\(n\)'s, because all nontrivial divisors exceed the
actual support. Both true marks are unique on their
respective inputs. The positive subset therefore lies
in the exact block (2). This is necessarily compensated
by the other physical terms of that block, not a
standalone reserve for the full covariance.

