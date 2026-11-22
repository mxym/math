# Inverse fourth moments in the raw complementary Vaughan sum

Use the exact low-cutoff raw sum of
[the complementary Vaughan partition](../raw_complementary_vaughan/Proof.md),
with \(V=\exp((\log\log N)^3)\), \(z=\exp((\log\log N)^2)\),
\(x=ab\), \(y=mcv=N-x\), and all its literal rough and unit masks.
Its weight is
\(\mu(a)\mu(c)\lambda_{>V}(b)\lambda_{>V}(v)Q_y(m)\).
For the present theorem, impose the actual raw cuts
\[
 N^{.501}\le a\le N^{.518},\qquad
 N^{.249}\le c\le N^{.251},\qquad
 N^{.355}\le m,v\le N^{.395}.                                  \tag{1}
\]

**Theorem.** The entire raw sum restricted to (1) is
\(O_{A,J_0}(NL^{-A})\) for each fixed \(A\) and every prescribed
even \(N\). This is an all-target signed deletion in the same
low-cutoff raw ledger. It is not an additional credit for an
overlapping long-label decomposition or the high-cutoff bank
analysis. No sign of the complementary raw sum is claimed.

The range is genuinely supercritical for the raw product:
\(\log_N(a m c)\ge1.105\) and
\(\log_N(mc)\ge.604\). In particular the first nonzero
reciprocal inequality in the earlier supercritical chart fails,
since \(.7(1.105)+.25(.604)-.85=.0745>0\).
Neither orientation of the earlier extreme-imbalance
Möbius B–V applies. A physical \(cv\) of exponent \(.625\)
can lie in the original giant interval. These are statements
about the geometric support, not a lower bound on the signed sum.

## 1. The literal four complementary terms

Expand each identity
\(\lambda_{>V}(n)=\log n-\sum_{f\le V,\,f\mid n}\Lambda(f)\).
On the left the log choice has \(f=1\) and weight
\(\log(x/a)\); otherwise \(b=fG_0\) and the weight is
\(-\Lambda(f)\). On the right the choices are \(t=1\)
with \(\log(y/(mc))\), or \(v=tK_0\) with \(-\Lambda(t)\).
Both labels, when present, are \(z\)-rough target units,
as are \(G_0,K_0\). Keep all four signed choices.
Use the same successive Bonferroni openings of the two
free \(z\)-rough variables as in the raw partition; they
give \(G_0=e_1G,\ K_0=e_2K_0'\). All label products and their
counts in these openings are \(V^{o(1)}\), and the same
positive omitted-label bounds are valid with (1).
Indeed each omitted label divides an actual \(x\) or \(y\);
the factorial reciprocal tail times the fixed physical
divisor envelope and Cauchy gives arbitrary log accuracy.

Put
\[
       A_0=a f e_1,\qquad F_0=t e_2.
\]
The true equation is now \(A_0 G+m c F_0 K_0'=N\).
For fixed \(f,t,e_1,e_2\) and the modulus \(A_0\), \(a\)
is determined, and is kept as a target unit with its
original \(\mu(a)\) and rough condition. Open
\(d\mid m,\ d<y/B\) and set \(m=dn\). The actual congruence is
\[
        nK_0'\equiv N\overline{dF_0}\,\overline c\bmod A_0.
                                                                  \tag{2}
\]
If \((dF_0 c,A_0)>1\) there is no row. In particular
one never changes the product modulus into an lcm.
The freely varying signed slot is \(c\), with
coefficient bounded by one including all its true
rough/unit masks. The two unweighted intervals
are \(n\) and \(K_0'=v/F_0\). Physical cutoffs
on \(m=d n\) and \(v=F_0K_0'\) stay literal.
The \(N\)-unit masks on \(n,K_0'\) may be opened and
truncated exactly as in
[the fourth-moment inverse angle](FourthMomentInverseAngle.md),
§2: a discarded target divisor at least \(N^\rho\)
divides \(y\), and the full physical tuple multiplicity
is still bounded by fixed divisor powers on \(x,y\).
The free integer \(G=(N-y)/A_0\) is already a target
unit on the retained support.

## 2. Square factors and the fourth moment

The only difference from the inverse-angle
estimate is that \(A_0\) need not be squarefree.
Since \(\mu(a)\ne0\), \(a\) is squarefree; \(e_1\)
is squarefree and coprime to \(af\).
The *full prime-power part* \(P_0\) of \(A_0\) at
primes occurring to exponent at least two divides
\(f\,\operatorname{rad}(f)\), so
\(P_0\le V^2=N^{o(1)}\). The rest is squarefree
and coprime to \(P_0\), and \(A_0\) is odd.
Every reduced conductor \(q=A_0/(j,A_0)\) inherits
such a coprime splitting, with the exceptional
factor \(q_0\mid P_0\).

In the full fourth-moment expansion use CRT.
At the exceptional factor \(q_0\) the unit inverse
numerators allow the ordinary complete Weil bound
\(|S_{q_0}(\lambda,h)|\ll\tau(q_0)\sqrt{q_0}\),
since \(\lambda\) is a unit even if \(h\) is not.
The four factors and the complete unit sum over
\(\lambda\bmod q_0\) cost \(q_0^{3+o(1)}\).
At the remaining squarefree factor use exactly
the three-pairing lattice of the inverse-angle proof.
In its normalized majorant this changes the prefactor
\(q^{5/2}\) by at most \(q_0^{1/2+o(1)}=N^{o(1)}\);
the matching divisors of the squarefree part still
satisfy \(e_1'e_2'e_3'\le q\).
The \(h=0\) term remains the Ramanujan sum \(\mu(q)\).
Thus (2) of the inverse-angle proof holds with its
unchanged \(N^{\rho+o(1)}\) factor.

Likewise, for \(g=(j,A_0)\) when passing to \(q=A_0/g\),
open on the inverse variable only the primes of \(g\)
*outside* \(q\); primes shared by \(q\) and \(g\) are already
excluded by its \(q\)-unit test. Every opened divisor
is therefore still a unit at the reduced conductor.
The Fourier \(1/g\) bound, the complete-period estimate
for large \(g\), and the injectivity of the reduced ratios
\((j/g)/c\) after fixing their genuine gcd are unchanged.
These facts do not require squarefreeness of the whole
modulus.

Now apply (3)–(4) of the inverse-angle proof to (2),
with its former signed slot \(a\) replaced by \(c\),
and its former modulus \(b\) by \(A_0\).
The true scale of \(A_0\) differs from \(a\) by \(N^{o(1)}\).
For fixed \(d,F_0\) the ratio invariance and the smooth
Fourier cutoffs hold also after the \(N\)-unit labels.
In particular \(\min(m,v)\ll N^{.3755+o(1)}\) by
\(m c v\asymp N\), and \(\max(m,v)\ll N^{.395}\).
Thus the three total exponents are still
\(.994375,.997625,.9905\), with the same
\(7\rho/4\) loss where applicable and additional
\(o(1)\) only. The \(a\)-sum counts at most
\(N^{.518}\) actual moduli at each fixed set of short
labels; the \(c\)-sum was already taken inside (4).
All short-label counts and \(d\ll S\) cost \(N^{o(1)}\),
including their fixed log weights. This gives a fixed
power saving for all nonzero frequencies.

## 3. Real endpoints and principal

Use a fixed relative log mesh on \(c,m,v\) with \(a\)
fixed by the modulus. At fixed \(a,d,f,t,e_1,e_2\)
all actual gates are axes or affine planes in logs,
including \(y>Bd\), \(cv\in I\) and \(y\) central.
Thus the positive smoothing and boundary counts of
the inverse-angle proof apply. Their area at fixed
integer \(c\) is \(O(MK L^{-F})\) before real changes
of variables; \(M,K\) here denote the physical
\(m,v\) scales. Divide by \(dF_0\) and the two
\(N\)-unit labels when passing to the model.
For the log choices, the weights
\(\log(x/a),\log(y/(mc))\) vary by \(O(L^{1-F})\)
on interior boxes, and both are \(O(L)\) on the fixed
central region. The \(\Lambda(f),\Lambda(t)\) weights
are constant on their fixed terms. The same positive
estimates pay their smoothing without using an
unsigned correlation hypothesis.

Restore all literal domain inequalities in the zero mode.
At fixed \(a,c\) and real \(m,v\), after the two unit
expansions its density is
\[
 \frac{\varphi(A_0)}{A_0^2}
   \left(\frac{\varphi(N)}N\right)^2\frac1{d F_0}.
\]
The outside units of \(a,c,f,t,e_1,e_2\) and compatibility
\((c F_0,A_0)=1\) are still required. The only remaining
\(d\)-condition beyond coprimality is \(d<T_y\); \(m\)
itself has no \(z\)-rough mask. Hence the signed inner
harmonic is precisely
\(\sum_{d<T_y,\,(d,A_0N)=1}\mu(d)/d=O_A(L^{-A})\).
Here \(T_y\asymp S\); the estimate is uniform in the
actual \(A_0,N,y\). The other model sums only cost log powers:
centrality leaves reciprocal \(a,c\) harmonics, the original
rough labels have absolute reciprocal sums of log size,
and the \(f,t\) weights use \(\sum\Lambda(f)/f,\sum\Lambda(t)/t\)
over the fixed short ranges (or the log choices).
Target-label and boundary model errors have the same
reciprocal, not cardinality, summations. This proves the
claim in the entire raw chart with all four choices kept.
