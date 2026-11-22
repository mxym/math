# A grouped uniform-residue shoulder after the common raw cuts

Use the common-cutoff double Vaughan identity (1) of the
[complementary short-label proof](../raw_complementary_vaughan/Proof.md).
In particular \(V=\exp((\log\log N)^3)\) is the cutoff on **both**
sides, and \(z=\exp((\log\log N)^2)\) is the actual rough cutoff.
At the fixed prescribed even target, reopen its two true long
divisor weights into the physical equation
\[
   x=a f g,\qquad y=m c h k=N-x,\qquad
   \mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m).
\]
All of \(a,f,c,h\) exceed \(V\), all of \(a,f,g,c,h,k\)
are \(z\)-rough, and \(x,y\) are target units.
The original central interval \(x\in NJ\), giant interval
\(c h k\in I\), unrestricted quotient \(m\), and literal short
score \(Q_y(m)=\sum_{d\mid m,d<y/B}\mu(d)\) are retained.

Fix independent dyadic boxes on \(a,f,m,c,h,k\).
The prime-side free coordinate \(g\) has no additional interval;
its actual \(z\)-roughness and target-unit masks are retained.
Let \(v_1\) be the **larger** scale exponent of \(a,f\), \(v_2\)
the smaller (base \(N\)). Choose a subset of the four right-side
factor slots \(\{m,c,h,k\}\), and let \(\beta\) be the exponent
of its product. Suppose it contains either \(m\) or \(h\) with an
individual fixed positive exponent, and that with fixed reserves
\[
 v_1+v_2>1/2,\quad 7v_1+12v_2<4,\quad
        v_1+2(v_1+v_2-1/2)<\beta<1-v_1.                         \tag{1}
\]
Then the signed contribution of this actual opened box is
\(O_A(N(\log N)^{-A})\) for every \(A>0\).
There is no small-radical hypothesis.

**A common-cutoff region not already paid.** Take exponents
\[
       a=.420,\quad f=.085,\quad
       m=.200,\quad c=.450,\quad h=.260,\quad k=.090 .
\]
Here \(g\) has central exponent .495, and the selected SW product
is \(m h\) at \(\beta=.460\), using the genuine \(\Lambda(h)\)
slot. The margin is \(.430<.460<.580\), with
\(7(.420)+12(.085)=3.96<4\). The \(m\)-only source has exponent
.200 and cannot meet (1), and the first modulus has the genuine
factorization \(a\times f\) rather than an arbitrary product.
The actual two free-coordinate outer products have exponents
.505 and .910. The **raw** \(a,mc\) exponents are .420 and .650:
their product exponent is 1.070, and the reciprocal condition's
first bound is \(.7(1.070)+.25(.650)-.85=.0615>0\).
The [raw asymmetric inequalities](../raw_complementary_vaughan/RawMobiusBV.md) \(u<(v-\log_N m)/2\) and
\(v<u/2\), with \(u=\log_N a,\ v=\log_N(mc)\), also both fail
at these center values. All stated inequalities persist on a fixed
small open neighborhood of this exponent shape. This is an
admissible geometric example, not a claim of signed mass or even
individual occupants in that box.

## Combining with the raw restrictions without an accounting change

The complementary proof sums its deletions in the common-\(V\)
identity *on raw gates in \(a,m,c\)*. On those gates it may use
\(\lambda_{>V}(n)=\log n-\sum_{j\mid n,j\le V}\Lambda(j)\)
on both sides. After those raw gates are removed, keep the
original \(\lambda_{>V}\) weights on the raw complement,
then reopen them using \(f,h>V\) as above. This is an exact
pointwise change before the signed summation, not an addition
of error bounds from different cutoffs.
A box to be subtracted from that complement is required to
lie **wholly** inside it. For example one may require, throughout
its \(a,m,c\)-ranges, \(a(mc)>N/V^3\) and fixed strict failure
of the reciprocal or other previously removed raw inequalities.
Independent factor dyads admit this check on their endpoints
up to their vanishing exponent widths. The example above has
these reserves. No sharp joint raw complement indicator is
inserted into the distribution estimate below. We make no
assertion for an arbitrary box intersected with a nonrectangular
raw boundary, or for the rest of the common-\(V\) identity.

## Proof

Use the real \(y\)-mesh and smoothing of
[GiantReciprocalSeam.md](GiantReciprocalSeam.md) to freeze the
\(m\)-interval from \(y/m\in I\) and the \(d<y/B\) cutoff.
The changed actual rows are counted by \(d\mid y,\ |y-Bd|
\ll NL^{-F}\), or \(m\mid y,\ |y-E m|\ll NL^{-F}\) for
one endpoint \(E\) of \(I\). Their union over all cells is
\(O(NL^{1-F}+S+\sqrt N)\) integers;
the absolute coefficient is bounded by fixed divisor powers on
\(x,N-x\). Thus Cauchy gives arbitrary-log accuracy before any
congruence theorem is used, and smoothing on thinner real strips
also has this accuracy. In a cell the score is the fixed
\(Q_T(m)\), with an independent \(m\)-interval, and the central
test is a smooth \(\Psi(y/N)\) of log-bounded derivatives.

Open only the **left** free \(g\)-roughness by a true sieve label
\(e\mid g\) on primes at most \(z\) outside \(N\).
The discarded positive tail is counted on the actual divisibility
\(e\mid x\) at the first omitted order, as in
[MaynardShoulder.md](MaynardShoulder.md), with arbitrary log
accuracy. The retained \(e\)'s are \(V^{o(1)}\). The actual
modulus is \(a(f e)\); since \(f\) is \(z\)-rough, \(f e\)
uniquely recovers \(f\) and \(e\). Thus **no** subpower
multiplier is paid in the number of modulus choices beyond
the two-coordinate distribution estimate. Their independent
coefficients cost at most \(L\). Either true factor \(a\)
or \(f e\) can supply the first modulus coordinate; use the
one at exponent \(v_1+o(1)\).

For the source, group the selected subset of \(\{m,c,h,k\}\)
into one integer and its complement into the other. The coefficients
are the literal divisor sums of their real factor weights.
After division by a fixed power of \(L\) both are bounded by
fixed divisor powers, since there are at most four factor slots.
At least one individual coefficient in the selected group has
the needed Siegel--Walfisz property in its true polynomial dyad:
for \(m\) it is the short-divisor coefficient \(Q_T(m)\) with
its actual target-unit mask, as verified in
[MaynardShoulder.md](MaynardShoulder.md), §2;
for \(h\) it is genuine \(\Lambda(h)\) on the independently
restricted rough, target-unit interval, as verified for the
identical \(f\)-coefficient in
[ReverseMaynardShoulder.md](ReverseMaynardShoulder.md), §1.
In both cases the condition includes the exact auxiliary
coprimality factor \(\tau(d_0)^{O(1)}\) for arbitrary \(d_0\).
For \(h\) this is ordinary prime Siegel--Walfisz after directly
bounding the proper powers and primes dividing \(Nd_0\);
for \(m\) the progression and reduced mean have identical
integer CRT mains for each actual short divisor.

At fixed remaining factors of that group let their product be
\(n_0\). If \(n_0\) is not a unit at the auxiliary mask or progression
modulus, both the reduced progression and reduced-mean terms
vanish. Otherwise the residue for the selected primitive factor
is multiplied by the inverse of \(n_0\). The actual grouped
dyad only adds a real interval to that factor. Its SW estimate,
summed over the independent fixed factors in their divisor-bounded
absolute masses, proves the same SW condition for the entire
group: the factor lengths multiply to its polynomial scale
and all losses are fixed powers of \(L\).
In particular the other selected factors, such as the signed
short score on \(m\) in the example with \(h\) as the SW input,
need no extra distribution hypothesis. Their weights are not
averaged independently of the selected group.

Separate \(\Psi(y/N)\) by compact Mellin inversion as in
the forward shoulder. Its log-power cutoff and its arbitrarily
log-small Fourier tail are unchanged. Oscillatory powers separate
over the actual factors, and the selected polynomial primitive
factor has uniform SW after partial summation at these fixed log
frequencies. The product of the two source scales is \(\asymp N\)
on accepted central dyads. Apply
[Maynard, Proposition 5.3](https://arxiv.org/html/2006.08250v1#S5)
with first modulus exponent \(v_1\), second \(v_2+o(1)\),
and SW exponent \(\beta\). Its strict restrictions follow from
(1) with \(\delta=v_1+v_2-1/2+o(1)\) and a small fixed
analytic epsilon. For fixed \(q_1\) choose the common residue
\(N\bmod q_1\), and for every \(q_2\) choose the literal
\(N\bmod q_1q_2\) above it. All are reduced because the
factorized modulus is a target unit; possible shared primes
between \(a\) and \(f\) do not obstruct the actual product.
Unique recovery of \(e\), the divisor norm, and the fixed
log weights make the total discrepancy \(O_A(NL^{-A})\).

The remaining model is the **actual** principal, with its
\(1/\varphi(a f e)\).
At fixed \(y,f,e\), its \(a\)-sum is the same signed rough
unit harmonic in \(\mu(a)/\varphi(a f e)\) as in the
forward shoulder. All remaining \(a\)-restrictions are fixed
intervals and \((a,Ny)=1\), and \(f\) is a true prime power
where its weight is nonzero. The prime-power overlap
factor is unchanged. The first and last constraints in (1)
give \(v_1<1/2-\delta\) with fixed reserve and hence
\(v_2>2\delta\); in particular the actual \(a\)-interval
has a fixed polynomial scale even with the common small
Vaughan cutoff. Thus its rough \(\mu/\varphi\) harmonic has
arbitrary-log saving by the same exact local-Euler/Mertens
argument. Sum the \(f,e\) weights reciprocally and all
physical \(y\)-factorizations by their ordinary divisor mass,
paying only log powers. This removes the principal and
proves the stated signed deletion.

The genuinely coupled boxes with neither available
factored-modulus rail nor an admissible source group remain.
Nothing here estimates the whole common-cutoff remainder
or proves a binary prime pair.
