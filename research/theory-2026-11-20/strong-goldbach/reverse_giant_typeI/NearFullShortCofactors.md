# Both short cofactors in the actual near-full giant remainder

Keep the direct \(\mathcal D_I\), actual central interval \(J\)
and all notation of [SecondTypeI.md](SecondTypeI.md).
Fix \(\varepsilon>0\) and \(C>0\), and assume
\(I\subset[N^{1/2+\varepsilon},B]\) and
\(\operatorname{rad}(N)\le L^C\). There exist fixed
\(\zeta,\eta>0\) such that, uniformly for
\(1\le H_1\le\exp(L^\zeta)\), the restriction of
\(\mathcal D_I\) to
\[
                          mk\le H_1,\qquad j\le H_1              \tag{1}
\]
is \(O_{C,\varepsilon,J_0}(NL^{-\eta})\).
Here \(H_1\) is not the \(H\) in \(Z(X)\).
Both \(a\) and \(b\) in this chart are at least
\(N^{1-o(1)}\), so the chart is distinct from the
[sub-root](ConductorHalf.md) and
[balanced over-root](OverRootAngles.md) cuts.
This is a signed deletion with a fixed log saving only,
under the stated small-radical hypothesis. It does
not cover all actual near-full giants, the singly
short-cofactor branch, or a polynomial cofactor cutoff.

The analytic input is the projected packet comparison
and first-active construction of
[the subpower double-Möbius aggregate](../small_radical_reflected_chowla/SubpowerAggregate.md).
Its displayed theorem alone, with 1-bounded cofactor
weights and a single central interval, is not enough.
We use the same comparison with the actual higher
divisor weights and finitely many disjoint moving-score
cells below. No other parity statement is imported.

## 1. Freezing the actual two moving cuts

Put \(w=mk\), \(y=aw\), \(p=N-y=bj\), and
\(W=1+\log H_1\). On the compact central support,
(1) implies \(a\gg N/H_1\), \(b\gg N/H_1\).
In particular \(am>Q\) and
\(b>Z(N/w)\le\sqrt N\) are automatic for large \(N\).
Keep the literal target-unit mask \((y,N)=1\), so
all divisor variables, including \(j\), are target
units. The effective additional conditions on \(m,d\)
are exactly
\[
        y/m\in I,\qquad d\mid m,\ d<y/B.
\]
Choose a fixed relative log mesh of width \(O(L^{-F})\)
in the compact positive \(y\)-interval, and denote its
disjoint cells by \(J_i\), their actual lengths by
\(|J_i|\), and a chosen point in each by \(y_i\).
The number of cells is \(O(L^F+1)\). Write \(D=L^F\)
in the mesh estimates only. For each cell put
\[
 c_i(w)=\sum_{\substack{mk=w\\y_i/m\in I}}
                       \log k\,Q_{y_i}(m).
\]
It satisfies the uniform majorant
\[
                 |c_i(w)|\le\tau_3(w)\log w,                    \tag{2}
\]
because \(\sum_{mk=w}\tau(m)=\tau_3(w)\).
The intended phase-freezing replaces the coefficient
of \(\mu(a)\) on \(y\in J_i\) by \(c_i(w)\).
We bound this change on actual integers before using
any signed projection estimate.

For integers \(r\ge1,h\ge1\) write
\[
 D_h(t)=\sum_{\substack{u\mid t\\u\le H_1}}
                  \tau_h(u)\log u .
\]
For fixed \(r,h\), opening the \(r\) divisors and
using at most \(X/[u_1,\ldots,u_r]\) multiples gives
\[
 \sum_{t\le X}D_h(t)^r
       \ll_{r,h} X W^{\,r+(h+1)^r-1}.                            \tag{3}
\]
Indeed after majorizing the log factors by \(W^r\)
and allowing all smooth divisor tuples, the Euler
factor at \(q\le H_1\) has its coefficient of \(1/q\)
equal to \((1+\tau_h(q))^r-1=(h+1)^r-1\).
Terms with maximum exponent at least two are
\(O_{r,h}(q^{-2})\) by polynomial prime-power
divisor bounds. Mertens' product proves (3).
In particular the second and fourth exponents
are \(17,259\) for \(h=3\) and \(5,19\) for \(h=1\).

Let \(E(y)\) denote the absolute positive expansion
of the coefficient error at \(y\in J_i\): for
the \(d\)-cut variation count marked \(d\mid m\)
with \(d\) between the cell extrema of \(y/B\);
for variation of \(y/m\in I\) count \(m\) between
one of the moving endpoint extrema, with weight
\(\tau(m)\). In each case retain \(mk\mid y,\ mk\le H_1\)
and \(\log k\). The \(d\)-cut error need only use
rows for which at least one of the real or frozen
\(m\)-cuts holds, but an upper bound can omit that
condition. Pointwise \(E(y)\le 2D_3(y)\).

For a fixed \(J_i\) the genuine number of \(y\)'s
with \(mk\mid y\) is at most \(|J_i|/(mk)+1\).
At the \(d\)-cut the possible \(d\) lie in an
interval of relative length \(O(D^{-1})\) around
\(S\), so their reciprocal mass is
\(O(D^{-1}+S^{-1})\). Write \(m=du\), and the
remaining harmonic sum in \(u,k\) with \(\log k\)
costs \(O(W^3)\). At each \(m\)-cut the ambiguous
\(m\)'s lie in an interval at scale \(M\gg S\) with
relative length \(O(D^{-1})\); indeed the upper
giant endpoint is at most \(B\). If the interval
is partly outside \(m\le H_1\) keep only the
intersecting part. Cauchy and the ordinary second
divisor moment give
\[
         \sum_{m\ {\rm ambiguous}} \tau(m)/m
                   \ll W^{3/2}(D^{-1}+S^{-1})^{1/2}.
\]
The remaining \(\log k/k\) costs \(O(W^2)\).
The sum of all genuine \(+1\) floors over all cells,
\(m,k\) and divisors in the expansion is
\(N^{o(1)}\), by \(mk\le H_1\) and ordinary
summatory divisor bounds. Thus
\[
                \sum_y E(y)\ll NW^{7/2}D^{-1/2}+N^{o(1)},       \tag{4}
\]
using \(S\) larger than every fixed power of \(L\).
The opposite actual absolute coefficient is
\(D_1(N-y)\). From (3) and Cauchy on the actual
reflected integer pair one has
\(\sum_y D_3(y)D_1(N-y)^2\ll N W^{18}\).
By (4) and \(E\le 2D_3\),
\[
              \sum_y E(y)D_1(N-y)
                   \ll NW^{11}D^{-1/4}+N^{1/2+o(1)}.          \tag{5}
\]
Increasing \(F\) makes this as small as needed in
fixed powers of \(L\). Strictness at \(d=y/B\) or
at either endpoint of \(I\) is paid by the same
real strips and single floors.

After freezing, define on cell \(i\) the coefficients
\[
 C_i(t)=\sum_{\substack{w\mid t\\w\le H_1}} c_i(w)\mu(t/w),
 \qquad
 B_1(t)=\sum_{\substack{j\mid t\\j\le H_1}}\log j\,\mu(t/j).
\]
The remaining sum is exactly
\(\sum_i\sum_{y\in J_i,(y,N)=1}C_i(y)B_1(N-y)\).
We have true envelopes \(|C_i|\le D_3\), \(|B_1|\le D_1\).
The \(c_i\) are fixed separately before any analytic
operation on that cell; they are not recomputed at
a subsequently divided argument.

## 2. Changes to the subpower comparison

Use the conventions and fixed comparison parameters
of [SubpowerAggregate.md](../small_radical_reflected_chowla/SubpowerAggregate.md),
including the derivative on the \(C_i\) side, the
first-active banks on the \(B_1\) side, and the
small-radical target projector. The following
checks justify the weighted change.

**Derivative and missed banks, before the mesh summation.**
On the physical row \(w\mid y,\ y\in J_i\),
\(\log(y/w)=L+O(W)\). Expand the exact identity
\[
    \mu(a)\log a
           =-\sum_{\pi^e\mid a}\log\pi\,\mu(a/\pi^e)
\]
at \(a=y/w\). As in the subpower comparison let
\(\epsilon_1=L^{-1/100}\). Discard powers \(e\ge2\)
and prime labels outside
\([N^{\epsilon_1},N^{1-\epsilon_1}]\).
The omitted unsigned log mass normalized by \(\log a\),
summed over all actual \(y\) and \(w\le H_1\)
with \(\tau_3(w)\log w\) weights, is at most
\(O(N(\epsilon_1+L^{-1})W^4)\).
This follows by counting genuine multiples of
\(w\pi^e\) and using
\(\sum_{w\le H_1}\tau_3(w)\log w/w\ll W^4\).
The positive error is pointwise bounded by \(D_3(y)\);
pairing with \(D_1(N-y)\) via the same moment as
in (5) costs \(O(N\sqrt{\epsilon_1}W^{11})\).
Replacing \(1/\log a\) by \(1/L\) costs \(O(NW^{12}/L)\)
using the two second moments in (3).
The exact remaining source coefficient on cell \(i\)
is
\[
       -\sum_{\substack{\pi q=y\\
            N^{\epsilon_1}\le\pi\le N^{1-\epsilon_1}\\
            \pi\ {\rm prime}}} \frac{\log\pi}{L} C_i(q).
\]
It has the same positive envelope \(D_3(y)\):
the sum of the distinct \(\log\pi\)'s is at most
\(\log y\le L\), and \(D_3(q)\le D_3(y)\).

The first-active missed-row count
\(O(N L^{-\kappa_K})\) for a fixed \(\kappa_K>0\)
is the same actual CRT count as in the input; apply
it over the entire compact central interval.
The actual product of the retained source and
opposite envelopes has squared sum
\(O(N W^{139})\), by pairing the fourth moments
\(259,19\) in (3). Thus the total weighted miss is
\(O(N L^{-\kappa_K/2}W^{139/2})\). These losses,
as well as the derivative losses, are taken once
over the disjoint \(J_i\), not multiplied by the
number of moving-score cells.

**Literal tagged residual.** The short-cofactor
test on the opposite leg is unchanged. Every
bank prime is larger than \(H_1\), for
sufficiently small \(\zeta\), so on a squarefree
tag extraction \(N-y=u h\) one has exactly
\(B_1(uh)=(-1)^K B_1(h)\), with the other bank
flags and reciprocal hit counts functions of
\(h\) alone. This is precisely the same
literal first-active transform as in §2 of the
subpower input. Tag-prime square errors still
have arbitrary log saving: the pointwise
new source envelope is
\(\sum_{w\le H_1}\tau_3(w)\log w\ll H_1 W^3\),
instead of \(H_1W\), whereas the old exponential
square error is \(\exp(-c L^{.1})\).
No condition on the prime factors of the
actual \(m\) and \(k\) is inserted.

**Projected minor and full projected Parseval.**
In §3 of the subpower input the only square norm
that changes is the \(C_H\) slot, now bounded
at scale \(U\) by \(O(U W^{17})\) instead of
\(O(UW^5)\), by (3). Its supported fibre
changes accordingly to \(O((U/\Pi)W^{17})\)
on a fixed product \(\Pi\) of labels.
The maximum norm changes from \(O(H_1 W)\)
to \(O(H_1 W^3)\), still admissible with the
\(2/T\) power for \(T\asymp \sqrt L\) and in all
bad parts with the old \(\exp(-cL^{.1})\) gain.
For arbitrary separated phases in a fixed box,
the product coefficient of the literal prime
\(\pi\) and \(q\)-slot has square norm
\[
          \ll N L^{.01} W^{17}
\]
by exactly the same distinct-prime multiplicity
\(\ll L^{.01}\), followed by (3) at the actual
\(q\)-scale. This is also the upper bound before
separation for the absolute source. It suffices
both for projected Parseval and for Fourier
tail removal at the literal modulus \(N d_1\).
The opposite residual square norm at tag scale
\(Y\) is unchanged, \(O((N/Y)W^5)\).

**Exceptional-character long slot.**
Open \(q=w v\) in the actual \(C_i(q)\), keeping
its fixed interval and its cofactor weights.
Exactly as in §3 of the input, a retained progression
with modulus \(d_0\) reduces after extracting
\((w,d_0)\); it does not add a factor \(w\) to any
character conductor. The remaining \(\mu(v)\)
has length at least \(\exp(cL^{.99})\) because
\(q\gg N^{\epsilon_1}\) and \(w\le H_1\).
Real and character twists separate with the extracted
\(w\), and all actual unit exclusions remain bank,
target and polylogarithmic factors. The old reciprocal
and Perron saving still applies uniformly in \(w\).
Summing it costs only
\(\sum_{w\le H_1}|c_i(w)|/w\ll W^4\).
The prime-slot Bessel bound is unchanged.

Thus all errors from fixed packets, their rational
and real separation, and the tag shells can have
arbitrary fixed log saving, exactly as in the
subpower comparison but with the stated moment
changes. There are only fixed powers of \(L\) boxes,
including the \(O(L^F)\) cells \(J_i\).
For the edges of \(\pi q\in J_i\) in the packet
mesh, the union of all \(O(L^F)\) endpoint strips
has total length \(O(NL^{F-F'}+L^F)\) under a
finer product mesh \(L^{-F'}\). Apply Cauchy
and the preceding full fourth-moment bound;
\(F'\) sufficiently larger than \(F\) pays
this positive loss. No asymptotic in a physical
short interval and no multiplication of the
leading missed-bank error by \(L^F\) are used.

Finally choose \(F,F'\) and comparison precisions
first. Uniformly for an initial bound
\(\zeta\le 1/10000\) the changed moments cost
only fixed log powers, so the chosen bank
multiplicity and the resulting \(\kappa_K>0\)
are fixed independently of the final \(\zeta\).
Then take \(\zeta\) small enough that both
\(L^{-.005}W^{11}\) and
\(L^{-\kappa_K/2}W^{139/2}\) save a fixed log
power, for example also require
\(\zeta\le\kappa_K/400\).
All other stated errors are smaller with the
fixed spare reserves. This proves the claim for
(1) with some fixed \(\eta>0\).
