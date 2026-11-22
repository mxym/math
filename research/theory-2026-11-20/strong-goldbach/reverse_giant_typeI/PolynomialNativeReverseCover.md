# An additive reverse cover on the polynomial-quotient native score

Use [the polynomial native identity](PolynomialNative.md)
at the actual fixed even target, fixed-gap interval \(I\),
and its positive polynomial cutoffs. Suppose
\(\operatorname{rad}(N)\le L^{B_0}\) with \(B_0\) fixed.
Fix \(0<\xi<\gamma\), where \(\gamma=1/2-\epsilon\) in the
calibration, and retain the actual cutoff \(m\ge N^\xi\)
only in the reverse cover.

Choose two disjoint collections of admissible banks,
each with \(\asymp_K\log L\) families of fixed \(K\ge2\)
separated colors, inside the range in
[the forward covered theorem](PolynomialNativeCovered.md).
They can be chosen together by partitioning the original
separated construction, still using at most \(\lfloor\log L\rfloor\)
families altogether. Use \(\mathcal E_+(A,C)\) from that theorem
on the first collection. On the second, for each family \(j\)
put \(V_j(mC)=1\) if \(mC\) avoids its whole bank and \(U_j(A)=1\)
if \(A\) is hit in every color. Put
\[
        \mathcal E_-(mC,A)=1-\prod_j(1-V_j(mC)U_j(A)).
\]
For every requested fixed \(D>0\), with sufficiently large
fixed \(K\), the portion of the literal polynomial native
sum with multiplier
\[
        1_{m\ge N^\xi}(1-\mathcal E_+(A,C))\mathcal E_-(mC,A)
                                                                    \tag{1}
\]
is \(O_D(NL^{-D})\), with the fixed cutoff data and \(B_0,\xi,J_0\)
as additional dependencies. This is signed cancellation on a
set **disjoint** from the already canceled forward part. In
particular it applies to the actual prime \(C>U_r\) rows if
\(m\) avoids a suitable reverse bank and \(A\) hits all its
colors. If both \(A,C\) are primes neither direction supplies
the required tags; also no reverse assertion is made for
subpolynomial \(m\). There is no conclusion about these
remaining signed rows or about a binary prime pair.

## 1. The long signed coefficient is the actual \(Q_T(m)\)

Use the same globally paid real \(y\)-mesh as in
[PolynomialNativeCovered.md, §2](PolynomialNativeCovered.md).
The \(m\)-interval and \(T_y\) cutoff are frozen in each cell,
with \(T\asymp_{J_0} S\). Group the source as
\[
         y=D_0 h,\qquad D_0=m C,
\]
with \(h\) the genuine prime. Besides the true \(C\)-weight
\(H_{U_r}(C)\), retain all actual masks on \(C\).
For the long signed slot fix this factor \(C\) and use
\(Q_T(m)\) on polynomial scale \(D_{0,\mathrm{scale}}/C\),
within the interval \(m\ge N^\xi\) and the frozen
\(m\)-gate. Target units in \(m\) are retained
and \(m\) avoids the specified reverse banks. No roughness
or assumption of coprimality with the arc denominator is
made on \(m\). All other transferred forward-family masks
on the source concern \(C\) only and are fixed here.

To verify its uniform character bound, split the small
rational arc denominator \(b=d_0d_1\) as in
[the one-prime comparison, §1](../small_radical_reflected_chowla/Proof.md),
where \(d_1\) is supported on primes of \(N\) and
\((d_0,N)=1\). The additive part uses actual residues
of \(D_0\bmod d_0\). Since \(C\) is \(z\)-rough and
\(d_0\) is polylogarithmic, reduce the residue to
\(m\equiv a_0\bmod d_0\) by inverting \(C\). Set
\(e=(a_0,d_0)\), with \(e=d_0\) at residue zero, and
write \(m=e m'\). The new reduced class is
\(m'\equiv a_0/e\bmod d_0/e\), allowing modulus one.
All characters from this class and the target-ring
factors are now on moduli dividing \(N d_1(d_0/e)\),
with the fixed additional polylogarithmic arc twists
allowed by the comparison. The multiplier \(\chi(e C)\)
in a target-ring character is fixed, and target units are
unchanged since \(e\) is a target unit. Both unit and
nonunit original residues are thus treated literally.

Squarefree support of \(\mu\) gives the exact reduction
\[
 Q_T(e m')=
 \sum_{s\mid\operatorname{rad}(e)}\mu(s)
       \sum_{\substack{d\mid m',\ (d,e)=1\\d<T/s}}\mu(d).             \tag{2}
\]
This does not require \((m',e)=1\): a squarefree divisor
of \(e m'\) has a unique portion \(s\) supported on primes
of \(e\), and its other portion divides \(m'\).
In particular the equality keeps the actual strict
threshold even when \(T/s\) is integral. The bank
avoidance on \(m'\) is unchanged since the bank primes
exceed all of \(e\). They also exceed \(T\), so the
short divisor \(d\) in (2) automatically avoids them.

For each fixed \(s\), open \(d<T/s\) and the actual
bank avoidance of the free integer \(m'/d\) by the
same factorial Bonferroni as in the forward proof.
The short \(d\)-count is \(O(S)\), the opened bank
labels and their number are \(\exp(O(L^{.3}))\),
and the initial \(m'\)-scale is \(\ge N^\xi/L^{O(1)}\).
Counting the positive omitted degree and floors is
therefore harmless even with maximal real prefixes.
For nonprincipal inducing characters, the free scale
is still \(\ge N^{\xi/2}\) and Iwaniec's Lemma 6 with
the short-conductor full-period case applies exactly
as in that proof. Include the fixed reduced class
in the character twist and retain all actual unit
and avoidance factors. For the principal the density
is independent of the short \(d\) apart from \(1/d\);
the signed model factor is precisely
\[
       \sum_{\substack{d<T/s\\(d,H)=1}}\mu(d)/d
               =O_E(L^{-E}),\qquad H\le L^{O(1)} .
\]
Here one may take the radical of \(H\) to contain
all the arc, target and \(e\)-primes involved:
\(\operatorname{rad}(N)\le L^{B_0}\). The bank
has not entered this mask on \(d\). Since
\(T/s\gg S/L^{O(1)}\), the masked Mertens harmonic
of [PolynomialNative.md, (3)](PolynomialNative.md)
and its proof apply uniformly, for the strict real
endpoint as well. The additional \(s\)-sum costs
only fixed log powers. Thus at fixed \(C\) this
actual \(m\)-slot has arbitrary-log character
cancellation on its dyad and in all relevant
prefixes. One sums \(C\) with the absolute reciprocal
weights \(|H_{U_r}(C)|/C\le\tau(C)/C\), not with
its cardinality. The genuine source coefficient
on \(D_0\) has the requisite arbitrary-log
character bound, also with fixed log-frequency
twists by partial summation. Its divisor clipping
is valid by ordinary moments on \(D_0\), and actual
\(D_0\mid y\) for the physical error.

## 2. The signed reverse extraction

Expand the forward failure in (1) and the
earlier reverse failures before the first successful
reverse family. This produces at most \(2^{O(\log L)}\)
separable terms with a log exponent fixed independently
of \(K\). The factors \(C_j(C)\) from the forward banks
are still fixed at each \(C\) in §1. A reverse avoidance
of \(mC\) splits literally into separate avoidance
of \(m\) and \(C\). All forward masks on the tag side
\(A\) are in disjoint banks from the chosen reverse
family. Thus successful reverse extraction does not
change the earlier hit or avoids on that side.
No row covered by the forward theorem is charged again.

Extract a real tag \(w\mid A\), one actual prime in
each selected color, with the same reciprocal
hit allocation. Remove bank-square incidences
\(p^2\mid x\) by actual multiples and divisor
moments. Write \(A=w A'\). Applying the exact
identity and smoothing of
[PolynomialNativeCovered.md, §2](PolynomialNativeCovered.md)
to \(H_{U_x}(w A')\) moves only true divisors
\(ds\mid A\mid x\) close to fixed \(U_x\).
It has the same one-dimensional Mellin budget,
with bounded phases on a selected subset of entering
labels. Restore the removed bank-square rows
after opening: on every artificially restored row
\(w\mid A\mid x\) still holds and \(p^2\mid x\) for
some bank prime. The absolute opened assignments
are bounded by fixed divisor powers on actual \(x,y\),
so the same multiple count pays this restoration
without retaining either a square exclusion or
\((w,A')=1\) in the separated residual. All forward
and earlier reverse masks on \(A'\) remain exact since
their primes do not divide \(w\). The equation in this
orientation is
\[
           D_0 h+w n=N,\qquad n=A' f.
\]
Its residual is one divisor-bounded coefficient
with square norm \(O((N/Y)L^{O(1)})\)
on \(w\asymp Y\), including the real prime \(f\)
and the actual \(H_{U_x}\) divisors after the
Mellin opening. The factor \(h\) is an actual
prime of polynomial size and both initial factors
\(D_0,h\) avoid the complete chosen bank.
As before these facts give the primitive physical
endpoints, even though \(m\) is not assumed rough.
The major uses the exact \(D_0\)-slot from §1
and restricted Bessel on the prime \(h\).
The residual Cauchy norm and minor are the same
as in the forward covered theorem. The real
mesh, Mellin, packet and tag shell costs are fixed
log powers before choosing \(K\); subset
choices only cost constants. The final signed
estimate is \(O_D(NL^{-D})\) on (1), as asserted.
