# A signed price for a true medium semiprime against the two-tag arm

Keep exactly the fixed even \(N\), central interval \(J\),
\(L=\log N\), \(M=|J|N\mathfrak S(N)\), and compensated
score \(S=G_b+W,\ b=.003\), of
[the three-by-three comparison](ThreeByThreeTagCredit.md).
All rows use \(x+y=N,\ x\in NJ,\ (x,N)=1\).

Let \(\mathcal A\) be the following **whole** physical chamber:

* The left coordinate \(x=pq\) is a genuine product of two
  distinct primes, with smaller prime angle
  \(\beta=\log p/L\in(.080,.1251]\).
* The right coordinate is squarefree, with exactly two
  prime factors at most \(N^{.080}\). Their actual ordered
  target-log angles \(u,v\) exceed .006 and have \(u+v>.065\).
  Every other prime factor is \(>N^{.080}\), without a rank
  restriction.

Let \(\mathcal A^{\rm op}\) be the reflection. Put
\(C_{\mathcal A}=\sum_{\mathcal A\cup\mathcal A^{\rm op}}S(x)S(y)\).

**Proposition.** The entire actual chamber is strictly adverse:
\[
                    -.385M+o(M)<C_{\mathcal A}<-.090M+o(M).
                                                                    \tag{1}
\]
It is disjoint from all previously removed chambers. The existing
\(1.3068M\) comparison, using the unchanged-score
[.003 tiny improvement](ImprovedTinyCovariance.md), therefore
gives the separate comparison
\[
               R_J\ge .9218M+\mathcal R_{\rm out,smaller}+o(M),
\]
where the exact exterior now also omits
\(\mathcal A\cup\mathcal A^{\rm op}\).
This is **not** a better coefficient for the old exterior. Neither
its new remaining sign nor a fraction of a Goldbach proof follows.

## 1. Literal profile and source

Both coordinates pass the .003 gate and have \(Q=W=0\).
Indeed neither is \(N^{.1251}\)-rough, the two right least angles
sum to \(>.065\), and the two left angles sum to \(1+O_J(1/L)\).
Thus \(S=H\). The counts of actual factors at most \(N^{.080}\)
are \((0,2)\), or \((2,0)\) for reflection; these rule out the
one-by-two, two-by-three and three-by-three chambers.
The \(.1251\)-rough chambers all need at least one such rough
arm, and the full two-tag chamber needs two small named primes
on each arm, impossible on a left semiprime whose larger
prime has angle at least \(.8749+O_J(1/L)\). This also proves
the two new orientations disjoint.

The actual rank-two score divided by \(L\) is
\(w(\beta)+O_J(1/L)\), where \(w(\beta)=1-F(\beta)\ge0\).
For definite notation in the right quotient write
\(h=p_1p_2\) for its two actual least primes and \(y=h m\).
There is no prime atom on either side. For a divisor \(d\mid m\)
put \(s=\log d/L\). After the own-log replacement the exact
right profile divided by \(Luv\) is
\[
 B(m;u,v)=\sum_{d\mid m}\mu(d)\,g_{u,v}(s),\qquad
 g_{u,v}(s)=\frac{F(s)-F(s+u)-F(s+v)+F(s+u+v)}{uv}.             \tag{2}
\]
We use the **sharp** original \(F\) in every term, with
\(g_{u,v}(s)=0\) for \(s\ge1/2\). On fixed-floor ranks
all log replacements are \(O_J(1/L)\) per term. The genuine
two-form upper in §3, also with \(d=1\), bounds the total
amplitude normalization, so the resulting error is \(o(M)\).
All membership cutoffs still use the target-log angles.
Nonsquarefree coordinates would have scored zero.

The true compact product source \(Z(x)\) consists precisely
of these \(p q\), weighted by \(w(\beta)\), with the original
target-unit condition. Its ordinary unopposed count is
\((m_Z+o(1))|J|N/L\), where
\[
       m_Z=\int_{.080}^{.1251}\frac{w(\beta)}{\beta(1-\beta)}\,d\beta .
                                                                    \tag{3}
\]
This is the actual prime reciprocal harmonic for the smaller
prime followed by the true prime count in the other slot.
The \(o(1)\) is unaffected by actual target prime exclusions at
these fixed power floors. The same source with the last prime
count supplied by a genuine two-form sieve, rather than PNT,
will use
\(m_0=\int_{.080}^{.1251}w(\beta)d\beta/\beta\).

## 2. Both signs in the ordinary subroot transfer

Use .001 cells for each of \(u,v\) and \(10^{-4}\) cells
for the \(d>1\) exponent \(s\). Fix one such tag cell and
put \(t_+=u_++v_+\), its upper tag sum. Always retain the
actual order \(p_1<p_2\) and actual sum \(u+v>.065\).
The \(d=1\) atom is treated separately.

For \(d>1\) with cell upper endpoint \(s_+\), put
\(D=.499-t_+-s_+\). Use the present transfer if \(D\ge.045\);
the \(d=1\) atom uses \(D=.499-t_+\). Open the **actual**
\(hd\) into the receiver factor \(y=hdr\), and linear-sieve
\(r\) at level \(N^D\). The genuine tested modulus is \(hde\),
\(e\le N^D\), so \(hde\le N^.499\). Use true product BV of
the actual weighted \(p q\) source, as in
[the one-by-two theorem, §2](OneByTwoTagCredit.md).
Angular and spatial endpoint separation is by real boxes and
fixed bounded weights, including separately the positive and
negative parts of \(g_{u,v}\). The total variation of the
fixed profile and the bounded ranks allow this approximation;
equal-cell ordered tag choices retain bounded divisor
multiplicity of the actual modulus. No distribution result
for a fixed pair of tag primes is assumed.

The source residue is the real reduced \(N\bmod hde\).
In the model \(1/\varphi(hd)\) is the outer weight and the
linear density at tested primes off \(Nxhd\) is \(1/(p-1)\).
Local omissions at \(\ell\mid xhd\), away from target
factors, cost \(1+o(1)\) on all these fixed positive power
floors with bounded ranks. In particular a shared source
prime would make the residue nonunit; it is absent from the
physical rows, and restores at most \(o(1)\) of the bounded
prime reciprocal harmonics in the model. The target factor
therefore is exactly \(\mathfrak S(N)\) to relative \(o(1)\).
All right-side small-prime squares from an omitted named
prime, or from any repeated quotient factor, can be removed
at \(O(N^{1-.006+o(1)})\) by their actual multiples and the
fixed divisor envelope. The right side is indeed squarefree
and \(N^{.080}\)-rough after its two tags.

Write \(a=.080\), and let \(U(D),k(D)\) be the upper and
lower coefficients used for this layer. For \(D\ge4a\), use
level \(4a\) and the verified \(.575/a,.549/a\).
For \(2a<D<4a\), use the standard lower
\(2\log(D/a-1)/D\), rounded below by its positive atanh
truncation. For \(D\le2a\), use lower zero.
For \(a\le D\le3a\), upper \(2/D\) is the exact linear
upper coefficient; if \(D<a\), upper-sift at \(N^D\)
instead of \(N^a\), still giving \(2/D\), and only enlarging
the true positive count. For \(3a<D<4a\) use
\[
                       U(D)=\frac2D\left(1+\frac{(D/a-3)^2}{4}\right);
\]
the upper follows from \(\log(1+z)/(2+z)\le z/2\)
on the standard integral branch. All constants are fixed for
the actual full cells, not optimized row by row.

Let \(e_a(s),o_a(s)\) be the unopposed reciprocal-harmonic
densities for an **even** or **odd** number of distinct
primes in a squarefree \(d>1\), all above \(N^a\).
In terms of the real one-arm densities \(b_\pm\) from the
one-by-two proof, they are
\[
                     e_a=(b_++b_-)/2,\qquad o_a=(b_+-b_-)/2.
\]
These follow from the true prime harmonics for \(d\)'s fixed
rank slots; in the model \(\varphi(d)\) may replace \(d\)
with relative \(1+o(1)\). The first atom is \(d=1\), with
unique weight 1. After multiplying the physical measure by
the right tags \(uv\), their reciprocal harmonics become
\(du\,dv\). The both-sided transfer therefore gives, per
unit \(m_Z M\,du\,dv\,ds\), the following lower and upper
for the contribution of a non-atomic layer of (2):
\[
 \begin{split}
 -\{(Uo_a-ke_a)\,g_+ +(Ue_a-ko_a)\,g_-\}
  &\ \le\ \text{layer}\ \le\
       (Ue_a-ko_a)\,g_+ +(Uo_a-ke_a)\,g_-,\\
            g_+=[g_{u,v}]_+,\quad g_-=[-g_{u,v}]_+ .
 \end{split}                                                     \tag{4}
\]
Here \(U=U(D)\), \(k=k(D)\). Both bounds keep the actual
positive and negative weighted sums; the differences in
(4) are not cancellation assumed in an unknown coupled
distribution. For the atom \(g_{u,v}(0)<0\), use
\([U(D)g_{u,v}(0),\,k(D)g_{u,v}(0)]\).
The sign of this atom is also uniformly checked in §4.

## 3. The beyond-transfer tail is an actual prime-opposite upper

For the remaining exponent bins fix genuine \(p,h,d\) with
\((p,hd)=1\) and \((phd,N)=1\), as required by the physical
units. The prime \(q\) and the rough \(r\) satisfy the
literal primitive affine equation
\[
                               pq+hdr=N.
\]
They vary over one actual lattice parameter of length
\(|J|N/(phd)+O(1)\). The two forbidden roots coincide
at primes dividing \(N\); at a prime dividing \(p hd\)
one affine slope is zero and its corresponding constant is
a unit, so exactly one root remains. At all other primes
there are two distinct roots. This includes the one-root
case at 2. Dropping further target-unit restrictions only
enlarges the positive upper.

Use an ordinary Selberg square for these forms with prime
cut \(N^a\) and the fixed cell support
\[
  N^{D_2},\qquad
  D_2=.499(1-.1251-t_+-s_+).
\]
Both forms pass the sieve: \(q\) is genuinely prime
and longer than this prime cut, and \(r\) really is rough.
The available exponent is at least \(1-.1251-.160-.500=.2149\).
The \(O(N^{2D_2}L^{10})\) true Selberg floor is power-small
relative to the fiber length, uniformly in the chosen
labels. The floors sum with the actual harmonic \(1/(phd)\)
and fixed logarithmic losses.

By the [same dimension-two denominator](RoughPositiveCredit.md#1-the-genuine-pair-ambient),
the true upper for each fiber is, with relative \(o(1)\),
\[
    \frac{|J|N\mathfrak S(N)}{phd L^2}\,C_2,\qquad
    C_2=\left(a^2\int_0^{D_2/a}\rho_2(z)\,dz\right)^{-1}.
                                                                    \tag{5}
\]
The one-root exceptions are the actual primes of \(Nphd\).
The additional ones in \(phd\) are polynomially large
and bounded in number, changing \(\mathfrak S(N)\) and
the normalized Dickman-2 limit by \(1+o(1)\), uniformly.
This is a real two-form upper even when \(hd\) itself
is above the product-BV range.

For the lower discard positive tail summands and upper-bound
negative ones; for the upper do the opposite. Now summing
the **true** smaller-prime harmonic uses \(m_0\), while
the right \(h,d\) use the same actual reciprocal harmonics
as in §2. Per unit \(m_0 M\,du\,dv\,ds\), the extra lower
debit is at most \(C_2(o_a g_++e_a g_-)\), and the upper
addition is at most \(C_2(e_a g_++o_a g_-)\).
The prime \(q\) is paid by (5), not put back as an
independent prime density. The estimates are valid for
every actual quotient rank and both reflections.

## 4. Exact numerical enclosure on the entire triangle

The [checker](check_medium_semiprime_adverse.py) verifies
the same earlier outward arithmetic and one-arm density
code by hash. It encloses \(m_Z,m_0\) in (3) on the
explicit \(10^{-4}\) mesh, uses the same \(10^{-4}\)
predecessor density bins for \(b_\pm\), and bounds the
second finite difference of \(F\) uniformly over each
**whole** interval product. This includes bins that meet
the sharp half endpoint. No smooth approximation or
rescaling of the profile is made in this numerical estimate.

For (5), the lower cumulative \(\rho_2\) grid uses the
same rational recurrence as the positive-ambient checker:
\(f(z)=\rho_2(z)/z\) equals 1 initially and then
\(f'(z)=-2(z-1)f(z-1)/z^2\). Its monotonicity bounds
each derivative step from the predecessor endpoints.
In the denominator truncate \(D_2/a\) downward to the
\(10^{-4}\) grid, then integrate \(z\) against the
outward lower endpoint height of \(f\) in each bin.
All integer recurrences and their sum use a scale of
\(10^{13}\), rounding in the required direction.

Each of the 2073 nonempty ordered \(u,v\) rectangles
uses its **actual clipped area** at \(u+v>.065\).
In equal cells this area is halved for the true order
\(p_1<p_2\); the reciprocal harmonic diagonal is negligible.
Thus the enumerated region is precisely the full triangle
of area .00203575, not only the cells wholly above the
oblique threshold. All additional boundary sets have
zero limiting true harmonic measure. There is no double
count of orientations: the left type has zero .080 tags,
while the right type has exactly two. Reflection uses
\(1-J\), of the same length, in the same two computations.

Run:

    python3 -OB check_medium_semiprime_adverse.py

The verified bilateral lower debit is below
\(.384826374M\), of which less than \(.055901M\) is the
real affine tail. The bilateral upper is below
\(-.0900218M\). This gives (1) on the full specified
physical chamber with no rank or sign selection.
