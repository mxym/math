# Two actual small tags against three, with every quotient rank

Use exactly the same \(N,J,L,M,S=G_b+W\) and the same
\(b=.003\) as in [the one-by-two theorem](OneByTwoTagCredit.md).
Here both sides have true quotient roughness \(P^->N^{.080}\).
The left side has **exactly two** actual primes at most \(N^{.080}\);
the right side has **exactly three**. All named prime tags have
target-log angles above .006, and belong to half-open .004 cells
beginning at .006 and wholly contained in \((.006,.080]\).
List the cells on each side in nondecreasing order, allowing ties
of cells, but use the increasing order of the distinct actual primes
inside that list. The sum of the lower endpoints of each arm's
first two cells must exceed .065. The sum of the three upper
endpoints on the right must not exceed .176. Require both
physical coordinates to be squarefree. These conditions define
\(\mathcal B\), with **no further exclusions** on either quotient's
rank or angle. Use its reflection \(\mathcal B^{\rm op}\) as well.

**Proposition.** The entire true signed covariance on these two
orientations is \(>.0395M+o(M)\). Each orientation is disjoint from
the other and from all the chambers removed in the one-by-two
theorem. Thus, after additionally removing only these two exact
chambers,
\[
                    R_J\ge 1.125M+\mathcal R_{\rm out,new}+o(M).
\]
The signed exterior is not bounded below here; no Goldbach
conclusion or solved fraction follows.

## 1. Physical support and arithmetic transfer

Both sides pass the .003 gate, both have \(Q=0\), and \(W=0\)
since both actually have a first-two angle sum \(>.065\).
Therefore \(S=H\) on this whole chamber. The case of a squared
coordinate would have product zero anyway. The exact count of
factors below or at \(N^{.080}\) distinguishes the two orientations
and also excludes both orientations of the previous one-by-two.
Neither coordinate is \(N^{.1251}\)-rough, so
\(\mathcal E_Q,\mathcal C_Q,\mathcal C_Q^{\rm op}\) are absent.
The three-tag arm has a third actual prime \(\le N^{.080}\),
which rules out the true \(N^{.110}\)-rough two-tag quotient in
\(\mathcal F_{\rm all}\). This establishes all disjointness in
the actual rows, regardless of signs.

For each paired cell, use the real measure with the product of
all five actual tag angles as weight. Write \(A=H(x)/(Luv)\)
for the two-tag angles \(u,v\), and
\(B=H(y)/(L\tilde u\tilde v\tilde w)\) for the three-tag angles.
The exact physical product is \(L^2 A B\) times the real measure
weight. As in the preceding theorem, use the signed lower
\[
 d[-k\,m_{\rm L}(A)-(U-k)m_{\rm L}(A_+)]
              -U\sqrt{m_{\rm L}(A^2)m_{\rm R}((B+d)^2)}
                                                                    \tag{1}
\]
in units of the paired cell volume times \(M\), where
\(k=.549/.080\), \(U=.575/.080\).
Here all \(m\)'s are unopposed ordinary one-arm moments.
This follows by actual Cauchy–Schwarz on the common physical
weighted measure, with \(AB=A(B+d)-dA\); the sign of the first
moment uses a genuine upper for \(A_+\) and lower for \(A_-\).
The two actual Cauchy factors use separately the genuine upper
for \(A^2\) and for \((B+d)^2\) on that same measure.

The full arithmetic proof of these marginal transfers is the
one-by-two theorem, §2. In the three-tag application the opened
receiver progression is the **actual** \(hd_0\), with \(h\)
a product of its three distinct true named primes and sieve level
\(d_0\le N^{4(.080)}\). Its exponent is at most
\(.176+4(.080)=.496<.499\); for the two-tag arm it is at most
\(.160+.320=.480\). Product BV for the source uses its actual
finite angle and rank boxes and its literal reduced residue \(N\).
The tag primes are polynomially large, so omitting actual source
prime collisions or excluding receiver named primes from its
sieve loses \(1+o(1)\) in the local model, with the target factors
retained in \(\mathfrak S(N)\). In the physical lower any omitted
receiver atom with a named prime dividing its own quotient,
or with a repeated quotient prime, is removed by the actual
\(p^2\mid x\) or \(p^2\mid y\) floor. All these primes are
\(>N^{.006}\); the bound \(O(N^{1-.006}+\sqrt N)\) with
divisor-bounded tag multiplicity is negligible. All moments
are taken in the common squarefree measure. In particular the
shifted square retains the \(d^2\) contribution on the true
zero-score ranks; those rows are not treated as if absent.

The cell volumes here are the ordered limits of real reciprocal
prime harmonics after multiplication by the named angles.
With multiplicities \(n_j\) of the distinct angular cells,
an arm with \(r\) tags gives volume \(.004^r/\prod_j n_j!\).
Indeed in each occupied interval the distinct-prime harmonic
is symmetric and exactly \(n_j!\) ordered allocations have
the same unordered product; the diagonal is negligible by the
polynomial floor. Different intervals force their own order.
This is equally valid when bounding a nonconstant weight,
since each moment bound below is uniform over the *full* cell
product before enforcing the order. The other factor is the
size of the real spatial interval; reflection preserves that size.
All field multiplicities in BV remain bounded by fixed powers
of the divisor function, including when angular cell labels tie.

## 2. The third real finite difference and interval verification

The two-tag ordinary mean and second moment use the same genuine
one-integer formulas as the one-by-two theorem, §3. We use the
simple ordinary bound
\(m_{\rm L}(A_+)\le\sqrt{m_{\rm L}(1)m_{\rm L}(A^2)}\).
It is Cauchy only on the unopposed one-integer angular measure.
The mass \(m_{\rm L}(1)\) is the plus density
\(b_+(1-u-v)\) on the exact unmarked rough quotient.
For the three-tag score replace \(g\) there by the third actual
divided difference
\[
       g_3(s)=\frac{(1-\tau_{\tilde u})(1-\tau_{\tilde v})
                              (1-\tau_{\tilde w})F(s)}
                         {\tilde u\tilde v\tilde w},\qquad
               \tau_tF(s)=F(s+t).
\]
It equals the uniform average of
\(-F'''(s+\tilde u V_1+\tilde v V_2+\tilde w V_3)\) over
\(V_i\in[0,1]\). This is an exact integral representation for
the products of actual prime labels, not an extra probabilistic
assumption on the opposite arithmetic coordinate.

Write \(h=(\tfrac12-s-\tfrac12(\tilde u+\tilde v+\tilde w))_+\),
and \(\sigma^2=(\tilde u^2+\tilde v^2+\tilde w^2)/12\).
When \(s+\tilde u+\tilde v+\tilde w\le\tfrac12\), the exact
average is \(1056h-13440h^3-40320h\sigma^2\).
This follows from the centered cube's first and third moments
being zero, and its second moment \(\sigma^2\).
If the interval can meet the profile endpoint, use an outward
range of \(1056v-13440v^3\) for
\(v=(1/2-z)_+\) across the full possible \(z\)-interval.
The cubic extrema on each nonnegative interval are the endpoints
and, if present, the maximum at \(v=\sqrt{11/420}\).
The checker brackets this fixed root by squaring both endpoints.
Here \(T=1-\tilde u-\tilde v-\tilde w\) in the right density,
and the same four occupied classes and shift atom \(d\,1_{s=0}\)
as in the one-by-two theorem enumerate **all** its actual
rough quotient ranks. Fixed-floor own-log errors are uniform \(o(1)\)
on these bounded ranks and use the same true count as before.

The [exact checker](check_two_by_three_tag_credit.py) verifies
the hash of the preceding interval code and reuses its outward
\(10^{-4}\) density bins, occupied-class separator integrals
(now 160 separator bins), moment identity, and elementary
sieve constants. It then adds the explicit cubic interval and
the cell factorials above. Run it with
`python -OB check_two_by_three_tag_credit.py` in this directory.
The integer shift is \(d=\lfloor1000-2000s_0\rfloor\), where
\(s_0\) is the center sum of the right tags.
The checker demands a strictly positive lower in **every** cell,
not only in a selected favorable subset. It verifies 115 left
cells and 349 right cells, totaling 40135 whole paired cells,
and bilateral lower \(>.0395335\) with all the genuine
ordering factors included. Thus the full chamber contributes
\(>.0395M+o(M)\). Adding this credit once to the exact smaller
exterior comparison gives the stated inequality.
