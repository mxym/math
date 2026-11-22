# A direct fixed-target composite proxy for actual binary Goldbach pairs

We now test the arithmetic score against a **genuine prime on the other
side of \(N\)**. This is different from the shared-index columns, in
which the other side of \(N\) is a product of two large integers.
The analytic device is a real moving gap around the square-root
divisor cutoff. Ordinary Bombieri–Vinogradov is used only below
its actual level, including the rough sieve divisors. The resulting
high-rank signed condition remains open.

Let \(N=2x\) be even, \(L=\log x,\ \ell=\log L,\ z=\exp(L/\ell^2)\),
and \(R_z(y)=1_{\{P^-(y)>z\}}\).
Let \(J=xJ_0\) for a fixed nondegenerate interval
\(J_0\subseteq[1,3/2]\).
Write the literal logarithmically weighted Goldbach count
\[
 {\cal G}_J(N)=\sum_{\substack{y\in J\\y,\ N-y\ {\rm prime}}}
                      \log y\,\log(N-y).
\]
Every prime on its right is genuine. Define
\[
 \mathfrak S(N)=\prod_{p\mid N}(1-1/p)^{-1}
                  \prod_{p\nmid N}(1-(p-1)^{-2}).
\]
Here \(N\) is even, so the product is positive and
\(\mathfrak S(N)\asymp N/\varphi(N)\).

Fix an odd integer \(m\ge3\), then
\(0<\epsilon<\min(.005,.04/m)\), before \(x\to\infty\).
Put
\[
 \delta_x=3\,\frac{\log\ell}{\ell},\qquad
 R_-=x^{1/2-\delta_x},\quad R_+=x^{1/2+\delta_x},
 \quad R_0=\sqrt{1.5x},\qquad C_y=y/x^{1-\epsilon}.
\]
(The formulas are used only for sufficiently large \(x\).)
Define \(S_+(b)=\sum_{a\mid b,\ a>R_+}\log(b/a)\).
Use the two-small cofactor sets from the
[calibrated completion](../calibrated_two_small_completion/Proof.md):
\(\mathcal P_y\) consists of \(c=pq\ge C_y\) with distinct primes
\(z<p<q<C_y\), and \(\mathcal H\) consists of \(c\)'s that are
products of \(m\) genuine primes from fixed, pairwise disjoint
exponent intervals in \((.4\epsilon,.8\epsilon)\).
They all exceed \(z\) for large \(x\);
\(c>C_y\) on \(\mathcal H\), and no such factorization is counted twice.

Let \(\lambda_+(y)\) be the explicitly calibrated, nonnegative
function from Section 2 below, and put
\[
 w_y(c)=\mu_2(c)1_{c<C_y}
       +4\,1_{c\in\mathcal P_y}
       -2^m\lambda_+(y)1_{c\in\mathcal H},
 \qquad \mu_2=\mu*\mu .
\]
The actual, prime-free partner score is
\[
 {\cal R}_{\rm gap}(y)=R_z(y)
   \left\{\sum_{\substack{r\mid y\\r>R_-}}\mu(r)\log(y/r)
       +\sum_{c\mid y} w_y(c)S_+(y/c)\right\}.                     \tag{1}
\]
Both terms in braces are exact finite sums.
Define its no-gap reference \({\cal R}_0(y)\) by
replacing \(R_-,R_+\) in (1) by \(R_0\), using the same
actual \(\lambda_+(y)\).

**Direct fixed-target conclusions.**
1. For each sufficiently large even \(N\), uniformly in its
arithmetic factors and with the fixed parameters above,
\[
 {\cal G}_J(N)=
   \sum_{\substack{y\in J\\N-y\ {\rm prime}}}
       \log(N-y)\,{\cal R}_{\rm gap}(y)
       +O_A(xL^{-A})                                               \tag{2}
\]
for every fixed \(A>0\).
2. For every fixed integer \(r_0\), replacing
\({\cal R}_{\rm gap}\) by \({\cal R}_0\) on the **actual**
squarefree ranks \(\omega(y)\le r_0\) costs at most
\[
 O_{r_0,m,\epsilon}\!\left(
       x\mathfrak S(N)(\delta_x+L^{-1})
                          (1+\log\ell)^{\max(r_0-2,0)}\right)
      =o(x\mathfrak S(N)).                                        \tag{3}
\]
No unsigned bound is claimed on the unbounded-rank gap.
3. The reference score is nonnegative on every squarefree
rank \(\le4\) and also on every squarefree \(y\) with at most
one genuine prime factor below \(C_y\).
The latter set has bounded rank for fixed \(\epsilon\).
The true paired sum over this nonnegative union is
\(\gg x\mathfrak S(N)\), through the explicit genuine
two-mark reservoir in Section 4.
Thus any missing positivity is a signed question about actual
rough \(y=N-p\) of rank at least five with at least two small
true prime factors. A genuine lower on the whole sum that
controls this last term is not established.

## 1. True prime-weighted transfer below the real gap

Take Bonferroni depth \(B=\lceil\ell\log\ell\rceil\)
for the \(z\)-rough condition. Every opened positive
or negative divisor \(d\) and every next-degree error
divisor is squarefree, supported on primes \(\le z\), and
\[
       d\le z^{B+1}=x^{(\log\ell)/\ell+o(1/\ell)}.
\]
For the short raw divisor \(r\le R_-\), the complementary
variable \(y/r\) is free. For the free-score terms \(a>R_+\)
with \(y=s c a\), put \(b=sc\); then
\(b\le1.5 R_-\) in the actual macroscopic box.
Keep \(R_z(r)\) or \(R_z(b)\) on the fixed factor, and
open only the rough free factor by these divisors \(d\).
Thus the exact prime progression has modulus \(rd\) or \(bd\)
and residue \(N\), after writing \(p=N-y\).
The factor \(r\) or \(b\) is \(z\)-rough, whereas \(d\)
is \(z\)-smooth and squarefree; these factors are coprime
and their reconstruction from this modulus is unique.
Both actual moduli are bounded by
\[
 1.5x^{1/2-\delta_x}z^{B+1}
   \le x^{1/2-(3/2)(\log\ell)/\ell}
\]
eventually, so lie below the ordinary Bombieri–Vinogradov
level for any required fixed log reserve. There is no
application to an uncut square-root modulus.

The actual prime values \(p\mid N\) contribute
\(O(x^{o(1)})\) with the fixed divisor/log envelopes,
since there are \(O(L)\) of them. Otherwise \((y,N)=1\).
Hence only moduli coprime to \(N\) appear.
When \(d\) shares a prime with \(N\) the true term is absent.
The prime main for each raw opened term is length divided
by \(\varphi(rd)\) or \(\varphi(bd)\).
We use the maximal prefix form of Bombieri–Vinogradov
for the Chebyshev sum on genuine primes.
The windows \(y>scR_+\), \(y>c x^{1-\epsilon}\),
and the literal pair condition defining \(\mathcal P_y\)
are intersections of intervals for each fixed cofactor tuple.
The weight \(\log(y/r)\) in the short raw branch costs
\(O(L)\) by partial summation. In the signed correction
\(\lambda_+(y)\) below has bounded log-power variation,
so it is also covered by the same maximal prefixes.

Here is the divisor-weight justification.
The degree-one coefficients of \(\mu(r)\) have
absolute size at most one. For fixed \(b\)
the decomposition \(b=sc\), with its actual
\(|\mu_2(c)|\) weight or the finite prime tags in
\(\mathcal P_y,\mathcal H\), costs a fixed divisor power.
The constants \(2^m\) and the bounded \(\lambda_+\)
depend only on the fixed parameters.
Thus the aggregated coefficient of a modulus including
all exact tuple multiplicities is at most
\(L^C\tau(q)^D\) for fixed \(C,D\), after partial
summation. From the ordinary unweighted BV bound
one obtains this weighted bound by Cauchy:
if \(\Delta(q)\) is the maximal discrepancy then
\[
  \sum_q\tau(q)^D\Delta(q)
  \le \left(\sum_q\Delta(q)\right)^{1/2}
      \left(\sum_q\tau(q)^{2D}\Delta(q)\right)^{1/2}.
\]
The second factor is \(O(x^{1/2}L^{C_D})\)
by \(\Delta(q)\ll xL/q\) and divisor moments,
while the first saves arbitrary logs.
This proves the total prime replacement without
treating the weights as factorable.

For the signed roughness error, the difference
between the rough indicator and its Bonferroni
polynomial is bounded by the next positive
factorial polynomial. Its literal prime average
is evaluated or bounded by the very same BV argument
with \(d\) from degree \(B+1\) and nonnegative
coefficient magnitudes. Its harmonic main is bounded
by
\[
 \frac{(\sum_{p\le z,\ p\nmid N}1/(p-1))^{B+1}}{(B+1)!}.
\]
The numerator harmonic sum is \(O(\ell)\);
the factorial at \(B\asymp \ell\log\ell\)
saves every fixed power of \(L\).
The other harmonic sums and fixed divisor/log
weights cost fixed log powers.
This bounds the actual prime-weighted sieve error,
not only a product of two modeled marginals.
For the main, completing the finite rough Euler
product introduces the same kind of error.
The exact common rough factor is
\[
  V_N(z)=\prod_{\substack{p\le z\\p\nmid N}}
                         (1-1/(p-1)).
                                                                    \tag{4}
\]
There is no \(p=2\) factor here because \(N\) is even.

## 2. Both principal signs and the exact calibration

Put \(V_z=\prod_{p\le z}(1-1/p)\).
In each of the preceding harmonic models,
replace \(\varphi(r)\) or \(\varphi(sc)\)
by \(r\) or \(sc\): all their prime factors
exceed \(z\), so the relative error is \(O(L/z)\)
pointwise. This also covers common primes of \(s,c\);
we did not need their pairwise coprimality.
Dropping the remaining \(p\mid N,\ p>z\) exclusions
from the harmonic coefficients costs at most
\(O(L^C/z)\), by dividing by an omitted prime
and the ordinary harmonic divisor moments.
Thus (4) is the same factor in **every** signed model.
Uniformly,
\[
                 V_N(z)/V_z=\mathfrak S(N)(1+O(L/z)).
                                                                    \tag{5}
\]

Write
\[
 F_-(y)=R_z(y)\sum_{\substack{r\mid y\\r\le R_-}}
                      \mu(r)\log(y/r).
\]
For fixed physical \(y\), the leading short model is
\[
 V_N(z)\sum_{r\le R_-}
             \frac{\mu(r)R_z(r)}r(\log y-\log r).
\]
The Dirichlet series of the harmonic coefficient is
\(\zeta(1+w)^{-1}\prod_{p\le z}(1-p^{-1-w})^{-1}\).
At zero it has a simple zero with derivative \(1/V_z\).
The fixed positive-power endpoint \(R_-=x^{1/2-o(1)}\)
therefore gives moments \(0,-1/V_z\) for
weights \(1,\log r\), respectively, up to arbitrary
logarithmic error. Use the rough Perron shift
\(\Re w=-c/\log z\), and the first derivative,
as in the [hyperbolic evaluation](../hyperbolic_composite_proxy/Proof.md).
The modified endpoint still saves \(\exp(-c'\ell^2)\),
and the finite Euler product and Perron truncation
bounds are uniform. Consequently
\[
       \sum_{y\in J,\ N-y\ {\rm prime}}\log(N-y)F_-(y)
                   =|J|\,\mathfrak S(N)+O_A(xL^{-A}).             \tag{6}
\]

For any admitted true \(c\le 3x^{m\epsilon}\), the
free model has \(s<y/(cR_+)\), which is polynomial
and greater than \(x^\xi\) with \(\xi=.10\).
Define the exact short harmonic contribution
\[
 H=\sum_{s\le x^\xi}R_z(s)\frac{\log s}{s},
 \qquad
 J_c^+(y)=\frac{H}{V_z}
       +\tfrac12[(\log(y/(cR_+)))^2-(\xi L)^2].
\]
Indeed the true short \(s\)-part is \(H\).
For the long \(s\)-part use the rough density \(V_z\):
ordinary integer floors after Bonferroni give
arbitrary-log precision in each prefix beyond
\(x^\xi\) and partial summation against \(\log s/s\).
The factor \(1/c\) comes from the harmonic
\(1/(sc)\) of the actual prime modulus.
Thus the model to insert for any free cofactor
of coefficient \(w_y(c)\) is exactly
\[
             V_N(z)V_z\,\frac{w_y(c)}c\,J_c^+(y).
\]
The target factors have been removed from the harmonic
short \(s\)-sum only at the \(O(L^C/z)\) cost noted above.
No assertion on independence of \(p\) and \(N-p\)
precedes this actual BV calculation.

Define
\[
 \lambda_+(y)=
   \frac{4\displaystyle\sum_{c\in\mathcal P_y}J_c^+(y)/c}
        {2^m\displaystyle\sum_{c\in\mathcal H}J_c^+(y)/c}.
                                                                    \tag{7}
\]
The denominator is positive and comparable, for fixed \(m,\epsilon\),
to \(H/V_z+L^2\). The same is an upper bound for the numerator:
the harmonic triangle
\(u,v<\log C_y/L,\ u+v\ge\log C_y/L\)
has bounded reciprocal prime mass, as in the calibrated
two-small completion. Each actual pair contributes only
through an interval in \(y\) and at most two jumps.
The crude full harmonic pair count is \(O((1+\log\ell)^2)\);
the continuous integrand varies by \(O(L)\).
Exactly as in that note, this gives
\(\lambda_+=O_m(1)\) and total variation
\(O_m((1+\log\ell)^2)\), with the starting \(x\)
depending on the fixed parameters.
Thus (7) is valid for the exact literal weights both
in the mean and in the prefix error in Section 1.
It cancels the two corrective models exactly.

For the hyperbolic part \(c<C_y\), the first three
partial harmonic moments of \(\mu_2(c)R_z(c)/c\)
are \(0,0,2/V_z^2\) up to arbitrary-log errors.
This follows from the same rough Dirichlet series
squared and its double zero; \(C_y\asymp x^\epsilon\)
has fixed positive exponent.
Therefore its sum against \(J_c^+(y)\) is
\(1/V_z^2+O_A(L^{-A})\).
After multiplying the common factor \(V_N(z)V_z\),
the free terms **added in (1)** have true
prime-weighted mean \(+|J|\mathfrak S(N)\).
Equivalently the negatively defined \(F\)-score
would have \(-|J|\mathfrak S(N)\).
The sign matches (6) and cancels it in the final
\(\Lambda\) transfer, not doubles it.

Indeed \(R_z(y)\sum_{r\mid y}\mu(r)\log(y/r)=R_z(y)\Lambda(y)\)
exactly. On genuine primes of this scale \(R_z=1\);
proper prime powers can be dropped with
\(O(x^{1/2+o(1)})\) error after the logarithmic weights.
Equation (1) is this exact identity **minus** \(F_-\),
plus the free sum whose prime-weighted mean is (6).
This proves (2), at the actual fixed even target.

## 3. The genuine bounded-rank square-root shoulder

For a fixed squarefree rank \(r\le r_0\), the only
differences between (1) and \({\cal R}_0\) come when
some actual divisor of \(y\) lies in \([R_-,R_+]\).
The two scores may differ pointwise there by \(O_{r_0,m}(L)\),
not by a putative small analytic shoulder.
Fix a nontrivial subset of its genuine primes whose
product is such a divisor. This subset and its complement
both have exponent sum \(1/2+o(1)\).
Choose one of the largest primes \(t\) in the complementary
subset, necessarily \(t\ge x^{c_{r_0}}\) for some fixed
\(c_{r_0}>0\). Fix every other actual prime factor,
with product \(D\), so the two true prime conditions
are on the integer variable \(t\):
\[
                            t,\qquad N-Dt .
\]
Its macroscopic range has scale \(U=x/D\asymp t\)
and hence polynomial length. If \((D,N)>1\),
there is no true macroscopic reflected prime except
the already excluded \(p\mid N\) case.
Otherwise use the ordinary two-form Selberg upper sieve
on this interval, at a fixed small power of \(U\);
both actual primes are larger than its sifting limit.
For \(p\nmid DN\) the two roots are distinct; for
\(p\mid N\) or \(p\mid D\) precisely one root is
excluded. Its singular factor is
\[
 \ll \mathfrak S(N)
       \prod_{\substack{p\mid D\\p\nmid N,\ p>2}}
                       (1+O(1/p))
 \ll_{r_0}\mathfrak S(N),
\]
since the fixed number of genuine primes of \(D\)
are all \(>z\). The parity prime 2 is already accounted
for by \(N\) even and \(D\) odd.
Thus the count of the last genuine prime satisfies
\(O_{r_0}(x\mathfrak S(N)/(D L^2))\).
The \(O(L)\) score and the actual \(\log(N-Dt)\)
pay the two logarithms exactly.

Among the fixed primes **inside** the cutoff divisor,
choose one of maximum size. It is also polynomially large,
and, when the others are fixed, its log exponent interval
has length at most \(2\delta_x+O(L^{-1})\).
The reciprocal prime mass of that interval is
\(O_{r_0}(\delta_x+L^{-1})\) by ordinary dyadic prime
upper bounds away from exponent zero.
Every other fixed prime contributes at most
\(\sum_{z<p\le2x}1/p=O(1+\log\ell)\).
The number of orderings and possible subsets
is bounded for fixed \(r_0\).
Summing these nonnegative upper bounds gives (3).
This proof counts actual prime \(N-y\) on the
same physical rows, not a fitted or averaged density.
It is essential that the rank \(r_0\) is fixed
before \(x\) grows.

Nonsquarefree true rough \(y\) can be omitted in the
natural-scale sign discussion: some \(p>z\) satisfies
\(p^2\mid y\), and the count \(O(x/z)\) with Cauchy
and the usual divisor moments pays the \(L^C \tau_4(y)\)
envelope of (1) and the logarithmic prime weight.
This is arbitrary-log even in the direct sum with
the prime condition dropped for this absolute bound.

## 4. An actual positive two-mark reservoir

The reference score has exactly the algebraic sign
proof of the [two-small completion](../calibrated_two_small_completion/Proof.md)
at cutoff \(R_0\): the all-rank no-small and one-small
arguments use only the exact cutoff ordering;
the rank-four argument sums all genuine small-pair
cofactor assignments. The negative \(m\)-prime payer
still vanishes on ranks at most \(m+1\), and is absent
whenever there is at most one eligible small prime.
No true prime pair was used in those statements.

We produce a positive reference contribution on real
rows at each prescribed target. Mark two genuine
distinct primes \(r,s\) in the exponent bands
\((.006,.007)\), \((.010,.011)\), respectively,
with \((rs,N)=1\). Let \(h=rs\).
Look at actual \(y=h a\in J\) with \(p=N-ha\)
genuinely prime, and sift \(a\) by all primes
\(\le w=x^{.21}\).
Use the ordinary lower **linear sieve** at level
\(D=x^{.47}\). For any squarefree divisor \(d\)
used in that sieve with \((d,N)=1\), the exact
prime progression is \(p\equiv N\bmod hd\)
with main \(|J|/\varphi(hd)\). If \(d\) contains
a prime dividing \(N\), the true term is zero once
the finitely many primes \(p\mid N\) are removed.
The prime sequence therefore has the multiplicative
dimension-one local factor
\[
 g_h(q)=
 \begin{cases}
 0,&q\mid N,\\
 1/q,&q\mid h,\\
 1/(q-1),&q\nmid Nh .
 \end{cases}
\]
This explicitly retains \(q\mid h\) and its
prime-power modulus, rather than assuming \((d,h)=1\).
Its finite product at \(w\) is comparable to
\(\mathfrak S(N)/L\) uniformly:
relative to \(V_N(w)\) only the two actual
large label primes modify it by \(1+O(1/r^2+1/s^2)\).
The dimension-one upper product condition holds uniformly
since \(g_h(q)\le1/(q-1)\) for \(q\ge3\), and \(g_h(2)=0\).
The lower function is strictly positive at
\(\log D/\log w=.47/.21>2\).

The lower-sieve remainder after all true \(h\)'s
is covered by BV at actual moduli
\(hd\le x^{.488}\). The number of reconstructions
is fixed divisor-bounded; the sieve weights are
bounded, so the same weighted BV argument applies.
It follows that the \(a\)'s in this physical band,
weighted by \(\log p\), have sum
\[
 \gg \frac{x\mathfrak S(N)}{L}
       \sum_{\substack{h\ {\rm actual\ two\ labels}\\(h,N)=1}}
                    \frac1{\varphi(h)}
                 \gg \frac{x\mathfrak S(N)}L .
\]
Here the two reciprocal prime bands each have
fixed positive mass; target divisors have negligible
harmonic effect. All exact rank conditions below can
be imposed after this lower sieve: \(a\asymp x/h\)
is \(w\)-rough and has at most four prime factors
because \(5\cdot.21>1\).
Any repeated prime of \(a\) exceeds \(w\);
its true absolute lost weight after all \(h\)'s is
\(O(x L\sum_{p>w}p^{-2})\), already negligible
without requiring \(p=N-ha\) prime.
The two marked primes occur exactly once and are the
only prime factors below \(w\), so there is no
uncontrolled label multiplicity.

All prime factors of these \(y\)'s exceed \(C_y\)
when \(x\) is large, since \(\epsilon<.005\).
There is no authentic small-prime corrective term,
and the reference score is
\(2\sum_{b\mid y,\ b>R_0,\ \omega(b)\ {\rm even}}\log(y/b)\).
There is always a positive summand of size \(\gg L\):
if \(a\) has even rank, use \(b=a\);
if it has rank one, use \(b=a r\);
if it has rank three, use the product of its largest
two primes, of size at least \(a^{2/3}>R_0\).
In every case the complementary logarithm includes
at least one genuine marked prime.
Thus the actual positive score on this reservoir is
\(\gg x\mathfrak S(N)\).
These \(y\)'s have rank from three through six.
Comparison (3) pays their exact gap discrepancy.
This does not assume or force an actual Goldbach pair:
all the selected \(y\)'s here are composite.

## 5. Exact remaining scope

At most one factor \(<C_y\) leaves the other factors
\(\ge x^\epsilon\), so those squarefree ranks are at most
\(2+1/\epsilon\) for fixed \(\epsilon\), and (3)
applies to their whole nonnegative reference union.
Discard nonsquarefree rough values at negligible cost
as in Section 3. Then (2) has a genuine, nonnegative
part given by that union and all ranks \(\le4\),
with the positive reservoir included, and the still
unknown term is the signed actual prime-weighted
\({\cal R}_{\rm gap}\) on ranks \(\ge5\) with at
least two eligible small primes.
It is not bounded by an unsigned treatment of the
full unbounded-rank square-root shoulder.

For exactly two eligible small primes there is a useful
further exact restriction in the no-gap score.
Write \(y=pq M,\ p<q<C_y\). In the notation of the
completed pair formula, a negative value can only
come from a divisor \(d\mid M\) of even rank with
\[
             R_0/p<d\le R_0,\qquad\text{weight }-2\log(M/d).
\]
Indeed the allowed small subset divisors of \(pq\)
then are \(p,q,pq\); their \(\mu\)-sum is \(-1\).
If all are allowed, or only \(q,pq\), this sum is zero,
and if only \(pq\) is allowed it is positive.
Odd-rank \(d\) gives a nonnegative coefficient as in
the two-small proof. The negative high-rank payer
cannot occur when there are exactly two eligible primes.
In particular when \(P^+(y)>R_0\) all admissible
divisors already contain that giant, and the exact
two-small completion gives zero: the full alternating
finite difference of \(\log(M)\) over both small
primes is zero. Thus this two-small class does not
have the former bulk giant debit.

At each fixed rank \(r_0\) one can also upper bound the
two-small exceptional class at natural scale by
\(O_{r_0}(x\mathfrak S(N)\epsilon
(1+\log(1/\epsilon))^{\max(r_0-4,0)})\),
after \(x\to\infty\).
Use the same true two-form upper sieve as Section 3,
with a longest genuine prime outside \(d\), and a
polynomial prime inside \(d\) whose harmonic exponent
width is at most \(\log p/L\).
Both macro groups have positive total exponent.
The two genuine tiny primes have harmonic integral
\(\int_0^\epsilon\int_0^\epsilon\min(u,v)\,du\,dv/(uv)
=2\epsilon\); dyadic endpoint fuzz \(O(L^{-1})\)
is negligible on the actual rough support.
The other macro primes are \(\ge x^\epsilon\),
giving the displayed log factors.
This does not sum uniformly over unbounded rank,
and it does not remove the three-or-more-small
population or its signed gap. A natural-scale lower
for the full remaining signed prime correlation is
still needed for a binary Goldbach conclusion.


### Follow-up: exactly two eligible small primes

The [opposite-divisor pairing](../direct_two_small_pairing/Proof.md)
uses the own square root to control the entire moving shoulder in this
family and proves nonnegativity at even total squarefree rank. At odd
rank it isolates a signed difference of Möbius values of the two actual
macro factors against the same opposite prime. That difference and the
part with at least three eligible small primes remain uncontrolled.

A [subsequent comparison](../direct_many_small_gate/Proof.md) bounds the whole exactly-two-small adverse contribution against a larger disjoint no-small reserve, without estimating the standalone Möbius difference. For sufficiently small fixed parameters the remaining signed estimate is restricted to actual squarefree complements of rank at least five with at least three eligible small primes, keeping the original calibration.
