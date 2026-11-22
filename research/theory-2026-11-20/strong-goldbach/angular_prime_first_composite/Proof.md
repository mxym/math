# A 3.446 upper from removing true first-prime composite rows

Keep the literal same fixed-target angular prime-product source of
[AngularPrimeDomination](../AngularPrimeDomination.md).
Thus \(N\) is any large even target, \(I=[N/3,2N/3]\),
\(X_N=|I|\mathfrak S(N)\), \(\Pi(y)=(\log N)1_{y\ {\rm prime}}\),
and \(C(x)\ge0\) is \(\log N\) times a bounded nonnegative fixed-rank
(\(k\ge2\)) angular weight on a genuine squarefree product \(x\in I\)
of \(k\) primes, each of fixed positive polynomial size.
The same position weights and compact Jordan approximation are allowed.
Let \(m_C=|I|^{-1}\sum_{x\in I,(x,N)=1} C(x)\).
Then
\[
 \limsup_{\substack{N\to\infty\\N\ {\rm even}}}
     \left[\frac{\langle C,\Pi\rangle}{X_N}-3.446\,m_C\right]\le0.
                                                               \tag{1}
\]
This improves the verified \(400/111\) from
[the level .555 ordinary Rosser support](../angular_prime_level_555/Proof.md).
It uses a positive subtraction on the **actual complement** \(y=N-x\)
and 340 ordinary independent marked lower sieves, not a larger
uniform level or an upper with an unspecified factorable sequence.

## 1. A pointwise disjoint subtraction

Put \(X=N/3\) and \(R_\eta(y)=1_{P^-(y)>X^\eta}\).
Restrict first to the actual units \((x,N)=1\); then \((y,N)=1\).
Our base roughness exponent is \(a_0=.1125\).
For \(0\le j<340\), set
\[
 a_j=a_0+\frac{j}{4000},\qquad b_j=a_j+\frac1{4000}.
\]
The half-open marked bands \((X^{a_j},X^{b_j}]\) fill
\((X^{.1125},X^{.1975}]\) with no overlap.
For each such \(q\) a true prime, require
\[
                     q\mid y,\qquad R_{b_j}(y/q)=1.           \tag{2}
\]
This implies \(q=P^-(y)\) and \(q^2\nmid y\), since
\(q\le X^{b_j}\); in particular two different marks cannot
occur on any single \(y\). All these rows are \(a_0\)-rough,
and are composite since \(y\asymp X\) while \(q\le X^{.1975}\).
Every true prime \(y\in I\) is base-rough and admits none of
these marks. Consequently
\[
 1_{y\ {\rm prime}}\ \le R_{a_0}(y)
       -\sum_{j=0}^{339}\sum_{\substack{X^{a_j}<q\le X^{b_j}\\
                                      q\ {\rm prime},\,q\nmid N}}
                   1_{q\mid y}R_{b_j}(y/q).                  \tag{3}
\]
The indices in the inequality are true marked composite
occurrences, not signed short divisors or a model of least labels.

For \(R_{a_0}\) take the positive upper product of the small-bank
and large-bank ordinary Rosser upper sums, at the usual physical
large-bank level \(D=X^{.555}\). The .555 proof's support argument
applies with this smaller prime ceiling too; we change only the
argument of its principal sieve function. For the marked term
in each \(j\), apply the positive-lower comparison to \(y/q\)
at a different allowed level, as follows.

## 2. Honest lower weights and the actual marked modulus

Let \(\theta=7/32\) and \(\alpha=1.001\); define
\[
 \begin{split}
 V_j={}&\min\left\{\frac{1+a_j}{2},\
       \frac{1-(3/2-2\theta)b_j}{1+\theta},\
       1-\frac{\alpha\theta+3b_j}{2}\right\},\\
 \Theta_j={}&V_j-.00007,\quad
 D_j=V_j-.00015,\quad
 r_j=D_j-b_j,\quad s_j=r_j/b_j .
 \end{split}                                                    \tag{4}
\]
Here \(X^{r_j}\) is the physical large-bank level in the
quotient sieve. The exact checks show
\(2.008<s_j<3.933\) for every bin. In particular
\(2b_j<r_j\), so the leading lower Rosser square test
at the prime ceiling \(X^{b_j}\) has power slack.

Use a small-prime bank up to \(X^\xi\) with upper and lower
fundamental-lemma divisor sums \(H_s,L_s\) of level \(X^b\)
and a separate large-prime bank to \(X^{b_j}\), with
upper and lower ordinary Rosser sums \(H_l,L_l\) of level
\(X^{r_j}\). Take \(b\) sufficiently small and then
\(\xi\ll b\), just as in the original proof.
For any one integer the true product bank-avoidance
indicator is bounded below by
\[
                     L_s H_l+H_s L_l-H_s H_l.                 \tag{5}
\]
Both upper functions are nonnegative. Replacing the \(L\)'s
in (5) by their own bank indicators gives a difference from
the true product equal to the negative of the product of
the two nonnegative upper errors. Thus (5) is a lower,
even when an individual lower function is negative.
All sieving primes dividing \(N\) may be omitted on the
actual target units, where they never divide \(y\) or \(y/q\).

For the distinct decreasing prime factors in the residual
large-bank label \(d\), the true lower support requires the
first-square test and **even cubic** prefix tests, as in
[Lichtman, §6.1](https://arxiv.org/html/2309.08522v1#S6).
They imply all-prefix square support at level \(X^{r_j}\):
at odd positions \(>1\) use the preceding even cubic, since
the next prime is no larger. The upper support has odd cubics
and gives the same all-prefix consequence. The rounded
versions can be obtained by rounding the exponents up in
the actual cubic tests; a first rejected even branch has
a nonnegative subtree contribution and truncating it gives
a lower, while rejecting an odd branch gives an upper.
The leading square test stays automatic. For fixed
\(\xi\), this changes the principal by \(o_\Delta(1)\)
if the exponent mesh \(\Delta\to0\) after the large-target
limit: only finitely many thin walls in compact exponent
boxes are involved. The new coefficients, not the unrounded
ones, are the ones evaluated in progressions.

We claim **the actual modulus \(qd\)** has all-prefix square
support at exponent \(D_j\) in (4), when \(q\nmid d\).
Insert the named \(q\) into the descending list of \(d\).
For every other prime's square test, the prefix is either
unchanged or obtains the one factor \(q\), so it satisfies
the claimed level since \(q\le X^{b_j}\).
At the new slot \(q\) itself, if it is first its square
fits since \(2b_j<D_j\). Otherwise let \(p>q\) be the
immediate predecessor and \(B\) the product of all preceding
residual primes before \(p\). Its actual test is
\(B p q^2\le (B p^2)q\le X^{r_j}q\).
This covers the case where some residual labels slightly
exceed \(q\) within its bin; we do not assume \(q\) is the
first factor in a literal ordered label. The full largest
prime still has exponent in \([a_j,b_j]\) since \(q\) is
in that bin and no residual sieve prime exceeds \(X^{b_j}\).

In a dyadic product chart of scale \(X'\asymp X\),
replace these exponents by those on base \(X'\) with only
\(O(1/\log X)\) changes. The actual residue is \(N\le
(X')^\alpha\) eventually. Thus Lichtman Proposition 6.1,
first alternative (6.2), applies at notional
\(\Theta_j\), with strict slack from \(V_j\).
The actual support exponent \(D_j\) leaves room for the
printed \(2\tau\) shrink and then the one independent
small-bank slot. For a medium selected source length
\(B_s\), use \(A=B_s(X')^{-\tau}\) with the same
\(A\)-range and margins as in the .555 proof.
Choose \(0<\tau\ll .00004\), allowing the source's
fixed polynomial support as well, then \(b\ll\tau\),
\(\xi\ll b\) and a fine enough independent exponent mesh.
The three product margins \(3\tau,3\tau,2\tau\) absorb,
respectively, \(2\tau,\tau,(1+2\theta)\tau\) from moving
\(A\) back to \(B_s\), and the small bank factor in
group three as before. This checks the actual Prop. 5.2
including its \(|a|^\theta\) rail. In particular no
claim about arbitrary arithmetic progressions at level
\(D_j\) is being used.

For a fixed rounded residual list, choose one representative
with the named \(q\) and the fixed index groups. The same
assignment applies to every true prime tuple in that
box with the rounded exponent data. Even when \(q\) and
other primes lie in the same rounded bin, the \(q\) slot
remains named; the integer coefficient is the product of
its own prime indicator and the independent residual
group coefficients. Underlying residual primes within
an equal exponent bin can be freely permuted with the
factorial normalization of the original proof. The marked
slot itself is not divided by a residual factorial.
This fixes each group independently of the actual source.
There are finitely many boxes at fixed \(\xi,\Delta\)
and only polylogarithmically many further dyads.

We keep the literal divisor identity for all repeated events
in the physical lower, before any analytic deletion.
The condition is \(q\mid y,\ d\mid y/q\), equivalently
\(qd\mid y\) also when \(q\mid d\). All terms with
\(q\mid d\) therefore have \(q^2\mid y\), and
\(q>X^{a_0}\). Their **total** physical contribution is
\(O(X^{1-a_0+o(1)}+X^{b_{339}+o(1)})\), summing the
integer square multiples weighted by fixed divisor powers
and log powers. In the model, moduli divisible by such
a square cost \(X^{-a_0+o(1)}\) in harmonic mass
relative to the ordinary source bound. The same
fixed-power argument handles any artificial repeated
large-prime labels introduced by dropping equality
restrictions inside independent coefficient factors;
the small and large banks are disjoint. Thus one may
equivalently omit \(q\) in the quotient model after
this power-small correction. **No repeat is falsely
counted as a genuine occurrence of (2)**.

The source proof is exactly as in the angular upper:
separate each smooth positive source profile into its
HB slots; the selected medium weight has auxiliary-mask
Siegel--Walfisz. The other coefficient is trimmed by
divisor moments, and three independent boxed modulus
groups just verified are used in Prop. 5.2.
If there is no medium slot, a fixed-rank source
with \(k\ge2\) has exactly two long free slots,
one in each of two original factors; all other
factors have product \(X^{O_k(\tau)}\).
Uniform-residue Lichtman Prop. 3.2 pays this branch:
every \(D_j\) in (4) is below .6, with room under
the \(2/3\) bound even after freezing the short
product. Actual \(X^{1/(\log\log X)^3}\) roughness of
the two free slots, log/position cutoffs and proper
prime power deletions are handled in the original
proof. No source prime on \(y\), beyond the final
one being bounded, is inserted by this argument.
Evaluate all rounded upper and lower sums in (3)
using these centered progression estimates.

## 3. The true subtraction and the scalar check

Both model sums retain the exact \((x,qd)=1\) mask.
For a fixed genuine source \(x\), its primes all have
fixed positive polynomial size; omitting them from
the sieve Euler product costs a relative \(1+o(1)\)
at each fixed angle bound.
The factor \(q\) has exact conditional density
\(1/(q-1)\) when \((q,xN)=1\). If \(q\mid xN\) it is
omitted from the harmonic \(q\)-sum: for \(q\mid x\)
there are at most \(k\) possible such labels,
and for \(q\mid N\) at most \(O(\log N)\);
their reciprocals are \(O((\log N)X^{-a_0})\).
The genuine prime \(q\) is not a second sieve level
or an independently payable secondary factor.
After extracting it and removing repeats, the local
\(d\) density remains \(1/(p-1)\) outside these
known unit masks. The product up to \(X^{b_j}\)
is therefore
\((1+o(1))e^{-\gamma}\mathfrak S(N)/(b_j\log N)\),
uniformly for the fixed original source profile.
The quotient lower (5) has the relative linear-sieve
factor at least \(f(s_j)-o(1)\) after taking the
rounding mesh and then the small-bank prime exponent
to zero as in the original proof. This lower uses
\(f(s)=2e^\gamma\log(s-1)/s\) for \(2\le s\le4\).
The \(q\)-harmonic in its true half-open interval is
\(\log(b_j/a_j)+o(1)\) by Mertens.
Thus the normalized amount removed at the \(j\)th
bin is at least
\[
                   \frac{2}{r_j}\log(s_j-1)\log(b_j/a_j).
                                                               \tag{6}
\]
There is no independence assumption about actual
factor counts at \(N\): (6) is a lower for the
specific **fixed-target weighted subcount (2)**
after applying the legitimate signed lower weights
on the actual quotient. This distinction is why
the subtractions may be spent inside (3).

For the first term of (3) the base upper has
\(s_0=.555/.1125\in[3,5]\).
The standard delay equation
\((sF(s))'=f(s-1)\), with \(3F(3)=2e^\gamma\),
gives its normalized upper coefficient
\[
           C_{\rm up}
      = \frac{2}{.555}
             \left(1+\int_3^{s_0}\frac{\log(u-2)}{u-1}\,du\right).
                                                               \tag{7}
\]
We use the exact ordinary Rosser upper model only,
at the already proved .555 support. In (7) the
factor \(\log N\) times the local product has been
included, so the comparison is with exactly \(X_Nm_C\).
The same normalization was used in (6).

The [exact arithmetic checker](check.py) proves
\[
       C_{\rm up}<5.0017,\qquad
       \sum_{j=0}^{339}\frac{2}{r_j}
               \log(s_j-1)\log(b_j/a_j)>1.55617,\qquad
       C_{\rm up}-\sum_{j=0}^{339}(\text{6})<3.446 .
\]
The checked directed bounds are about
\(5.001370669\) and \(1.556170827\).
For completeness the integrand in (7) is increasing
on \([3,5]\), since its derivative has sign
\((u-1)/(u-2)-\log(u-2)\ge4/3-\log3>0\).
The checker uses its right endpoints on 4096
equal cells, enclosing each logarithm by
\(2\sum_{h<n}t^{2h+1}/(2h+1)\) with \(t=(v-1)/(v+1)\)
and an explicit positive geometric upper tail.
The marked scalar lower sums use the same lower
logarithms and rational exponents. All interval
decisions and inequalities are exact, also with
Python optimization enabled. Combining (3),
(6), and (7) proves (1).

## 4. Same physical signed response and scope

The native quadratic signed comparison in
[AngularPrimeDomination, equations (2) and (4)](../AngularPrimeDomination.md)
is unchanged: its \(J_H\) response to a nonnegative true
bounded-rank source subtracts exactly \(4m_C\)
from the prime response, up to the stated iterated-limit
error. We now get the strictly negative slope \(-.554\)
rather than \(-44/111\) from the .555 theorem.
Using the existing genuine rank-two and rank-three
small-factor control in that proof, the disjoint
first-coordinate ranks of the single ordered comparison
satisfy
\[
 \liminf_{\theta_0\downarrow0}\liminf_{N\to\infty}
 \frac{\langle J_{H,2}+J_{H,3},J_H\rangle}{X_N}
       \ge .554\big(2+4\log2-\pi^2/6\big)>1.73 .
\]
This is not a second reflection orientation and not an
upper or lower for all native signed terms. The angular
upper can be used for genuinely nonnegative pieces of
other scores, but not for an arbitrary signed
linear-cusp correlation in place of its original ledger.

The underlying idea of removing actual least-prime
classes is ordinary Buchstab, not a new sieve identity.
See [Lichtman, §7](https://arxiv.org/html/2309.08522v1#S7)
for substantially more extensive decompositions on the
original one-prime source. The present bound uses only
one disjoint removal level and explicitly transfers it
with moving residue to the actual **product-prime**
source. [Slava Chan's November preprint, Theorem 2.1
and Proposition 4.1](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf)
claims a stronger \(3.3808684\) in the same
normalization for the overlapping finite smooth
bounded-rank product-prime class. Its large-modulus
and coefficient constructions are not imported or
independently certified here. We do not claim priority.

The result makes the actual positive envelope smaller
and improves a genuine native signed interaction; it
does not provide the independent signed high-rank
control needed in the binary Goldbach inequality.
