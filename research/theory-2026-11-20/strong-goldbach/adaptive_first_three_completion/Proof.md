# Adaptive first-three completion on the true fixed-target prime leg

This is an alternative to completing *all* small subproducts in the
[direct all-small calibration](../wide_gap_all_terminal/Proof.md).
It uses only the first three actual small prime factors of each
squarefree integer, hence at most eight actual cofactor orientations.
The unpriced Goldbach positivity is still present in the fully
rough channel. The theorem below evaluates a signed score, not the
count of binary representations.

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(J=xJ_0\subset[x,1.5x]\), \(P=N-y\) an actual prime, and
\(R_z(y)=1_{P^-(y)>z}\), where
\[
 \ell^{-2}\le\chi=\log z/L\le\ell^{-1},\qquad
 w=\ell^{-1/3},\quad W=x^w,\quad U=\ell^{-1/4},\quad
 T_y=\frac{\log y}{2L},\quad D_y=T_y-U,\quad D_0=\tfrac12-U.
\]
For each squarefree rough y choose the first
\(\min(3,k)\) actual prime factors in \((z,W]\), increasing in
ordinary prime size, where \(k\) is the total number of these
prime factors in y. Let \(A_y\) be their squarefree product.
In the direct reciprocal gap with lower and upper cuts
\(\sqrt y\,x^{-U},\sqrt y\,x^U\), put
\[
 \mathcal R_3(y)=R_z(y)1_{\mu^2(y)=1}
 \left[
  \sum_{\substack{r\mid y\\r>\sqrt y\,x^{-U}}}\mu(r)\log(y/r)
   +\sum_{c\mid A_y}\mu_2(c)
               \sum_{\substack{a\mid y/c\\a>\sqrt y\,x^U}}\log(y/(ca))
 \right],\qquad \mu_2=\mu*\mu .
\]
The convention \(A_y=1\) for \(k=0\) is literal.
For \(k\le2\) this is identical to the all-completed score
with the same \(W\). For \(k\ge3\) it stops after the
first three even if y has many more actual W-small primes.

Write \(Q_w(t)\) for the cumulative of
\(\exp^*(2\,1_{u>w}du/u)\) (as in the wide-gap calibration),
and \(c_0=e^{-\gamma}\).
All errors below are uniform in even N and \(\chi\) in the stated
range, and \(o(x\mathfrak S(N))\) is at the genuine Goldbach scale.

**1.** The total signed actual prime average is
\[
 \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}\log P\,\mathcal R_3(y)
   = {\cal G}_J(N)
         +|J|\mathfrak S(N)\,[Q_w(D_0)-1]
                          +o(x\mathfrak S(N)).                    \tag{1}
\]
Thus it agrees to this precision with completing *all* small primes
at the **same W and the same U**, not with an independently
chosen fixed \(\epsilon\) or its baseline \(Q_\epsilon(1/2)\).

**2.** The entire actual \(k\ge3\) class has signed total
\(o(x\mathfrak S(N))\), even in the following strong form:
\[
 \sum_{z<p<q<r\le W}
  \left|\sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
             p,q,r\ {\rm are\ its\ actual\ first\ three}\\
             y\ z\text{-rough and squarefree}}}
          \log P\,\mathcal R_3(y)\right|
           =o(x\mathfrak S(N)).                                  \tag{2}
\]
This is not a pointwise estimate on \(\mathcal R_3(y)\) or
an absolute-value bound inside each triple. The individual
profile signs do not disappear. The same estimate also holds for the
fully completed score at W on these actual pinned triples (Section 4),
but its physical weights can differ whenever there are additional
small factors. Thus the truncation simplifies the arithmetic score,
not the occupation of its support.

**3.** After short-raw subtraction, the \(k=1,2\) channels
have computable same-target signed means. The only surviving
binary-prime term belongs to \(k=0\). More explicitly, let
\(F_k\), \(k=0,1,2\), be the total of the **free contribution**
on the true k channel, normalized by \(|J|\mathfrak S(N)\).
Then with \(D=D_0\),
\[
\begin{split}
 F_0 &= c_0^2\left[\frac{D^2}{2w^2}-\frac14\right]+o(1),\\
 F_1 &=\frac{c_0^2}{w^2}
       \left[2D(w-\chi)-\tfrac34(w^2-\chi^2)+w(w-\chi)\right]+o(1),\\
 F_2 &= \tfrac32 c_0^2(1-\chi/w)^2+o(1).
\end{split}                                                       \tag{3}
\]
The short-raw contribution has this normalization \(1+o(1)\)
for \(k=0\) and \(o(1)\) for each \(k=1,2\).
In particular (1) and (2) do not imply an improved lower bound
in the fully W-rough \(k=0\) channel.

## 1. Actual prime progressions with the first marks pinned

The exact full raw logarithmic divisor identity leaves
\(\Lambda(y)\) minus a short raw divisor sum after restricting
its cutoff. The reciprocal convention for the free term
gives the same short condition \(d\le x^{D_y}\) for \(d=y/a\);
differences of strict edge choices give \(O(x^{1/2+o(1)})\)
total for rough squarefree y. Every such edge divisor determines y.
A prime y belongs to \(k=0\); proper prime powers are negligible.

For a physical pinned tuple of \(j_0\) distinct actual tags,
where \(j_0=k\le2\) or \(j_0=3\) for \(k\ge3\), let \(A\)
be the product of all these tags. When \(k\ge3\), write r
for the largest selected tag and \(v=\log r/L\); when \(k\le2\)
put \(v=w\). A squarefree y in the indicated class is exactly
\(A\,s\,b\), where all the other prime factors of \(s,b\)
exceed \(x^v\). For \(k\ge3\), this is what makes the
selected triple the *first* three and does not forbid
any further prime factors above r. For \(k\le2\), it says
there are no other W-small factors.
For a short divisor \(d\mid y\), let \(A_I\) be the product of
its selected tag subset and \(j=\log A_I/L\).
Write \(d=A_I s\), so \(s\le x^{D_y-j}\), and
\(y=A\,s\,b\); b is the free remaining factor.
Given y and the actual short d, the allocation of tags
to the two legs is unique. Its eight-case sum is a sum over
true actual divisor orientations.

The exact short free factor for an allocation is
\[
 \sum_{c\mid A_I}\mu_2(c)\log(d/c)
                 =(-1)^{|I|}(\log s-Lj),                       \tag{4}
\]
by the zeroth and first subset moments of \((-2)^{\omega(c)}\).
The short raw factor is \((-1)^{|I|}\mu(s)
[\log y-Lj-\log s]\).
All tags are genuine primes; do not replace their selection
by an independent threshold on the free variable.

We evaluate the actual rough condition on b by the upper and
lower dimension-one fundamental lemma, with sieve level
\(H_0=x^{U/2}\) at cutoff \(x^v\) and the same positive
coefficient handling as the [thin-gap proof](../thin_true_giant_gap/Proof.md).
For a sieve divisor \(h\le H_0\), the literal modulus on P
is \(A s h\), even when some tag lies on the free side.
Since \(A s=(A/A_I)d\le W^3\sqrt{1.5x}\,x^{-U}\), this
modulus is at most
\[
     \sqrt{1.5x}\,x^{-U/2+3w}
                     \le \sqrt{1.5x}\,x^{-U/3}
\]
eventually, below ordinary maximal BV by more than any fixed
log reserve. The displayed short cutoff is a genuine prefix
condition in y for fixed d; the raw weight \(\log y\) is
handled by partial summation. Fixed divisor multiplicities
from the possible tuple reconstructions at a modulus
and eight allocations are bounded by \(\tau(Q)^{O(1)}\).
There is no factorability assumption on either signed
score. The sign of (4), when needed, is fixed after s and I
are pinned; raw positive logarithms are multiplied by the
fixed sign of \(\mu(d)\).
Dropping the P dividing N branches costs \(x^{o(1)}\).
As in the wide-gap proof, one can restore the squarefreeness
of the entire rough y after the AP calculation at arbitrary
log cost by its \(O(x/z)\) nonsquarefree count and fixed
divisor moments. Within the model one may therefore leave b
squareful or overlapping s as an intermediate; s is still
squarefree in the literal d. In harmonic sums replacing
squarefree s by all rough s in the free terms costs
\(O(L^{O(1)}/z)\) by its Euler harmonic square tail.

At a sieve prime \(p_0\le x^v\) dividing no target factor, the
density is \(1/(p_0-1)\) if \(p_0\nmid A\) and \(1/p_0\) if
\(p_0\mid A\) (then the exact modulus was multiplied by an
additional \(p_0\)). The excluded target primes have local
density zero; 2 divides N. The latter modified factors differ
by a product \(1+O(z^{-2})\) since every tag is \(>z\).
The common conditional main is therefore
\(V_N(x^v)/(A s)\) up to the same superlogarithmic errors
after replacing \(1/\varphi(A s)\) by \(1/(A s)\).
Removing remaining target prime divisors in the harmonic
using \(\sum_{p\mid N,\ p>z}1/p\ll L/z\) is harmless.

The smallest fundamental-lemma parameter is
\(U/(2w)=\tfrac12\ell^{1/12}\), whose factorial error saves
every fixed power of \(1/\ell\), uniformly at the moving r.
The total unsigned main over all pinned tags is bounded by
\(x\mathfrak S(N)\chi^{-2}(1+\log\ell)^3\):
use \(\sum_s R_{x^v}(s)/s\ll v^{-1}\),
the weights \(O(L)\),
\(V_N(x^v)\ll\mathfrak S(N)/(vL)\), and the absolute
reciprocal sum of at most three genuine prime tags.
Thus this signed prime replacement has
\(o(x\mathfrak S(N))\) total error, **even after summing
the absolute errors of the individual pinned-triple models**.
It does not assert a uniform tiny error for every fixed
tuple separately.

## 2. Uniform rough harmonic polynomials including the logarithm

Let
\[
 H_0^{(v)}(t)=\sum_{s\le x^t,\ P^-(s)>x^v}\frac1s,\qquad
 H_1^{(v)}(t)=\sum_{s\le x^t,\ P^-(s)>x^v}\frac{\log s}{s}.
\]
For \(t\in[.40,.60]\), \(\chi\le v\le w\), the needed
polynomials are
\[
 H_0^{(v)}(t)=c_0(t/v+1)+E,\qquad
 H_1^{(v)}(t)/L=c_0\bigl(t^2/(2v)-v/4\bigr)+E',
                                                                    \tag{5}
\]
where \(E,E'\) are \(o(\ell^{-B})\) for every fixed \(B\)
uniformly. The analogous signed moments are
\[
  \sum_{s\le x^t,\ P^-(s)>x^v}\frac{\mu(s)}s
        =o(\ell^{-B}),\qquad
  L^{-1}\!\sum_{s\le x^t,\ P^-(s)>x^v}
                    \frac{\mu(s)\log s}{s}=-e^\gamma v+o(\ell^{-B}).
                                                                    \tag{6}
\]
To see both uniformities, use the quantitative
prime-harmonic convolution and unit atom in
[the two signed sectors, §2](../completed_gap_two_true_sectors/Proof.md).
The error there saves every logarithmic power also with cutoff
\(x^v\ge z\) and with a single logarithmic slot.
For the signed harmonic the cumulative is \(\rho(t/v)\);
partial summation, the factorial tail and
\(\int\rho=e^\gamma\) give (6).

For the positive harmonic in units of \(\log(x^v)\),
write its measure as
\(E_1=\delta_0+\omega_{\rm ext}(u)\,du\), where
\(\omega_{\rm ext}=0\) below 1 and is the Buchstab function
above 1. This is the positive convolution exponential
\(\exp^*(1_{u>1}du/u)\).
The Buchstab error \(\omega_{\rm ext}(u)-c_0\) decays
exponentially; see the primary
[Hildebrand--Tenenbaum differential-difference paper](https://tenenb.perso.math.cnrs.fr/PPP/Diff-diff_eqns.pdf)
also cited in the [many-small renormalization](../direct_many_small_renormalization/Proof.md).
For clarity, its two moments needed here are determined
by the elementary Laplace expansion
\[
 \int e^{-\sigma u}dE_1(u)
 =\exp\left(\int_1^\infty e^{-\sigma u}\frac{du}{u}\right)
   = c_0\left(\sigma^{-1}+1+\sigma/4+O(\sigma^2)\right).
\]
Thus the finite signed exponential-tail measure
\(F=E_1-c_0\,du\) has total mass \(c_0\) and first moment
\(-c_0/4\); this follows by taking the value and derivative
at zero of its convergent Laplace transform, not by a
second-term Tauberian inference. Integrating up to \(t/v\)
gives (5) since \(t/v\gg\ell^{1/3}\).
The corresponding \(H_1/L\) multiplies the first moment
in these units by v. This includes the atom at 1 in \(H_0\)
and assigns it zero logarithmic weight in \(H_1\).

## 3. Eight true allocations and the surviving calibration

Under the genuine prime main from §1, the free harmonic
for fixed marks and allocation I, before the factor
\(V_N(x^v)/A\), is
\[
 \begin{split}
  (-1)^{|I|}\bigl[H_1^{(v)}(D_y-j)
                     -Lj H_0^{(v)}(D_y-j)\bigr]\\
   =(-1)^{|I|}\frac{c_0 L}{v}
       \bigl[\tfrac12 D_y^2-2D_y j+\tfrac32 j^2-vj-v^2/4\bigr]
           +L\,o(\ell^{-B}).                                    \tag{7}
 \end{split}
\]
All \(D_y-j\) remain in \([.40,.60]\) eventually, because
there are at most three actual marks each \(\le W\).
The term \(-Lj H_0\) in (7) is the actual logarithmic tag
weight of (4); ignoring it would change the calibration.
For three marks, \(j\) is the sum of their exponents selected
in the short leg, and the third alternating difference of
the quadratic in (7) vanishes exactly. Thus for every
pinned first triple its main cancels after summing the
eight actual allocations. In the raw main (6) gives the
same constant \((-1)^{|I|}e^\gamma vL\) per allocation
up to negligible tails; its sum cancels as well. Since
there is no prime y on this class, §1 proves (2) on summing
the absolute errors and the uniformly tiny tails.

For \(k=0,1,2\) the common \(v\) is w.
There is no proper \(\Lambda\) contribution when \(k>0\);
(6) gives raw normalization 1 on k=0 and 0 on k=1,2.
For k=0 the free polynomial in (7) at \(j=0\)
gives the first line of (3), using
\(L V_N(W)/\mathfrak S(N)=c_0/w+o(\ell^{-B})\).
For k=1 the alternating first difference at exponents
\(0,u=\log p/L\) in (7) is \(2D_yu-\tfrac32u^2+wu\),
with common factor \(c_0L/w\). Summing \(1/p\) over
the actual \(z<p\le W\) by prime Mertens with the
\(du/u\) density gives the second line of (3).
For k=2 the alternating second difference is
\(3u_1u_2\) times that same common factor, so the
actual \(p_1<p_2\) sum equals
\(\tfrac32 c_0^2 (1-\chi/w)^2+o(1)\).
For these PNT replacements one can also use
\(\sum_{z<p\le W}(\log p)/p=(w-\chi)L+O_A(L^{-A})\)
after harmless log powers, dropping the genuine
diagonal \(p_1=p_2\) at \(O(L^{O(1)}/z)\).
The shift from \(D_y\) to \(D_0\) is \(O(L^{-1})\),
negligible even in the largest term \(D_y^2/w^2\).
This proves (3), in particular with the full signed
k≥3 orientations included only through their zero main.

Summing (3) gives
\[
 F_0+F_1+F_2
      =c_0^2\bigl[D_0^2/(2w^2)+2D_0/w+3/2\bigr]+o(1)
      =Q_w(D_0)+o(1).
\]
Here \(\chi/w^2=o(1)\); the precise polynomial in (3)
also records the \(\chi\)-dependent terms.
For the second equality, in \(1/w\) scaled units the density
measure for \(Q\) is \(E_1*E_1\).
From \(E_1=c_0\,du+F\), the cumulative of its convolution
is a quadratic plus an exponentially small tail, using
\(\int dF=c_0\), \(\int u\,dF=-c_0/4\).
The quadratic terms are:
\(\tfrac12 c_0^2 t^2\) from the Lebesgue square;
\(2c_0^2t+\tfrac12c_0^2\) from the two cross terms; and
\(c_0^2\) from the full \(F*F\) mass.
This gives \(Q_w(D_0)\) as displayed. Independently the
all-completed harmonic with exactly this W and U gives
\(Q_w(D_0)+o(1)\) by the Mark--Dickman integral in
[wide-gap calibration, §3](../wide_gap_all_terminal/Proof.md):
retain \(D_0\) rather than moving to \(1/2\), and use
\(\chi/w^2=o(1)\) in its shift estimate.
Subtracting the short raw mean and keeping the actual
prime \(\Lambda\) term now proves (1).

## 4. Comparison on each true first-three family

For the fully completed score at the *same* W, the residual short
s above has genuine additional small product \(S=\prod_{p\mid s,p\le W}p\).
Its free factor in allocation I becomes exactly
\[
            (-1)^{|I|}\mu(S)(\log s-2\log S-Lj).
\]
Unlike (4) this depends on all the actual additional small factors
of s. It is still a fixed weight on the short factor s, bounded
by \(O(L)\), so the true prime progression argument of Section 1
applies unchanged to each actual first-three family.
There is no restriction on additional small factors of the
free b beyond its true lower cutoff r.

We verify that these changed free factors have the same
zero first-three harmonic to the precision of (2). Put
\(\nu_v=1_{u>v}du/u\) and retain \(w=\log W/L\).
On the squarefree r-rough residual short s the signed
prime coefficient is negative up to W and positive above it.
Its continuum cumulative \(A_{v,w}(t)\) is thus the cumulative
of \(\exp^*(-\nu_v+2\nu_w)\), i.e.
\[
 A_{v,w}(t)=\rho(t/v)
       +\int_0^t \rho(u/v)\,q_w(t-u)\,du ,
\]
where \(q_w\) is the positive density of the non-atomic part
of the \(Q_w\) measure. The exact mark for
\(\log s-2\log S\) is Lebesgue measure \(1_{u>v}du\)
times \(L\), by the genuine \(f^2\) identity.
Consequently the free logarithmic cumulative divided by L
is \(B_{v,w}(t)=\int_0^{t-v} A_{v,w}(u)\,du\).
Prime-harmonic stability with a log mark is as in Section 2;
moving the endpoint W just changes one of the signed prime intervals.

The density \(q_w(t)=2Q_w(t-w)/t\) for \(t>w\)
follows by marking a convolution slot with its exponent.
For \(t\) in any fixed compact positive interval near \(1/2\),
the quadratic law for \(Q_w\) from Section 3 therefore gives
\[
             q_w(t)=c_0^2(t/w^2+2/w)+o(\ell^{-B})
\]
for every fixed B. In the integral for \(A_{v,w}\),
split at any sufficiently small fixed positive u.
Below the split this affine law applies uniformly,
while beyond it the factorial tail of \(\rho(u/v)\)
beats every fixed power of \(1/\ell\), even after
the polynomially bounded \(w^{-1}\)-scale density factors.
Thus \(A_{v,w}(t)\) is affine in t, with coefficients
possibly depending on v,w, up to \(o(\ell^{-B})\)
uniformly on a fixed neighborhood of \(D_y\).
Its first integral \(B_{v,w}(t)\) is quadratic plus
the same size error there up to a common constant:
only its derivative \(A_{v,w}(t-v)\) is needed locally.
The three allocation exponents stay in this neighborhood.
The resulting normalized free weight
\((-1)^{|I|}[B_{v,w}(D_y-j)-jA_{v,w}(D_y-j)]\)
again has vanishing third difference of its quadratic part.
This is uniform in the actual pinned r and applies with the
same absolute harmonic and BV envelopes. Hence the fully
completed \(k\ge3\) score also satisfies (2). This adds
no pointwise equivalence or parity control: the adaptive
form makes only the **selected small-tag algebra** finite.

The argument halves neither an arbitrary prime
discrepancy nor an omitted large-rank sign.
It gives a true prime average with bounded **selected**
small cofactor rank, while total rank of the residual
W-rough partner can still grow. No upper or lower
bound of the needed new sign in that k=0 channel
is asserted here.
