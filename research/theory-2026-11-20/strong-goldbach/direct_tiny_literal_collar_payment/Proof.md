# Literal even-rank collar payment with arbitrarily tiny factors

Use the same all-small-completed own-centered gap score and the literal
raw-pair and safe-pair weights \({\cal A}^{\rm raw}_y(d)\) and
\({\cal C}_y(b)\) from the
[literal collar payment](../direct_literal_collar_payment/Proof.md).
In particular, \(N=2x\) is even, \(L=\log x,\ \ell=\log L\),
\(J=xJ_0\) with fixed \(J_0\subset[1,3/2]\), \(P=N-y\),
\(C_y=y/x^{1-\epsilon}\) for a fixed \(0<\epsilon<.005\),
and the actual cutoffs are \(R_\pm(y)=\sqrt y\,x^{\pm\delta}\).
A prime divisor of \(y\) is small if it is \(<C_y\), macro otherwise.
Take
\[
 \ell^{-2}\le\chi\le\ell^{-1},\qquad W=x^\chi,\qquad
 0<\delta\ll\chi\log\ell,\qquad
 \theta_0=\ell^{-1/4},\qquad \theta=\ell^{-1/8}.
\]
Work only on squarefree \(W\)-rough \(y\) with literal
prime \(P=N-y\) and even total rank, \(\mu(y)=+1\).
No positive cutoff change of an unbounded-rank actual score is made.

For each short collar divisor \(R_-(y)<d<\sqrt y\), write
\(d=SM\) with its full actual small part \(S\).
An eligible deletion prime is an actual prime divisor of \(d\)
with exponent at least \(\theta\).
All macro primes are eligible for sufficiently large \(x\).
Consider the following actual negative literal raw-pair types:
- **A:** \(\mu(S)=+1\), and \(M\) has odd rank at least 3;
- **B:** \(\mu(S)=-1\), \(M\) has even rank at least 2, and
  \(S\) contains at least two eligible small primes.

Require in addition \(P^-(d)<x^{\theta_0}\).
This last restriction connects the theorem disjointly to the
earlier polynomial-minimum payment, and does not bound the number of
smaller primes on \(d\). The result is literally about the raw
\(-\log y\) contribution of each such short divisor; it is not
just its difference from an own-root score.

**Theorem.** There is a selection on each physical \(y\) of distinct
safe orientations \(b<R_-(y)\) with genuine positive gap weights
\({\cal C}_y(b)\), such that the sum of these weights together with
all covered \(-\log y\) raw pairs of A and B, tested against
the true \(\log P\), is at least
\[
       -o_{\epsilon,J_0}(x\mathfrak S(N)).
\]
Every selected \(b\) has \(P^-(b)<x^{\theta_0}\) and lies
\(x^\theta\) or more below the short divisor from which it is
made. Thus no receiver is a \(\theta_0\)-rough receiver of the
earlier literal payment or any raw receiver inside the collar.
No claim is made about other uses of the same positive terms:
in any joint score decomposition one can use each orientation
only once. The scalar calibration and all uncovered weights
remain in the original fixed-target ledger.

## 1. Local arithmetic and how many collisions can be afforded

If \(d\) is in A or B, \(\mu(d)=-1\), and its full
inside-collar raw pair is exactly \(-\log y\).
Choose as prospective receivers every \(b=d/p\) with
eligible \(p\mid d\), omitting any zero weights.
Each is truly safe since \(\theta>\delta\) eventually; it
still contains every original factor below \(x^{\theta_0}\).
At a safe \(b\) write \(b=S_bM_b\).
On the even-total-rank rows the exact gap score is
\[
       {\cal C}_y(b)
        =\begin{cases}
             2\mu(S_b)\log M_b,&\mu(M_b)=+1,\\
            -2\mu(S_b)\log S_b,&\mu(M_b)=-1 .
          \end{cases}                                       \tag{1}
\]
Deleting a macro prime in A therefore gives \(2\log(M/p)\);
deleting a small prime gives \(2\log(S/p)\).
Deleting a macro prime in B gives \(2\log S\);
deleting a small prime gives \(2\log M\).
These receivers are all nontrivial and positive whenever
counted.

On each \(y\) delete from use **every prospective receiver
shared by at least two originally covered short divisors**,
and use all the unshared ones remaining.
Thus no allocation is double-counted, and it is enough
to cover a given \(d\) after loss of *one* receiver unless it
belongs to a separately paid collision class.
Let \(U=\log S\), \(V=\log M\), \(r=\omega(M)\),
\(k=\#\{\text{eligible small primes in }S\}\), and let
\(T\) be the product of all ineligible small primes in \(S\).
Write \(t=\log T\).
We will pay separately the case \(t>(\epsilon/2)L\),
so for now \(0\le t\le(\epsilon/2)L\).

For A, the total macro receiver weight divided by 2
is \((r-1)V\), and the total eligible-small receiver
weight divided by 2 is
\[
                   kU-(U-t)=(k-1)U+t ,
\]
interpreted as zero if \(k=0\).
If at most one receiver is lost, the total remaining
weight divided by 2 is \(\ge U+V=\log d\), as follows.
- If \(k=0\), \(U=t\le\epsilon L/2\); even after
  losing macro \(p\) the remaining macro weight divided
  by 2 is \((r-2)V+\log p\), more than \(V+U\) by
  at least \(\epsilon L/2\).
- If \(k=1\) with unique eligible small \(p_0\),
  losing that receiver leaves \((r-1)V\ge2V\),
  while \(U\le (3\epsilon/2)L+O(1)<V\).
  Losing a macro \(p\) leaves excess above \(V+U\)
  of exactly \((r-3)V+\log p-\log p_0\).
  It is nonnegative because \(p\ge C_y>p_0\).
  With no receiver lost the inequality is strict by
  a fixed positive multiple of \(L\).
- If \(k\ge2\), losing a macro leaves \((r-2)V+\log p\)
  and the small weight is at least \(U\).
  Losing a small \(p_0\) leaves \((r-1)V\) and small
  weight at least \((k-2)U+t+\log p_0\).
  At \(k=2\) the remaining excess is at least
  \(V-\log p_1>0\) with the other eligible small \(p_1\);
  at \(k\ge3\) it is at least \(V\).
  These margins exceed the collar width for large \(x\).

Thus the full \(\log y\) debit in A is paid, except for a
possible shortfall \(<2\delta L\) in the case \(r=3,k=1\)
with a lost macro \(p\) obeying
\(\log p-\log p_0<\delta L\).
Such a \(p\) is necessarily in the true thin range
\([C_y,C_y x^\delta]\).
No assumption about the parity of the small labels in the
complement is used.

For B there are \(r\ge2\) macro receiver weights \(2U\)
and \(k\ge2\) eligible-small receiver weights \(2V\).
Losing at most one receiver leaves at least one of each
and an additional receiver of weight at least
\(2\min(U,V)\ge 2\theta L\).
That surplus exceeds the possible width
\(\log y-2\log d<2\delta L\).
This covers all of B with at most one collided receiver.

The exceptional short divisors with at least two
different collided receivers, the large-\(T\) short
divisors, and the explicitly described thin shortfall
will now be bounded on the real prime leg, uniformly.

## 2. A true upper when the remaining cofactor is long

We use the
[macro-collar mixed two-bank sieve](../direct_macro_collar_payment/Proof.md)
with the exponent \(\theta\), or a fixed positive multiple
of \(\theta\), in place of its moving minimum.
If a fixed actual \(W\)-rough unit \(H\) leaves
\(a=y/H\) a free interval of length \(\asymp x/H\gg x^\theta\),
then the number of \(W\)-rough \(a\) with actual prime
\(P=N-Ha\) is
\[
        \ll \frac{x}{H}\frac{\mathfrak S(N)}{\chi\theta L^2}.
                                                                  \tag{2}
\]
Indeed the small bank \(\le W\) sieves both forms, the
later bank up to \(x^{\theta/100}\) sieves the true
prime form, and the CRT floors at levels
\(x^{\theta/10},x^{\theta/20}\) are power-small relative
to the available \(x^\theta\) length. The first-bank
sieve parameter tends to infinity since \(\theta/\chi\to\infty\).
Its product contributes \(\mathfrak S(N)/(\chi L)^2\),
the second contributes \(O(\chi/\theta)\);
the actual primes dividing \(H\) change these bounds by
\(1+O(L/W)\), while \(N\)'s local root coincidences
remain in \(\mathfrak S(N)\).
If \(x/H\gg x^{\kappa}\) for any fixed \(\kappa>0\),
we can choose the second bank \(x^{\kappa/100}\),
and omit the factor \(\theta^{-1}\) in (2), with
constant depending on \(\kappa\).
All coefficients in this upper come from actual fixed
factors; dropping primality is not how the bound is
obtained.
Opposite primes dividing \(N\) cost \(x^{o(1)}\) and
cutoff equality costs \(x^{1/2+o(1)}\) with the fixed
divisor-moment weight, as in the literal collar payment.

For an actual true prime \(p\ge x^\theta\), over an
interval of exponent width \(\Delta\), ordinary prime
upper bounds give harmonic mass
\(O((\Delta+L^{-1})/\theta)\).
At \(p\ge x^\epsilon\) this becomes
\(O_\epsilon(\Delta+L^{-1})\).
The full prime harmonic mass between \(x^\theta\) and
\(2x\) is \(O(1+\log(1/\theta))\).
Any unrestricted positive \(W\)-rough cofactor
\(D\le2x\) has harmonic mass \(O(\chi^{-1})\) by
the positive Euler product.
These are the only harmonic envelopes below.

## 3. Paying the exceptions in actual arithmetic

**Large tiny product.**
An exponential tilt and the elementary prime harmonic
log bound give
\[
 \sum_{\substack{W<P^-(T),\,P^+(T)<x^\theta\\
                         \log T>(\epsilon/2)L}}
      \frac1T
       \ll \frac{\theta}{\chi}
                      e^{-\epsilon/(2\theta)} .
\]
Here \(T\) is squarefree; indeed weight each prime
by \(e^{\log p/(\theta L)}\) and compare its product
with the ordinary reciprocal-prime Euler product.
The ratio is \(O(1)\), since
\(\sum_{p<x^\theta}\log p/p\ll\theta L\).
The other prime factors of \(d\), all at least \(x^\theta\),
have harmonic product \(O(1/\theta)\).
With \(H=d\), \(a=y/d\) has polynomial length \(\gg\sqrt x\),
so (2) holds with the fixed-exponent option, without
\(\theta^{-1}\).
Multiplying the two logarithms of the true debit and
its opposite prime gives the bill
\[
       O_\epsilon(x\mathfrak S(N)\chi^{-2}
                       e^{-\epsilon/(2\theta)})=o(x\mathfrak S(N)).
\]

**Two collided receivers.**
For every such \(d\), choose witness pairs
\[
    b_i=d/p_i,\qquad b_i q_i\ne d\quad(i=1,2),
\]
where \(p_1\ne p_2\) are eligible deletion primes,
and \(b_iq_i\) is a competing genuine short collar divisor
of the same squarefree \(y\).
The \(q_i\) are true primes outside \(d\), as \(y\) is
squarefree and \(q_i\ne p_i\).
All are \(\ge x^\theta\), and \(q_i/p_i\in[x^{-\delta},x^\delta]\).
The two competing \(q_i\)'s may equal each other;
this is not omitted.
Choose one spare prime \(r_0\mid d\) distinct from both
\(p_i\)'s: in A use a macro prime (there are at least three),
and in B use any of its macro or eligible-small primes
(there are at least four in all).
It has \(r_0\ge x^\theta\).

Put \(H=d\prod_{q\in\{q_1,q_2\}}q\) with a shared
\(q\) included only once.
The product of the distinct \(q_i\)'s is at most
\[
                p_1p_2 x^{2\delta}
                      \le (d/r_0)x^{2\delta}.
\]
Thus \(H\) divides \(y\), and
\(x/H\gg r_0 x^{-2\delta}
\ge x^{(1-o(1))\theta}\),
using \(d^2<y\le1.5x\).
Apply (2) with \(\theta/2\) so the actual remaining quotient
is long. For A the spare prime is macro, so the fixed
exponent variant would also suffice.

There are *three* independent harmonic widths,
with no model assumption about pairs of primes:
1. If \(q_1\ne q_2\), keep \(p_1,p_2\) fixed and sum
   the two new distinct \(q_i\)'s in the two indicated
   logarithmic widths. If \(q_1=q_2\), keep that one
   common prime fixed and sum the independent
   \(p_1,p_2\) in those widths instead.
2. For either case, keep these now chosen four or three
   prime labels fixed and use the true \(d\)-collar
   \(d\in[x^{1/2-\delta},\sqrt{1.5x}]\) to sum
   the distinct spare prime \(r_0\).
   It has its own width \(\delta+O(L^{-1})\).
   This gate does not vary either of the first two
   widths, since \(r_0\notin\{p_1,p_2,q_1,q_2\}\).
3. All remaining unlabelled factors of \(d\) can be
   summed as one unrestricted \(W\)-rough factor,
   at harmonic cost \(O(1/\chi)\).
   The unfixed free-cofactor representation \(y=Ha\)
   uses exactly \(1/H\) in (2); there is no multiplicity
   loss from a shared \(q\).
   
Thus, with \(h=\delta+L^{-1}\), the fixed-factor harmonic
bill is
\(O(h^3(1+\log(1/\theta))^2/(\chi\theta^3))\)
before the true-prime count in (2).
We bound one full lost debit by \(O(L)\) and include
the genuine \(\log P=O(L)\).
The resulting bound for all discarded short divisors is
\[
 O_\epsilon\left(x\mathfrak S(N)
        \frac{h^3(1+\log(1/\theta))^2}{\chi^2\theta^4}\right)
                 =o_\epsilon(x\mathfrak S(N)).
\]
For our parameters, \(h^3/\chi^2\ll\chi(\log\ell)^3\)
and \(\theta^{-4}=\ell^{1/2}\).
The upper counts every possible collision witness,
so choosing a witness for each nonpayable original
\(d\) incurs no assumption about distribution of the
number of competing receivers.

**Thin shortfall in A.**
A possible unpaid width in A requires a macro prime
\(p\) in \([C_y,C_y x^\delta]\),
hence in \([x^\epsilon,1.5x^{\epsilon+\delta}]\).
It yields \(O_\epsilon(h)\) harmonic mass.
Fix this prime and all but one different macro prime
of \(d\); summing that distinct spare prime using
the \(d\)-collar yields a second \(O_\epsilon(h)\).
The remaining rough factors have harmonic cost \(O(1/\chi)\).
Use (2) with \(H=d\) at polynomial length \(\gg\sqrt x\)
(no \(\theta^{-1}\) factor).
The actual remaining debit is only \(O(\delta L)\),
so including the opposite \(\log P\) gives at most
\(O_\epsilon(x\mathfrak S(N)h^3/\chi^2)
=o(x\mathfrak S(N))\).

These three bills and the explicit nonoverlapping receiver
selection prove the result without removing any ordinary
composite factor or evaluating an unproved long prime
progression.
The open types include, in particular, one-macro-prime
debt and B with fewer than two eligible small labels,
as well as noncovered outside-collar weights.
