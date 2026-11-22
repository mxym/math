# Optimally rough composite rows for the Hurwitz mark on cubic Goldbach targets

For a coprime, odd, nonsquare pair of positive integers `a,b` with
$N=a+b\equiv0\pmod4$, consider the mark
$3H(ab)\equiv2\pmod4$. Here $H(D)$ counts **all** positive definite
binary-form classes of discriminant $-D$ with the usual Hurwitz weights.
A subset of actual prime pairs has this mark. It does not certify a prime
pair, not even after local division tests to a fixed constant times the
cube root of the target.

**Theorem.** For all large $Y$, there are
$\gg Y/(\log Y)^6$ distinct $n\asymp Y$ for which $N=4n^3$ has
both of the following:

* an actual representation as a sum of two primes;
* a different representation $N=a+b=p u^2+Qv^2$ where $p,Q,u,v$
  are four distinct odd primes, each $\asymp N^{1/3}$,
  $3H(ab)\equiv2\pmod4$, and the *primitive* class number
  $h(-ab)\equiv0\pmod4$.

The constants are absolute. Both displayed composite legs are themselves
of order $N$ and have no prime divisor smaller than $cN^{1/3}$ for
some fixed $c>0$. On a nonsquare composite with a nontrivial square
factor the exponent $1/3$ cannot be improved: it has at least three
prime factors counted with multiplicity. The genuine pair in the first
conclusion is not asserted to have the mark. We prove a rowwise
obstruction, not failure of Goldbach at any target or a barrier to other
global uses of class numbers.

## What the weights detect

The characterization of $3H(D)\bmod4$ for $D\equiv3\pmod4$
is already [Chen–Garvan, Theorem 2.5](https://arxiv.org/pdf/2010.14315).
In the coprime nonsquare rows considered here, their mark is equivalent to
the squarefree kernels of $a,b$ being distinct primes $p,Q$, with
$(Q/p)=-1$ and the exponents of these kernel primes on their own legs
each equal to 1 modulo 4. These primes are opposite modulo 4, so
quadratic reciprocity makes the symbol condition symmetric. In particular,
when both legs are primes the mark selects precisely their nonresidue case.

For contrast, use the primitive ring-class number. Write $-D_0$ for
the fundamental discriminant, $ab=D_0 f^2$. Here $D_0$ has at least
two different odd prime factors since both coprime legs are nonsquares,
so $D_0>4$ and there are no exceptional unit weights. Gauss genus theory
gives $2^{\omega(D_0)-1}\mid h(-D_0)$; for $D_0=pQ$ the Rédei
criterion gives $h(-D_0)\equiv2\pmod4$ exactly when $(Q/p)=-1$.
See [Sasaki, Propositions 1–2](https://doi.org/10.1017/nmj.2018.16),
or take the fundamental case of Chen–Garvan. The ring-class formula is
$$
 h(-D_0f^2)=h(-D_0)\prod_{r^e\parallel f}
    r^{e-1}(r-\chi_{-D_0}(r)).
$$
See [Beckwith–Raum–Richter, Hurwitz class number formula](https://doi.org/10.1073/pnas.2005984117).
A conductor prime outside $D_0$ gives an even factor, whereas one in
$D_0$ gives an odd factor. Hence in these rows $h(-ab)\equiv2\pmod4$
selects exactly two odd prime powers, one on each leg, of odd exponent,
with nonresidue kernel primes. Removing the higher powers from
this latter test requires checking only odd exponents at least 3.
There are $O(N^{1/3})$ candidate bases and powers in total: the cubic
contribution is $O(N^{1/3})$, larger odd exponents contribute
$O(N^{1/5}\log N)$. This is an exact distinction, not an efficient
evaluation of the primitive class sum.

## A cube and a forced symbol change

Take
$$
 Y<p<1.01Y,\quad 4Y<q<4.1Y,\qquad p\equiv3, q\equiv5\pmod8.
$$
Require all seven forms
$$
 p, q, q'=2q+p,\quad (3q-p)/4, (q-3p)/4,\quad
 (3q+p)/2, (q-p)/2
$$
to be prime. There are $\gg Y^2/(\log Y)^7$ such integer pairs by
[Green–Tao's linear equations theorem](https://annals.math.princeton.edu/2010/171-3/p08)
and the [Green–Tao–Ziegler completion for finite complexity](https://arxiv.org/abs/1009.3998).
Indeed put $p=8x+3,q=8y+5$; the resulting affine forms are integral,
all odd, and their seven rational linear parts have distinct projective
directions. At any odd local prime one may choose $p=1,q=-1$ in the
residue field, since 8 is a unit: all seven values are then $1$ or
$-1$. Local densities are positive and outside finitely many primes
their normalized factors are $1+O(\ell^{-2})$ by pairwise independence.
The box has positive scaled area, all values are positive and comparable
with $Y$. Proper prime powers among von Mangoldt contributions cost
$O(Y^{3/2}(\log Y)^{O(1)})$ since fixing one form leaves $O(Y)$
points.

Exactly one of $Q=q,q'$ has $(Q/p)=-1$, since
$q'\equiv2q\pmod p$ and $(2/p)=-1$. For that choice set
$$
 n=(p+Q)/4,\quad u=(3Q-p)/4,\quad v=(Q-3p)/4.
$$
Both choices give $Q\equiv5\pmod8$, and $u,v$ are the last four
prime forms in the appropriate pair. For $Q=q$, measured in units
$Y$, $(u,v)$ lie in $(2.74,2.83)\times(0.24,0.28)$; for $Q=q'$,
they lie in $(6.49,6.66)\times(1.49,1.56)$. These intervals and
the ones for $p,Q$ are disjoint **within each candidate**. Thus no
kernel prime divides either conductor, $a,b$ are coprime, and
$$
 p(3Q-p)^2+Q(Q-3p)^2=(p+Q)^3,\qquad a+b=4n^3.
$$
The conductor is $uv$. The primitive class of full discriminant has
even extra factors, hence vanishes modulo 4; in the sum
$H(ab)=\sum_{d\mid uv}h(-pQd^2)$ only the fundamental term is
nonzero modulo 4. Any test restricted to conductor primes
$r\le cN^{1/3}$, for sufficiently small fixed $c$, removes no term.
Nor can trial division of the individual legs up to that bound discard
this row.

For a fixed $n$ and fixed $p$ there are at most two original $q$:
one from $p+q=4n$, the other from $2(p+q)=4n$. There are
$O(Y/\log Y)$ possible primes $p$. Thus the tuples give at least
$\gg Y/(\log Y)^6$ distinct $n$. Finally
[Perelli, *Goldbach numbers represented by polynomials*, Corollary 1](https://content.ems.press/assets/public/full-texts/serials/rmi/12/2/5197/online/10.4171-rmi-205.pdf)
applied to $F(n)=4n^3$ leaves $O_A(Y/(\log Y)^A)$ unrepresented
indices in this fixed union of dyadic-scale intervals, for every $A$.
Indeed the even-target singular series is bounded below, and the
proper-prime-power contribution to the weighted count per target is
$O(\sqrt N(\log N)^3)$. Taking $A>6$ proves coexistence.
No stronger recent exceptional-set exponent is used.

Related but different: [Dominguez–Miller–Wong](https://arxiv.org/abs/1211.2605)
used actual prime pairs at polynomial targets and class-group criteria
to produce cyclic 2-class groups. Our construction instead distinguishes
the imprimitive local mark from actual primality. It cannot convert a
positive or nonzero Hurwitz trace into a genuine binary representation.
