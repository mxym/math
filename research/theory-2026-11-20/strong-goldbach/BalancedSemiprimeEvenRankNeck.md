# One-sided long centering puts every even rank into a true product neck

Retain the genuine balanced reflected semiprime profile of
[BalancedSemiprimeLongFreeDescent.md](BalancedSemiprimeLongFreeDescent.md),
with the same \(N=2x\), \(s\), \(m=ph=N-sq\), \(c=(1-\log_x s)/2\),
\(F_s(m)=-2\log p\), \(W_s(q)\ge0\), \(M_N\), and
\(|\log_x p-(c-\eta)|<w=\eta/1000\). In particular
\(sq\in(x/2,x]\), \((m,N)=1\), \(s,p,h\) are true primes, and
\(q\) is integral in an opened row. Fix \(0<\eta<.002\) before taking
\(x\to\infty\), and put
\[
 V=x^\eta,\qquad U=x^{c-4\eta},\qquad
 B=x^{c+5\eta},\qquad Z=q/B\in[\tfrac12 x^{c-5\eta},x^{c-5\eta}].
\tag{1}
\]
The integer cutoff \(U\) is understood as the real boundary in a
strict or nonstrict comparison, and both \(U,B\) depend on \(s\).

Define the new center by replacing only the reverse Möbius coefficient:
\[
 \mathcal C_s^\mu(q)=\frac1{\log q}
       \sum_{\substack{rk\mid q\\r>U,\ k>V}}
                        (\mu(r)-P_B(r))\Lambda(k),\qquad
 P_B(r)=-\sum_{tb=r,\ b>B}(\mu*\mu)(t).
\tag{2}
\]
**Theorem.** This entire artificial row equals the genuine prime-quotient
statistic:
\[
 \sum_{s,q}W_s(q)F_s(m)\mathcal C_s^\mu(q)
   =\sum_{s,q\ {\rm prime}}W_s(q)F_s(m)+O_{A,\eta}(xL^{-A})
\tag{3}
\]
for every fixed \(A>0\). It vanishes exactly whenever \(q\) has a prime
factor \(>B\). If \(q\) is \(V\)-smooth it vanishes except for the
proper-power exceptions described below.

Every \(q\) of exactly three distinct prime bases is **favorable**
against \(F_s(m)<0\), apart from a power-small set. For even
\(\omega(q)\), the exact formula (7) below is supported solely on a
near-half divisor neck, with no rank restriction. For any fixed
\(K\ge4\), the total **absolute** contribution of the even-rank
part \(2\le\omega(q)\le K\) satisfies
\[
 O_K\!\left(\eta\log^{K-1}(2/\eta)\,|\mathcal R(F)|\right)
                        +o_{\eta,K}(M_N).
\tag{4}
\]
Here \(\mathcal R(F)<0\) is exactly the reference of the preceding proof
and \(|\mathcal R(F)|\asymp wM_N\); the \(O_K\) constant is independent
of fixed \(\eta\). In particular (4) includes arbitrarily small prime
bases, not just polynomially rough \(q\).

## 1. Whole arithmetic exchange before imposing any rank mask

The short reverse identity, with \((U,V)\) in place of \((Y,Y)\)
in (4) of [BalancedSemiprimeRaisedSign.md](BalancedSemiprimeRaisedSign.md),
has every divisor modulus \(se\) with \(e\le UV=x^{c-3\eta}\).
The same literal \((e,s,1)\) dispersion applies, with the actual
residue \(N=2x\), short SW prime \(p\) and other factor \(h\).
The first two Lichtman 5.2 rails are \(\le-2\eta+O(w)\) and
\(1-2\eta+O(w)\), the remaining two \(<1.79,1.70\). All true
prime factors of \(m\) exceed \(\max(U,V)\). Keep the reduced
\(1/\phi(se)\) initially and remove the terms with \(s\mid e\)
in the **mean** at harmonic cost \(O(L^C/s)\), exactly as in
[BalancedSemiprimeRaisedSign.md](BalancedSemiprimeRaisedSign.md).
The overlap between \(r\le U\) and \(k=P^j\le V\) has
\(U/P\) polynomially long, so the uniform finite constant/log
\(\mu/\phi\) moments give the same \(+\mathcal R(F)\).
The predecessor's separation argument applies to the single
moving cutoff \(U\): a wrongly included short label is a
divisor of \(q\) in the relative \(O(L^{-A'})\) neighborhood of \(U\),
paid by fixing \(s\), counting such divisors and their multiples,
and then the same global weighted divisor moments.
Proper prime powers in \(\Lambda(q)/\log q\) remain power-small.

The difference made by centering \(\mu\) alone collapses exactly to
\[
  -\frac1{\log q}\sum_{\substack{a\mid q\\a<Z}}
                      (\mu*\Lambda_{>V})(a)
\tag{5}
\]
before summing rows: write the marked free factor as \(b>B\), let
\(a=q/b\), and sum \(\mu_2*1=\mu\) over its short complements.
Every such marked \(r\) is automatically \(>U\), and the literal
switch is \(m\equiv N\bmod s a\), \(b=(N-m)/(s a)\). Use the same
\((a,s,1)\) dispersion, now with first rail at most \(-4\eta+O(w)\).
The edge \(a<Z\) is paid by counting \(b\) approaching \(B\) in the
fine boxes, as in the preceding proof. Its harmonic main is
\(-\mathfrak S(Nsm)\) before the physical \(1/\log((N-m)/s)\);
indeed \(-\mu*\Lambda=\mu\log\) and the removed overlap
\(P^j\le V\) has both endpoints \(Z/P^j\) and \(Z/P^{j+1}\)
polynomially long. Removing \(s\mid a\) and replacing
\(\mathfrak S(Nsm)\) by \(\mathfrak S(Ns)\) incur power-small errors
as before. Thus (5) has whole main \(-\mathcal R(F)\).
The exact short and long means cancel with their signs. This proves
(3) with no constraint relating either kernel to the prime factorization
of \(q\) before its whole arithmetic exchange. No \(\Lambda\)-long
coefficient has been inserted.

## 2. Exact parity shift

If \(P>B\) is a true prime divisor of \(q\), it is simple because
\(B^2>q\), and \(q/P<Z<U\). If \(P\mid r\), all eligible marked
\(b>B\) in \(P_B(r)\) contain \(P\); summing their complements gives
\(-\sum_{t\mid r/P}\mu_2(t)=-\mu(r/P)=\mu(r)\). If \(P\nmid r\),
then \(r\le q/P<U\), impossible. This proves the giant-prime claim.

Put \(J=q/\operatorname{rad}(q)\) and discard \(J>x^\epsilon\),
where \(0<\epsilon<\min(\eta/100,.01/K)\) for (4).
For \(q\) so discarded, its full squareful divisor obtained by
taking all prime powers of exponent at least two exceeds \(x^\epsilon\).
The count of squareful integers at most \(T\) is \(O(T^{1/2})\),
by writing them as \(a^2 b^3\) with \(b\) squarefree. Therefore their
reciprocal tail beyond \(x^\epsilon\) is \(O(x^{-\epsilon/2})\).
At each fixed \(s\) find at most \(O((x/s)x^{-\epsilon/2})\)
exceptional \(q\). Formula (5), the original weight and Cauchy with
global divisor moments in \(sq,N-sq\) pay even all physical log and
divisor weights, giving a power-small total. On the retained set,
any repeated prime power in \(q\) is at most \(J^2\le x^{2\epsilon}<V\).
Thus only simple primes \(P>V\) contribute \(\Lambda_{>V}\);
in particular a \(V\)-smooth \(q\) contributes zero.

For retained \(q\) not already killed, exact (2), (5) and the complete
Möbius sum on \(q/P>1\) give
\[
 (\log q)\mathcal C_s^\mu(q)
   =-\sum_{\substack{P\mid q\\P>V}}\log P
               \sum_{\substack{d\mid\operatorname{rad}(q/P)\\
                                      Z/P\le d\le U}}\mu(d).
\tag{6}
\]
The inequality \(Z/P\le U\) always holds. If \(\omega(q)\) is even,
then \(\mu(\operatorname{rad}(q/P))=-1\). Complementing divisors in
this radical, which equals \(q/(J P)\), gives the exact strict
cut conversion
\[
 \sum_{d\mid\operatorname{rad}(q/P),\,d<Z/P}\mu(d)
       =-\sum_{d\mid\operatorname{rad}(q/P),\,d>B/J}\mu(d)
       =\sum_{d\mid\operatorname{rad}(q/P),\,d\le B/J}\mu(d).
\]
Since \(B/J>U\), this proves
\[
 (\log q)\mathcal C_s^\mu(q)
   = \sum_{\substack{P\mid q\\P>V}}\log P
       \sum_{\substack{d\mid\operatorname{rad}(q/P)\\ U<d\le B/J}}\mu(d).
\tag{7}
\]
For squarefree \(q\) one may also combine the outer sum at each \(d\)
as \(\log((q/d)_{>V})\), where the subscript retains only prime
factors \(>V\). Formula (7) is exact for all even ranks with the
same tiny-squareful exception, not a replacement by product density.

For \(\omega(q)=3\), each divisor sum in (6) is over \(\{1,a,b,ab\}\).
If \(Z/P\le1\), either \(ab\le U\) and all four enter, or a singleton
\(\le U\) cancels the positive 1. Indeed \(P\ge Z\) and both
\(a,b>U\) would give \(Pab>ZU^2>q\). If \(Z/P>1\), 1 is absent.
The only possible positive \(ab\) has both \(a,b\le U\), and at
least one is \(\ge Z/P\); otherwise
\(\operatorname{rad}(q)=Pab<Z^2/P<Z^2<q/J\).
Both strict inequalities \(ZU^2>q\) and \(Z^2<q/J\) follow directly
from (1) and \(J\le x^\epsilon\). In all cases the inner sum is
nonpositive. The coefficient \(\mathcal C_s^\mu(q)\) is therefore
nonnegative and \(F_s(m)\mathcal C_s^\mu(q)\le0\).
Rank one is either \(V\)-smooth, a prime already killed, or
in the discarded powers.

## 3. The actual even-rank population: a small-base toggle and reversed sieve

It suffices to majorize the absolute value of (7) at
\(\omega(q)\le K\); its coefficients are bounded by a constant
depending only on \(K\). Let \(\ell_0\) be the least prime base of
\(q\). If \(\ell_0>V\), use the full product neck of (7).
If \(\ell_0\le V\), it is not the selected \(P\) in (7).
Pair the divisors \(d'\) and \(\ell_0 d'\) for
\(d'\mid\operatorname{rad}(q)/(P\ell_0)\), so \(d'\) contains neither
selected base even when \(\ell_0\) is repeated in \(q\).
The literal complementary bits \(+\mu(d')\) and \(-\mu(d')\)
restrict to the two edges
\[
 U/\ell_0<d'\le U,\qquad B/(J\ell_0)<d'\le B/J.
\tag{8}
\]
The sign on each edge is irrelevant for an upper bound. These edge
intervals have log length \(\log\ell_0\); they are disjoint since
\(B/(JU)\gg\ell_0\). Both full neck and toggled neck put the
radical divisor \(d'\) (or \(d\) in the first case) and its physical
complement \(q/d'\) in exponent intervals
\([c-5\eta-o(1),c+5\eta+o(1)]\). Here \(P\) is outside the divisor.

Apply the actual reversed \(h\)-upper sieve of §3 of
[BalancedSemiprimeRaisedSign.md](BalancedSemiprimeRaisedSign.md):
\(n=sq\equiv N\bmod p e\), with \(z_h=x^{.035},D_h=x^{.070}\)
and the \((p,e,1)\) Lichtman slots. In this positive envelope one may
include nonunit supplied \(n\) against \(N\), still retaining \(p\nmid N\)
and omitting all primes of \(N\) from the sieve set. Some extra independence details
are needed for (7)–(8). At bounded rank, enumerate assignments of
prime labels to the divisor and its complement and enumerate the
full exponents of those labels (at most a power of \(L\)).
Before grouping take independent fine relative boxes on true prime
labels and on \(p\). Use the positive envelope obtained by admitting
boxes touching each necessary inequality (1), (7) or (8), and the
physical product bounds. Their log boundary widths enlarge by
\(o(1)\) in ordinary logarithms, including the powers \(O(L)\);
this is smaller than \(\log\ell_0\ge\log2\) for (8).
The support requires no signed arithmetic transfer at an edge:
the pointwise sieve majorant for \(h\) is nonnegative on all
enlarged tuples. Use the union with bounded labeled multiplicities
and sum errors with arbitrary log reserve.

Initially the two near-half sizes are for \(d'\) and \(q/d'\), but
one base may not appear in both independent groups. Assign every
full prime power to the group of its base. This moves a product
of at most \(J\le x^\epsilon\) and now makes the factorizations
independent. Start with the larger of the original two groups
(before attaching \(s\)), taking the two possible orientations.
Move its entire prime powers with base at most \(z_0\) into
the other group to meet the source's SW rough support. This
second product is \(\le J z_0^K=x^{\epsilon+o(1)}\).
All assignments and the base-\(z_0\) splits can be made on the
individual label boxes before grouping; the other group also
absorbs the true \(s\). The selected group has exponent between
\(c-2\epsilon-o(1)\) and \(c+5\eta+2\epsilon+o(1)\), and has a
true prime variable at least \(x^{.4/K}\) by its near-half size
and the bound on repeated parts. Its normalized coefficients are
\(O_K(1)\) by unique factorization at bounded rank and fixed powers.
A true macro prime gives the auxiliary-mask SW exactly as in the
raised-sign note by fixing the other labels, with \(.4/K\) in place
of \(.20\). The other group is polynomially long. In particular both
groups, not just their product, meet Proposition 5.2. Its first
rail is \(\le-\eta+w+2\epsilon+o(1)\); its second is
\(\le1-\alpha+10\eta+4\epsilon+.070+o(1)<.991+o(1)\).
The other rails are \(<1.51\) by the same substitutions.
The residue is the individual \(N=2x\), and slot3 is the unit dyad.

In the reduced mean the \(p\mid n\) case gives zero, and the
\((n,e)=1\) factor must be kept. The exact local omissions from
the sieve due to primes of \(n\) remove at most \(K\) odd primes,
since \(s>z_h\); their effect is \(\le 2^K\).
The nonnegative upper sieve mean is \(O_K(\mathfrak S(N)/L)\),
as in (11) of the raised-sign note before dropping the \(p\) mask.
This handles prime factors of \(q\) even below the sieve range and
coincidences with the moving outer \(p\) label.

For the available product mass at fixed \(s\), choose a true
polynomially large prime label in the divisor and another in its
complement. Such labels of exponent at least \(.4/K\) exist by the
near-half sizes (with slack by using any fixed slightly smaller
constant if necessary). In the toggled case the second can be
chosen different from \(\ell_0\), since deleting \(\ell_0\)'s full
power, of size at most \(VJ\), leaves a macro-sized group.
Both selected labels are simple since \(J\le x^\epsilon\) and
\(\epsilon<.01/K\). Fix all other labels. The first selected
prime has harmonic mass \(O_K(\eta)\) in the full neck, or
\(O_K(\log\ell_0/L)\) in (8), by its log interval length and ordinary
PNT (enlarge by an absolute log length if needed). The repeated
ratio \(J\) depends only on the other labels. The second selected
prime supplies the central prime count \(O_K(x/(s\,tL))\),
where \(t\) is the product of the fixed other labels including
the value of the first selected prime, by the uniform PNT upper.
Thus the fixed-\(s\) tuple bound is \(x/(sL)\) times the harmonic
factor just obtained and the sum of inverse powers of all remaining
prime labels. The powers cost at most \(2/\ell\) for each label
\(\ell\). If all labels exceed \(V\), the remaining harmonics are
\(O_K(\log^{K-2}(2/\eta))\) by Mertens. In the toggled case, at
fixed \(\ell_0\) the remaining \(K-3\) harmonics are at most
\(O_K((1+\log(L/\log\ell_0))^{K-3})\). On the shell
\(\eta2^{-j-1}<\log\ell_0/L\le\eta2^{-j}\) the \(\ell_0\) harmonic
is \(O(1)\), and its extra factor is \(\le\eta2^{-j}\).
The geometrically weighted sum is
\(O_K(\eta\log^{K-3}(2/\eta))\). For rank two the toggled
case is empty: (8) would require a near-half \(d'\) not using
either of the two prime labels, hence \(d'=1\).
All these bounds also apply over the union of outer boxes because
the corresponding log intervals enlarge by a bounded amount,
not by the number of boxes. This yields the weaker common bound
\(O_K(x\eta\log^{K-1}(2/\eta)/(sL))\) on supplied tuples.
Multiplying by \(O_K(\mathfrak S(N)/L)\), by the actual \(O(w)\)
outer-\(p\) harmonic per \(s\), and by the bounded \(s\) harmonic
gives the genuine upper count. Finally \(|F_s|\ll L\),
\(W_s\) is bounded, and the coefficients in (7)–(8) are bounded
at fixed \(K\). This proves (4).

## 4. The surviving obstruction

Already at rank five there is an open geometric adverse chamber.
With all five true prime factors of \(q\) near exponent \(2c/5\),
each divisor interval in (6) admits precisely the six two-prime
divisors of \(q/P\), no other ranks. At its center the lower
and upper exponents are \(3c/5-5\eta+o(1)\) and \(c-4\eta\);
the singleton, pair and triple exponents \(2c/5,4c/5,6c/5\)
have fixed margins relative to them. Thus \(\mathcal C_s^\mu(q)=-6\)
on a fixed small open chamber about this shape. This is a
pointwise obstruction to extending the rank-three sign, not a
lower bound for that family's population on each fixed shifted
prime equation. Unbounded ranks cannot be discarded using (4).
This representation changes the surviving profiles materially,
but it does not bound the whole signed statistic relative to the
reference, and it does not prove strong Goldbach.

## Comparison with nearby 2026 work

[Arneth's October 20 v1](https://zenodo.org/records/23504447) studies signed Vaughan reassembly and parity separation, and [Pham's October v1](https://www.preprints.org/manuscript/202610.3061) treats different reflected rough and signed-boundary comparisons. The present argument uses an actual one-sided centering at the stated reflected semiprime profile, not any general parity separation. Its analytic input is the same fixed-residue Lichtman theorem as in the preceding notes.
