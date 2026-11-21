# Actual small-base removal at odd rank, and the rank-five reverse-rail limit

Keep the genuine \(m=ph=N-sq\) profile, \(\mu\)-only center
\(\mathcal C_s^\mu\), and asymmetric cuts of
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md):
\[
  c=(1-\alpha)/2,\quad \alpha=\log_xs,\quad
  U=x^{c-4\eta},\quad V=x^\eta,\quad B=x^{c+5\eta},\quad Z=q/B .
\]
Both statements below are on that actual profile. The first is an
absolute count on part of the odd-rank residual; the second isolates
a precise failed analytic transfer on its genuinely remaining rough
rank-five cell. Neither is a signed estimate for that remaining cell.

## 1. The smallest-prime toggle works at odd as well as even rank

For any fixed integer \(K\ge4\) and \(\log 2/L\le\delta\le\eta\),
the actual opened contribution from \(2\le\omega(q)\le K\) and
\(P^-(q)\le x^\delta\) satisfies
\[
 \sum_{\substack{s,q\\2\le\omega(q)\le K\\P^-(q)\le x^\delta}}
      |W_s(q)F_s(N-sq)\mathcal C_s^\mu(q)|
 \ \ll_K \delta\log^{K-3}(2/\delta)\,|\mathcal R(F)|
                         + O_{A,\eta,K}(x L^{-A}).
\tag{1}
\]
The constant on the first term can be taken independent of \(\delta\)
and fixed \(\eta\) in the indicated range; \(A\) is arbitrary.
One may replace \(\omega(q)\le K\) by rank exactly \(k\), \(3\le k\le K\),
with log exponent \(k-3\). Rank two with a base \(\le V\) is zero
off the same power-small squareful exception. In particular rank
five with a base \(\le \exp(\sqrt L)\) has \(o(M_N)\) contribution
for any fixed \(\eta\), while no such claim is made for the
fully macroscopic rank-five cells.

Here is the new sign-sensitive support step before its absolute count.
As in §2 of the cited note, remove the power-small set
\(J=q/\operatorname{rad}(q)>x^\epsilon\), with
\(0<\epsilon<\min(\eta/100,.01/K)\).
Every eligible \(\Lambda_{>V}\) label in the remaining exact (6)
of that note is a simple prime \(P>V\).
Let \(\ell=P^-(q)\le x^\delta\). It cannot be the chosen \(P\).
Pair \(d\) and \(\ell d\) with \(d\mid\operatorname{rad}(q)/(P\ell)\)
inside that signed divisor interval. Put \(A_P=Z/P\).
The interval \([A_P,U]\) overlaps its translate under division
by \(\ell\), since \(A_P<U/\ell\), by \(Z<U\) and \(P>\ell\).
The literal change of the two indicator bits
\(1_{A_P\le d\le U}-1_{A_P\le\ell d\le U}\) is supported on
\[
       U/\ell<d\le U,\qquad
       Z/(P\ell)\le d<Z/P .
\tag{2}
\]
The signs are opposite on these strips. Crucially the second one is a
**physical** neck in the complementary product:
\[
                    B<q/(Pd)\le B\ell .
\tag{3}
\]
This strict/nonstrict conversion retains the true moving \(Z=q/B\),
not an independently frozen surrogate. Use the groups
\((d,q/d)\) for the first strip and \((Pd,q/(Pd))\) for the second.
Both groups in each strip have exponents in
\([c-6\eta-o(1),c+6\eta+o(1)]\).
They have a designated group with an independent log interval of
length exactly \(\log\ell\), conditional on \(s\) and \(\ell\).
There is no parity assumption in (2)–(3). If every prime factor
is \(\le V\), the centered row was already zero as in the cited note.

For the actual count use the same reversed \(h\) upper sieve, with
\(D_h=x^{.070},z_h=x^{.035}\) and literal \(n=sq\equiv N\bmod p e\).
We give the changes to §3 of the preceding proof. Assign prime
powers within a group to their full base to remove any cross-group
shared base, then move the \(z_0\)-small bases out of the SW group.
The size cost is at most \(x^{2\epsilon+o(1)}\) as before.
The intended SW group starts as the larger of the two physical
groups in (2) or (3), so after this adjustment it has exponent
\(\ge c-2\epsilon-o(1)\). The new upper exponent is
\(c+6\eta+2\epsilon+o(1)\). Thus the Lichtman Proposition 5.2
first rail retains \(-\eta+w+2\epsilon+o(1)\);
the second now retains
\(1-\alpha+12\eta+4\epsilon+.070+o(1)<.995+o(1)\).
The remaining rails are \(<1.52+o(1)\).
An independent true prime \(>x^{.4/K}\) in this group supplies the
auxiliary-mask SW, the other group remains polynomial, and slots are
\((p,e,1)\) at the actual \(N=2x\). Enumerating all ordered
independent prime-label boxes, including fixed repeated-power
exponents, involves a fixed power of \(L\). The simple threshold
tests in (2)–(3) may be covered outward using the pointwise
nonnegative upper-sieve envelope. Their log widths enlarge by \(o(1)\),
uniformly in \(\ell\) including \(\ell=3\). The local upper-sieve
mean is \(O_K(\mathfrak S(N)/L)\) exactly as before: retain
\((n,pe)=1\) until the upper evaluation, omitting at most \(K\)
core bases from its Euler product.

For the central supply select a simple polynomial-size prime in
each of the two groups (other than the fixed least base \(\ell\)).
This is possible since deleting \(\ell\)'s full power, of size
\(\le x^{\eta+\epsilon}\), still leaves each affected half group
macroscopic. Both selected primes can be required \(>x^{.4/K}\).
Fix the other labels. In the designated group the selected prime
has harmonic mass \(O_K(\log\ell/L)\) by (2)–(3), even after the
outer boxes; repetitions of other prime labels are fixed.
The other selected prime contributes \(O_K(x/(s t L))\) by ordinary
PNT, with \(t\) the product of its other fixed labels, including
the value of the designated-group prime. This is the actual
\(1/L\) factor, not an assumption that a sifted composite is prime.
Arbitrary geometric sums over repeated exponents of nonmarked
labels cost only \(\ll1/\ell'\) per prime base \(\ell'\).
The other \(k-3\) label harmonics at fixed least base \(\ell\)
are \(O_K((1+\log(L/\log\ell))^{k-3})\).
On the shell \(\delta2^{-j-1}<\log\ell/L\le\delta2^{-j}\),
the \(\ell\)-harmonic is \(O(1)\); multiplying by
\((\log\ell)/L\) and summing \(j\) gives
\(O_K(\delta\log^{k-3}(2/\delta))\).
These bounds apply to the union of admitted boxes, with bounded
label multiplicity, not once per box.
For \(k=2\) and \(\ell\le V\), the partner prime must exceed \(B\)
unless the number is power-exceptional, so (2)–(3) cannot survive.

Combine the tuple bound, the \(O(w)\) genuine \(p\)-harmonic per \(s\),
bounded \(s\)-harmonic and the reversed sieve mean.
Then use \(|F_s|\ll L\) and the \(O_K(1)\) pointwise multiplicity in
(2), since \(\log P/\log q\le1\). Uniform remainder follows by choosing
the source log reserve arbitrarily large and \(\epsilon,\eta,K\)
fixed; allowing \(\delta\) to shrink does not alter any source rail.
This proves (1).

## 2. Why this does not reach balanced \(h\)-Type II in the rest of rank five

In the open adverse rank-five chamber of the preceding note, take
all five q primes in exponent bands
\[
          \log_x r_i=(1-\alpha)/5+O(\sigma),\qquad
                              \sigma<10^{-4}.
\]
There \(\mathcal C_s^\mu=-6\) pointwise with a fixed margin.
To address it by opening the primality of the genuine reflected
quotient \(h\), its balanced branches have a divisor
\(e\asymp h^{1/2+o(1)}\). The direct switched congruence on the
actual input \(n=s r_1 r_2 r_3 r_4 r_5\) is \(n\equiv N\bmod p e\).
The following obstruction concerns specifically the independent
slot groupings in
[Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5),
even if \(e\) can be split into arbitrarily convenient independent
factors. Let \(\beta\) be its true short SW input exponent; that
group must be formed from a nonempty subset of the six true input
prime labels. Write \(v_i\) for the three modulus-slot exponents.

* The actual prime \(p\) of exponent \(c-\eta+O(w)\)
  cannot be in slot 2: the third rail is already
  \(\theta+\beta+v_1+5v_2+2v_3\ge
        7/32+5(.43-\eta-w)>2.35\).
* It cannot be in slot 3: the second rail would give
  \(\beta<1/2-(c-\eta-w)\le.073\), but a nonempty
  genuine input group here has exponent \(>.099\).
* In slot 1 it requires \(\beta>c-\eta-w>.427\)
  and the second rail requires \(\beta<1/2\).
  A subset of at most two q labels without \(s\) is too short;
  three or more q labels are too long even without \(s\).
  With \(s\), zero or one q label is also too short.
  The only possible independent group is **\(s\) times two q
  primes**, of exponent \(\beta=(2+3\alpha)/5+O(2\sigma)\).

Even granting all the splitting of \(e\), the first and second
rails bound its exponent by
\[
 \log_x e \ \le\ (\beta-\log_x p)+(1-2\beta)
      \ \le\ \frac{1-\alpha}{10}+\eta+w+2\sigma <.093 .
\tag{4}
\]
The actual balanced \(h\)-split requires
\(\log_x e=(1+\alpha)/4+\eta/2+O(w)+o(1)>.274\).
Thus no orientation of these slots reaches the necessary
balanced modulus. This is stronger than the failure of placing
all of \(e\) in slot 2, and it leaves valid direct upper-sieve
counting using small \(e\). As a pointwise observation, the
tests \(d\mid h\) for \(d\le x^{.093}\) give the same Boolean
values on true primes \(h\) and on semiprimes whose two factors
exceed \(x^{.093}\); the upper-sieve estimate alone cannot supply
a matching signed h-prime lower against the adverse rank-five
population. There is no assertion that other multi-variable
dispersion or a genuinely coupled arithmetic estimate cannot do so.

The determinant reformulation \(s q+ph=N\) with \(q\) prime
would require a real anisotropic rank-four all-prime slice.
The fixed-determinant affine-sieve bounds in
[Nevo–Sarnak, arXiv:0902.0692, Theorems 1.1–1.2](https://arxiv.org/pdf/0902.0692)
give an upper on prime points and a lower on almost-prime points,
not this lower. The prime-matrix density result recalled by
[Horesh–Nevo, arXiv:1707.04746, Theorem 1.1](https://arxiv.org/pdf/1707.04746)
starts at matrix size \(n=3\). Neither source supplies a uniform
moving-\(N\) lower or a signed estimate for the chamber above.
The actual rough rank-five balance remains open.

**Dated comparison.** [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) analyzes balanced five-factor coefficients in a prime-filter setting and leaves a conditional arithmetic compensation. The estimate here keeps the actual semiprime-reflection equation for the very-small-base subpopulation, then audits the permitted direct switched slot placements on the distinct fully rough cell. [Arneth XLIII, October 22](https://zenodo.org/records/23560521) supplies a different finite Bonferroni–Liouville conditional reduction. Neither comparison provides the missing signed estimate here.
