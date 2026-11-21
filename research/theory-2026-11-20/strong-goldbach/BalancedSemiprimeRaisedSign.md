# Raised reverse cut: one-sided support on genuine reflected semiprimes

Use the notation of [BalancedSemiprimeLongFreeDescent.md](BalancedSemiprimeLongFreeDescent.md):
\(N=2x\), \(L=\log x\), \(sq\in(x/2,x]\), \(m=N-sq\), with the genuine
prime \(x^{.10}<s<x^{.14}\) and \((m,N)=1\). Put \(\alpha=\log_x s\),
\(c=(1-\alpha)/2\), and \(F_s(m)=-2\log p\) on the actual semiprimes
\(m=ph\) with \(|\log_x p-(c-\eta)|<w=\eta/1000\), zero elsewhere.
Fix \(0<\eta<.002\) **before** taking \(x\to\infty\).
Keep \(B=B(s)=x^{c+2\eta}\), \(Z=Z_s(q)=q/B\), and the exact \(W_s(q)\ge0\)
and negative reference \(\mathcal R(F)\) of that note, with
\(|\mathcal R(F)|\asymp w M_N\).
Now use the equal **sharp** reverse cuts
\[
                       Y=Y_s=x^{c/2-3\eta/4}.
\tag{1}
\]
Write \(\mathcal B_Y(q)=(\log q)^{-1}\sum_{rk\mid q,\ r,k>Y}\mu(r)\Lambda(k)\).
Define \(\mathcal C_s(q)\) by replacing \(\mu(r),\Lambda(k)\) in this expression
by \(\mu(r)-P_B(r),\Lambda(k)-H_B(k)\), the same long-free centered
coefficients as in the preceding note.

**Theorem.** For every fixed \(D>0\), uniformly at the individual target,
\[
 \sum_{s,q\ {\rm prime}} W_s(q) F_s(m)
     =\sum_{s,q} W_s(q) F_s(m)\mathcal C_s(q)+O_{D,\eta}(xL^{-D}).
\tag{2}
\]
Every \(q\) with a prime factor \(>B\) has \(\mathcal C_s(q)=0\), regardless
of rank. Restrict the centered sum to integers with at most two distinct
prime bases \(\le Y\). Its **signed upper bound** is
\[
       O\!\left(\eta\log^2(2/\eta)\,|\mathcal R(F)|\right)+o_\eta(M_N)
\tag{3}
\]
with an absolute first constant. With no small prime base the adverse
part is confined to the old balanced rank-two neck of width \(O(\eta)\).
With exactly one small prime base there is no adverse part outside a
power-small exception. The complement not bounded by (3) has at least
three distinct small prime bases and no prime \(>B\).

## 1. Whole equal-cut exchange

At \(q>Y\), the exact short identity is
\[
 \Lambda(q)-(\log q)\mathcal B_Y(q)
     = \sum_{r\mid q,\,r\le Y}\mu(r)\log(q/r)
       -\sum_{rk\mid q,\,r,k\le Y}\mu(r)\Lambda(k).
\tag{4}
\]
Both short divisors \(e=r,rk\) satisfy \(e\le Y^2=x^{c-3\eta/2}\).
Use [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5)
in the literal \((e,s,1)\) orientation of §2 of the preceding note. The
SW factor is the true \(p\) of exponent \(c-\eta+O(w)\), with the
other polynomially long true factor \(h\), and the actual residue is \(N=2x\).
The first rail at the upper cutoff is \(-\eta/2+O(w)\), the second
\(1-2\eta+O(w)\), the last two \(<1.79\) and \(<1.70\).
The unit slot uses the dyad \((1/2,1]\). The coefficient on \(e\) is
\(O(L)\) by \(\sum_{d\mid e}\Lambda(d)=\log e\); first freeze \(Y_s\)
in a fine \(s\)-interval and only then form the coefficient on \(e\).

For separation use disjoint relative \(O(L^{-K})\) boxes in \(s,p,h\)
and the central variable as in the preceding note. Freezing \(Y_s\)
can change only divisors \(r\) or \(k\) of the actual \(q\) in an
\(O(L^{-K})\) relative edge of \(Y_s\). At fixed \(s\) there are
\(O(Y_sL^{-K}+1)\) such candidate integers, each dividing at most
\(O(x/(sY_s)+1)\) physical \(q\). Summing over \(s\) costs
\(O(xL^{1-K}+x^{1-\min\log_xY_s+o(1)}
              +x^{.14+\max\log_xY_s+o(1)})\).
The physical log/divisor weights are paid by Cauchy and global divisor
moments on \(sq,N-sq\). In the reduced means a changed interval costs
its harmonic width \(O(L^C(L^{-K}+1/Y_s))\) after the other labels.
The moving edge \(p s^{1/2}=x^{1/2-\eta\pm w}\), the central edges, and
the exact varying \(W_s(q)/\log q\) have the same separation and power
or arbitrary-log errors as in §2 of the preceding note.

The actual modulus is \(se\), with \((se,N)=1\); the reduced mean
additionally has \((m,se)=1\). True factors of \(m\) exceed \(Y\), hence
\((m,e)=1\). Retain \(1/\phi(se)\) first. Terms with \(s\mid e\) are
power-small in the reduced mean by \(O(L^C/s)\) in the inner harmonic
sum, since \(\phi(s)\phi(e)/\phi(se)\le1\). Keep \((m,s)=1\).
The uniform finite harmonic evaluation in the proof of (3) of
[CompensationNeutrality.md](CompensationNeutrality.md) now applies
with \(U=Y=Y_s\); all its short endpoints remain polynomially long,
splitting each overlap \(p_0\le\sqrt Y\) and bounding larger \(p_0\)
by \(O(L^C/p_0^2)\). It gives \(+\mathcal R(F)\) for (4).
Proper prime powers cost only a power-small error, by their
\(O((x/s)^{1/2}L^C)\) count at fixed \(s\) and the same divisor moments.

For the long-free difference the exact collapse of §1 of the preceding
note remains valid:
\[
 \mathcal B_Y(q)-\mathcal C_s(q)
   =\frac{1}{\log q}\sum_{a\mid q,\,a<Z}\mathcal L_Y(a,q/a),\qquad
 \mathcal L_Y(a,b)=-(\mu*\Lambda_{>Y})(a)
        +\mu_{>Y}(a)\log b-(\mu_{>Y}*\Lambda)(a).
\tag{5}
\]
Here \(\mu_{>Y}(a)=\mu(a)1_{a>Y}\) and likewise for \(\Lambda_{>Y}\).
Only one long-free factor can occur since \(B^2>q\); a marked \(r\) or
\(k\) is automatically \(>Y\). The \((a,s,1)\) dispersion of that note
applies for every \(a<Z\), with first rail at most \(-\eta+O(w)\).
The sharp \(r,k\) edges are paid as in (4), since the factors are divisors
of the actual \(q\); pay the \(a<Z\) edge by counting the true switched
free \(b\) near \(B\). In the mean the same \(s\mid a\) removal is
power-small. At fixed \(s,m\) put \(Q=(N-m)/s\) and \(E=Nsm\); the
inner harmonic sum is
\[
 \sum_{\substack{a<Z_s(Q)\\(a,E)=1}}
             \frac{\mathcal L_Y(a,Q/a)}{\phi(a)}
                       =-\mathfrak S(E)+O_{D,\eta}(L^{-D}).
\tag{6}
\]
Here is the check specific to the new higher \(Y\). In the first
term of (5) remove from the full convolution the part with
\(k=p_0^j\le Y\). The nonoverlap endpoint \(Z/k\) is polynomially
long. The overlap endpoint \(Z/(k p_0)\) is also polynomially
long for \(p_0\le x^{.01}\), since \(Z/Y\) has exponent
\(c/2-5\eta/4+o(1)>.20\). Larger \(p_0\) have absolute overlap
\(O(L^C/p_0^2)\) times \(\Lambda(p_0^j)/\phi(p_0^j)\).
The middle term is the difference of the finite constant and log
moments at \(Z,Y\). In the third term the full moment equals the
truncated \(r\le Y\) moment: \(Z/r\) is polynomially long, and
the local correction \(-\log p_0/(p_0-1)^2\) for \(p_0\mid r\)
uses the constant \(\mu/\phi\) moment at \(Y/p_0\), splitting at
\(\sqrt Y\). These are the exact finite moments of §2 of the
preceding note, also the Goldston–Yıldırım moments quoted in
[Huang–Li, Lemma 1](https://huixil.wordpress.com/wp-content/uploads/2019/10/on-a-variant-of-the-elliott-halberstam-conjecture-and-the-goldbach-conjecture.pdf).
Consequently (5) has whole main \(-\mathcal R(F)\), including the
same **physical** \(1/\log Q\) and \(q\)-test. Summing with (4)
proves (2); one cannot discard either nonzero main separately.

## 2. Exact sign identities

Throughout the central interval,
\[
 Y^2>Z,\quad q/Y^2<B,\quad B^2>q,\quad Z^2Y>q,\quad
 \Delta=\log(B/Z)=4\eta L+O(1).
\tag{7}
\]
If \(P>B\) is prime and divides \(q=P t\), then \(P^2>q\) and
\(t<Z\). The centered \(\mu,\Lambda\) coefficients vanish on every
\(r\) or \(k\) containing \(P\): eligible long free divisors are
exactly those containing \(P\), and summing their complementary
divisors recovers the original coefficient by the identities of §1
of the preceding note. Thus \(P\) must lie in the intact original
free slot, leaving a factorization of \(t<Z<Y^2\) with \(r,k>Y\),
which is impossible.

Discard every \(q\) divisible by \(p_0^j>x^\epsilon\) for prime \(p_0\),
\(j\ge2\), where \(\epsilon=\eta/100\). At fixed \(s\) their count is
\(\ll (x/s)x^{-\epsilon/2}L^C\), by the reciprocal \(p_0^j\) sum
(split for each \(j=2,\ldots,O(L)\) at \(x^{\epsilon/j}\) and sum
over integer bases). Global divisor moments pay the weights because
\(\mathcal C_s(q)\ll\tau(q)^C L^C\) by (5). The aggregate loss is
power-small. All primes \(>Y\) in \(q\) are now simple and every
full small-base power is \(\le Y\).

Write \(q=zV\), \(V=\prod_{i=1}^j b_i\), where \(z\) is the full core
with bases \(\le Y\), and \(Y<b_1<\cdots<b_j\le B\).
Necessarily \(j\le4\). For \(z=1\), actual prime \(q\) has already
been eliminated. For \(j\ge2\) the original \(\mathcal B_Y=-1\)
by the complete Möbius sum for each fixed \(k=b_i\).
In (5) only singleton large primes \(a=b_i<Z\) contribute,
with \(\mathcal L_Y=-\log q\) each. Thus
\[
                     \mathcal C_s(q)=\#\{i:b_i<Z\}-1.
\tag{8}
\]
If \(j\ge3\) then at most one \(b_i\ge Z\) by \(Z^2Y>q\), so this
is favorable against \(F_s(m)<0\). If \(j=2\), both \(b_i\ge Z\)
because each is \(\le B\), and the coefficient is \(-1\).

For \(1<z<Z\) there is the exact formula
\[
 \mathcal C_s(q)=\sum_{\substack{P\mid V\\P<Z}} S_z(Z/P),\qquad
                   S_z(t)=\sum_{\substack{d\mid z\\d<t}}\mu(d),
\tag{9}
\]
where \(P\) runs over prime labels. Indeed all the original
\(k>Y\) with nonzero \(\Lambda(k)\) are singletons of \(V\).
For each \(k\), the sum over \(r\) involving a large prime
has a complete \(\sum_{d\mid z}\mu(d)=0\).
The original weight is therefore \(R_Y(z)\log V/\log q\) with
\(R_Y(z)=\sum_{d\mid z,\,d>Y}\mu(d)\). All-small divisors enter
(5) in full, their first convolution vanishes, and their other terms
combine exactly to \(R_Y(z)\log V\) before division by \(\log q\).
Every other short divisor is \(Pd<Z\) with \(d\mid z,d<Y\).
Its coefficient is \(-\mu(d)\log q\): the first term contributes
\(-\mu(d)\log P\), the explicit log \(-\mu(d)\log(q/(Pd))\),
and the rest \((\mu*\Lambda)(d)=-\mu(d)\log d\).
This proves (9). For one small base the full core is \(\le Y<Z\)
and \(S_z\) takes values only 0 and 1.

For two small bases let \(z=u^i v^k\) with primes \(u<v\le Y\),
\(A=\log u\), \(C=\log v\), and \(E_0=\log(z/(uv))\le2\epsilon L\).
The values of \(S_z(e^\ell)\) are \(+1\) on \(0<\ell\le A\), \(-1\)
on \(C<\ell\le A+C\), and 0 elsewhere.
If \(z\ge Z\), each full small power lies in \([Z/Y,Y]\). Both
are true simple primes (by the exception removed above), in bands of
exponent width \(O(\eta)\), and the two groups \(z,q/z\) lie
in \([Z,B]\). The complement \(q/z\) consists of one or two
large primes. The bounded-rank coefficient (5) is \(O(1)\)
after division by \(\log q\); no sign is needed for this case.

If \(z<Z\), then \(j\ge2\) since no prime can exceed \(B\).
Adversity in (9) requires at least one \(P\) with
\(C<\ell=\log(Z/P)\le A+C\), giving \(Pz\ge Z\).
For \(j\ge3\) we have \(V/P>Y^2\), so \(Pz<q/Y^2<B\).
For \(j=2\), write \(P'\) for the other prime. Its
\(\ell'=\log(Z/P')=A+C+E_0-\Delta-\ell<A\), since \(\Delta>E_0\).
Its term is favorable unless \(\ell'\le0\); if the total is
negative then \(P'\ge Z\), equivalently \(Pz\le B\).
In either case every adverse core admits a true marked \(P\) satisfying
\[
              Pz,\ V/P\in[Z,B],\qquad {Z}/{(uv)}\le P<Z/v.
\tag{10}
\]
The multiplicity of these marks and the coefficient in (9) are
bounded by 4. At fixed \(s,z\) put \(Z_0=(x/s)/B\) and use
\(Z\in[Z_0/2,Z_0]\). The allowed \(P\) is in the intersection of
\([Z_0/(2z),B/z]\) and \([Z_0/(2uv),Z_0/v]\), of log length at most
\(\min(4\eta L+O(1),\log u+O(1))\).

## 3. A genuine reversed neck count, including small local factors

For each adverse sector use its two complementary near-half groups:
the two q primes in (8) of rank two, \(z,q/z\) in the two-core case
\(z\ge Z\), and (10) otherwise. Upper-sieve the **actual** prime
\(h=(N-sq)/p\) at \(z_h=x^{.035}\), with level \(D_h=x^{.070}\),
using ordinary dimension-one Rosser upper weights \(\lambda_e^+\)
with sieve primes prime to \(N\). The congruence is the literal
\(n=sq\equiv N\bmod pe\). The pointwise envelope on integer \(h\)
is nonnegative and majorizes actual prime \(h\).

Before grouping, take independent relative \(O(L^{-K})\) boxes
on the individual prime labels and the true modulus label \(p\).
Fixed powers \(i,k\) are dealt with separately, at most \(O(L^2)\)
possibilities. Very small labels may be fixed in singletons up to
\(L^{2K}\). Use the explicit necessary positive envelope just
derived (and the central product band); admit boxes touching the
inequalities. This outer cover can be used because the upper-sieve
envelope was pointwise nonnegative. With \(s\) near its midpoint,
the two near-half groups are explicitly grouped **after** these
tests; use one of size at least \((x/(2s))^{1/2}\) as the intended
short SW slot, taking both possible orientations if needed. The
tests, such as the two explicit \(P\) intervals after (10), involve
only finite products or powers (and \(i,k=O(L)\)); their log
widths enlarge by \(O(L^{1-K})\), preserving the bound
\(O(\min(\log u,\eta L))\) since \(\log u\ge\log2\).
Likewise the \(s,p\) exponent band retains width \(2w+o(1)\),
and \(n\) stays in the central band up to a vanishing relative
extension. One never inserts a coupled mask into the theorem
after independent grouping. The box count is a fixed log power.

The SW slot in Lichtman 5.2 requires **all** its prime factors \(>z_0\),
where \(z_0=x^{1/(\log\log x)^3}\). Move any full small-base powers whose
base is \(\le z_0\) from the selected group to its complement, before
grouping. Their total size is at most \(x^{2\epsilon+o(1)}\) because a
repeated power after the exception is \(\le x^\epsilon\).
Split label boxes at this independent cutoff. The selected group
still contains an actual prime of size at least \(x^{.20}\):
in (10) this is \(P\) or a complementary large prime; in \(z\ge Z\)
both core labels are already macroscopic. Thus its exponent is
between \(c-2\epsilon-o(1)\) and \(c+2\eta+o(1)\), and the other
group absorbs both the moved labels and true \(s\).

Each grouped coefficient is \(O(1)\) in a fixed box, by unique prime
factorization and the bounded number of label assignments with fixed
power exponents (also if \(s\) equals a core prime). For the precise
auxiliary-mask SW of the selected group (Lichtman (2.2)), fix its
other labels and use PNT in small reduced progressions on a true
macro prime, with any independent prefixes. If its fixed cofactor
is not a unit modulo the tested modulus, both reduced sums vanish;
otherwise reduce by its inverse. For the auxiliary mask \(d\),
discarding the macro primes dividing \(d\) costs at most \(\tau(d)\)
per fixed tuple of other labels, of which there are
\(O(X_1x^{-.20}L^C)\) at group scale \(X_1\).
(The elementary fixed-factor count follows from
\(\sum_{j\le T}\tau_b(j)\ll T(1+\log T)^{b-1}\), counting power labels
as integral factors.) For progression moduli \(>\log^A x\), the
bounded group coefficient and integer count \(O(X_1/q_0+1)\),
where \(q_0\) is the tested modulus, give the required estimate
with a sufficiently large log threshold. The coprime reduced mean
has the same bound after the usual \(\phi(q_0)\) log loss.
Thus SW holds with arbitrary log reserve. Further dyad partitions
and log normalizations are harmless.

Now apply Proposition 5.2 with slots \((p,e,1)\) and actual residue
\(N\). The first rail is \(\le-\eta+w+2\epsilon+o(1)<-.97\eta+o(1)\);
the second \(\le1-\alpha+4\eta+.070+o(1)<.979+o(1)\).
The last two are \(<1.50+o(1)\) by substituting
\(v_1\le c-\eta+w\), \(v_2\le.070\), \(v_3=0\),
\(c-2\epsilon-o(1)\le\log_x X_1\le c+2\eta+o(1)\),
and \(\theta=7/32\). Both input lengths are polynomial.
Use again the unit dyad \((1/2,1]\). The discrepancy is
\(O_{D,\eta}(xL^{-D})\), including all independent boxes.
No factorability of \(p\) or of the actual shape tests is assumed.

The true reduced mean is supported on \((n,pe)=1\).
If \(p\mid n\) it is zero (the actual class is also impossible,
because \(p\nmid N\)); keep this mask until after evaluating the
nonnegative main bound. Since \(p>z_h\), \(\phi(pe)=\phi(p)\phi(e)\).
At fixed \(n\), all sieve primes fail to divide \(n\) except possibly
the two core bases. The exact restricted mean factor satisfies
\[
            0\le \sum_{(e,n)=1}\frac{\lambda_e^+}{\phi(e)}
                      \ll \frac{\mathfrak S(N)}{L}.
\tag{11}
\]
Indeed these Rosser upper coefficients restricted to divisors of a
subset of sieve primes are the same Rosser upper coefficients for
that set, by their ordered-prime definition. Apply the upper
dimension-one evaluation for \(g(\ell)=1/(\ell-1)\) on the sieve
set with primes dividing \(N\) or the core omitted
(see the definitions and evaluation in
[Kumchev–Tolev, §4.2](https://prime.sdu.edu.cn/__local/3/07/0F/32C1A34A2B081008AF70E53CBBB_B422122B_9C4B8.pdf)).
Those at most two extra omissions are odd primes and cost at most
fourfold in the Mertens product. Nonnegativity also follows by testing
the pointwise upper sieve against the independent Bernoulli
measure with the displayed local probabilities. In particular
dropping \((e,n)=1\) from the alternating sum without this argument
would not be justified. Once (11) is used, dropping the \(p\)-unit
mask can only enlarge the resulting positive envelope.

In the \(z<Z\) two-core case, at fixed \(s,u,v,i,k\), the true
marked prime \(P\ge Y\) has harmonic mass
\(O(\min(\log u/L,\eta))\), by (10) and the ordinary PNT upper:
enlargement of the log interval by an absolute amount is harmless.
Use at least one other large true prime to obtain \(x/(s z P L)\)
from the central product constraint after summing the remaining
macro harmonics \(O(1)\). The resulting available tuple count at
fixed \(s\) is
\[
 \ll\frac{x}{sL}\sum_{u<v\le Y}\frac{\min(\log u/L,\eta)}{uv}
       \ll\frac{x}{sL}\eta\log^2(2/\eta).
\tag{12}
\]
Here the first sum is over primes and the powers are summed by
geometric series. For the last estimate, \(\log u/L\ge\eta\) has
double harmonic mass \(O(\log^2(2/\eta))\) by Mertens. Below
\(\eta\), split \(\log u/L\) into dyadic shells \(\eta2^{-j-1},\eta2^{-j}\).
The \(u\)-harmonic is \(O(1)\) per shell and the \(v\)-tail at most
\(O(1+\log(1/\eta)+j)\), giving a convergent geometrically weighted
sum. The case \(z\ge Z\) has the same tuple bound with \(\eta^2\)
instead by the two neck-base harmonics, and the no-core semiprime
population gives \(\eta\) as in the preceding note.
The harmonic main is bounded over the **union** of the outer boxes
with only the fixed orientation or prime-label multiplicity, not
by multiplying (12) by the number of fine boxes.

Combine (11), (12), the \(O(w)\) true \(p\)-harmonic per \(s\) and
bounded true \(s\)-harmonic. The total **actual** adverse count in
the asserted sectors is bounded by
\[
      O(w\eta\log^2(2/\eta)\,\mathfrak S(N)x/L^2)
                                  +O_{D,\eta}(xL^{-D}).
\]
The coefficients are bounded there, \(|F_s|\ll L\), and \(W_s\)
is bounded and nonnegative. All remaining portions of these
sectors were favorable and need no absolute estimate.
This proves (3) with the indicated order of limits and absolute
first constant.

Compared with the lower reverse cut, the whole giant-prime adverse
rank-three chamber is identically absent. The result concerns only
the given actual reflected semiprime profile. The incomplete
Möbius function in (9) for at least three small bases can have yet
other signs, or the core itself can exceed the short endpoint.
Neither that full signed complement nor strong Goldbach is solved.

## Comparison with nearby work

The large-residue input is [Lichtman's Proposition 5.2](https://arxiv.org/abs/2309.08522). [Arneth's September 2026 marked-switching audit](https://zenodo.org/records/23011047) treats other weighted sieve and parity issues; [the November Li–Liu formalization chapter](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-liliu.html) treats a separate almost-prime count. The theorem here preserves the exact reflected semiprime band and prices only the quotient cells with at most two distinct small bases after the raised reverse cutoff. It uses no new result from those manuscripts.
