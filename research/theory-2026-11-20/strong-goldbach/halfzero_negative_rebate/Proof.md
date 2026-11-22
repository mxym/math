# A true prime rebate on the negative rank-three to rank-five half-zero score

Let \(N\) be an individual even target, \(L=\log N\), and fix a
nondegenerate \(J\Subset(1/3,2/3)\). On the actual rows \(x+y=N\),
\(x\in NJ\), \((x,N)=1\), put
\[
 M=|J|N\mathfrak S(N),\qquad
 \Pi(n)=1_{n\ {\rm prime}}\log n,\qquad
 R_J=\sum_{\substack{x\in NJ\\(x,N)=1}}\Pi(x)\Pi(y).
\]
The singular series \(\mathfrak S\) is the same as in the
[half-zero detector](../halfzero_detector/Proof.md).
For an actual squarefree integer \(n>1\), define the literal own-root
angular scores
\[
 A_j(n)=\sum_{d\mid n}\mu(d)
             \left(1-\frac{2\log d}{\log n}\right)_+^j,\qquad j=2,4,
\]
and the actual half-zero score
\[
 H(n)=(\log n)\left\{\frac74 A_2(n)-\frac34 A_4(n)\right\}
                                      -\Pi(n).
\]
Set \(H=0\) on nonsquarefree integers. By the cited theorem this is
the squarefree own-log representative of its score, with
\(o(M)\) absolute change in its full paired sum. Only that
quartic half-zero score is being used, not the compensated
unit-jump receiver.

Put \(S_j=1_{\{n\ {\rm squarefree},\ \omega(n)=j\}}[-H(n)]_+\)
for \(j=3,4,5\). With
\(\langle \Pi,S\rangle=\sum_{x\in NJ,(x,N)=1}\Pi(x)S(y)\)
one has, for every sufficiently large even target,
\[
 \frac{21}{5}\langle\Pi,S_3\rangle
       +\frac43\langle\Pi,S_4+S_5\rangle
         > .263 M+\frac{11}{20}R_J,                            \tag{1}
\]
and in particular
\[
                   \langle\Pi,S_3+S_4+S_5\rangle > .062 M .
                                                                  \tag{2}
\]
Both inequalities hold with the same weights reflected to \(1-J\).
They still hold if the respective \(S\)'s are limited to actual
\(P^-(n)>N^\eta\) for one sufficiently small fixed \(\eta>0\).
This is a genuine prime-opponent lower on the *negative* scores
that enter the signed negative-arm decomposition. No lower is
claimed on either exact rank separately. In particular it may
include rows with the very rough negative arm already considered in
[the negative-rough-arm estimate](../halfzero_detector/OneArmRoughDebit.md):
one cannot add it as a new small-factor credit to that estimate
without accounting for this overlap.

## 1. True calibration for the comparison profile

Take \(c=31/20\), \(B_c=A_4-cA_2\), and use \(B_c\) on
actual squarefree rows. For each \(j=2,4\) the prime-opponent
calibration, including the prime atom of \(A_j\), is
\[
       \sum_{\substack{x\in NJ,\ (x,N)=1\\y\ {\rm squarefree}}}
                     \Pi(x)(\log y)A_j(y)=2j M+o(M).           \tag{3}
\]
Here is the scope of the analytic transfer. With \(t=\log d/L\),
the profile \(f_j(t)=(1-2t)_+^j\) has a zero of order at
least two at half. Use the strictly sub-root smooth cutoff
\(f_j(t)\chi((t-1/2)/\delta)\) in the
[half-zero proof, §§1–3](../halfzero_detector/Proof.md).
For fixed \(\delta>0\) this has its true support
\(d\le N^{1/2-\delta}\) and derivative \(-2j\) at zero.
Ordinary weighted maximal-prefix prime Bombieri--Vinogradov
has the required strict reserve there. Retain the actual
central endpoints and \(\log y\) in the reduced model.
The signed \(\mu(d)/\varphi(d)\) zeroth moment with the
real \(N\)-unit mask vanishes, and its first log moment is
\(-\mathfrak S(N)\); hence this principal is \(2jM+o_\delta(M)\),
not a model of prime pairs. Higher powers in the von Mangoldt
version of BV occur at \(O(N^{1/2+o(1)})\) actual source
integers, with only fixed divisor/log weights, and are removed.

The Fourier envelope in the cited proof applies verbatim
to \(f_j\) and its taper: the difference has a factor
\(\delta^j\), instead of \(\delta^2\), with uniform scaled
bounded-variation derivative norms, so its weighted Fourier
norm tends to zero. Retain the true prime as the opposite
arm. This justifies \(\delta\downarrow0\) after the fixed
target limits, and also the exponential rank and polynomial
tiny-factor tails there. Actual nonsquarefree rows cost
\(o(M)\) after this tiny-factor bound and the true large
square count. The Lipschitz own-log change on a fixed
rough rank costs \(O(1)\) per detector, and the true
two-rough count is \(O_\eta(M/L^2)\); hence it is harmless.
These are the squarefree own-log values in (3). In
particular all prime terms are retained with the real
weight \(\Pi(x)\log y\), not with a hypothetical count.

On a prime \(B_c=1-c=-11/20\). Thus (3) gives the exact
real prime-free principal
\[
  \sum_{\substack{x\in NJ,\ (x,N)=1\\y\ {\rm squarefree\ composite}}}
             \Pi(x)(\log y) B_c(y)
           =1.8 M+\frac{11}{20}R_J+o(M).                     \tag{4}
\]

## 2. Pointwise payments on the true negative scores

Write \(h=H/\log n\) on a squarefree composite and
\(u_p=\log p/\log n\), so \(\sum u_p=1\).
On rank four \(A_2=0\) and \(A_4=192\prod u_p\).
On rank five \(A_2\le0\) and \(A_4\ge0\), by the
[same fixed-rank finite differences](../prime_neutral_quartic_rank34/Proof.md),
or the central density formula in
[the negative-rough-arm estimate, §1](../halfzero_detector/OneArmRoughDebit.md).
Consequently on either rank
\[
          B_c\le\frac43[-h]_+ .
\]
This is an exact pointwise comparison on the unchanged
negative score. Every even rank at least six has \(A_2=A_4=0\)
by complementary subsets and the full polynomial moments.

On rank three \(A_2>0\). Put \(r=A_4/A_2\) and
\[
       \omega(r)=\left[r-\frac{31}{20}
                         -\frac{63}{20}(r-7/3)_+\right]_+ .
\]
The exact pointwise bound is
\[
           B_c\le\frac{21}{5}[-h]_+ + W_3,\qquad
                            W_3=A_2\omega(r).                 \tag{5}
\]
For nongiant rank three, set \(a_i=1-2u_i\), \(a_i\ge0\),
\(\sum a_i=1\). Its real short subsets are just the empty
set and the singleton labels. Thus
\(A_2=1-\sum a_i^2,\ A_4=1-\sum a_i^4\).
In this case \(A_4\le2A_2\): if
\(e_i\) are the elementary symmetric functions of the
three \(a\)'s, then \(2A_2-A_4=2e_2^2+4e_3\).
Thus \(W_3=(1-c+c\sum a_i^2-\sum a_i^4)_+\).
With a giant, write \(s=u_1+u_2<1/2\) for the two
other actual angles. The complete cofactor differences
give
\[
 A_2=8u_1u_2,\qquad
 r=6(1-s)^2+2(u_1^2+u_2^2).
\]
In particular (5) includes the actual negative giant
rank-three chart and its transition at \(h=0\); it does
not treat all of \(B_c\) on that rank as transferable
negative mass.

On rank two, with \(a=1-2u_{\min}\), the unused
positive cap for \(B_c\) is
\((1-a^2)(1+a^2-c)_+\). On the remaining odd ranks
at least seven, a positive upper consists of \(c(-A_2)_+\)
and \(A_4\) only if it is positive. Rank seven has \(A_4\le0\).
We use the rigorous angular estimates (8)–(10) of
[the prime-neutral quartic–quadratic calculation](../prime_neutral_quartic_rank34/Proof.md);
in its ordinary simplex harmonic normalization they give
\[
 \sum_{\substack{j\ge7\\j\ {\rm odd}}} I_j((B_c)_+)
  \le c(.01661+.01824+.02010)+.00163=.0868025,               \tag{6}
\]
where \(I_j(G)=\frac1{j!}\int_{\sum u_i=1}\!G\,\prod u_i^{-1}
\,du_1\cdots du_{j-1}\). In particular *rank five is not
an unwanted high-rank charge* in this comparison.

## 3. Certified actual margins

The unused rank-two integral is
\(2\int_0^1(t^2-.55)_+\,dt\). It is bounded above by
\(2((1-b^3)/3-b^2(1-b))\) with \(b=.74161<\sqrt{.55}\).

For the nongiant part of \(I_3(W_3)\), use the variables \(a_i\)
above. The density becomes
\(\frac13\,da_1\,da_2/\prod (1-a_i)\).
By symmetry take \(a\) as the largest among the three
(equivalently multiply this restricted integral by three),
write \(b=(1-a)t,\ d=(1-a)(1-t)\), and use
\(a\in[1/3,1]\), \(t\in[0,1]\), \(b,d\le a\).
The density is now \(da\,dt/((1-b)(1-d))\); on this
region \(b,d\le1/2\), so the denominator is bounded
away from zero. Divide each coordinate into \(m\)
equal pieces. Drop a rectangle only if its lower
\(b\) or \(d\) bound already exceeds its upper \(a\)
bound. In each retained rectangle use independent
upper endpoints for \(b,d\), clamped at both their
proven upper bounds \(\min(a_{\max},1/2)\), for the
denominator and for \(c z^2-z^4\). This polynomial is
increasing up to \(1/2\); its maximum on the
\(a\)-interval is the maximum of its endpoints or
\(c^2/4\) if that interval contains \(\sqrt{c/2}\).
These bound the nonnegative numerator even if no
physical cofactor lies in part of the rectangle.

For the giant part, choose the actual giant slot (factor
three of the \(1/3!\) ordered symmetry), and change to
\(s=u_1+u_2\), \(t=u_1/s\).
The \(A_2=8u_1u_2\) factor cancels the two small angles.
Restrict \(t\) to \([0,1/2]\) with a factor two by
symmetry. The integral is now
\[
       \int_0^{1/2}\int_0^{1/2}
                     \frac{8s}{1-s}\omega(r(s,t))\,dt\,ds .
\]
The ratio \(r(s,t)=6(1-s)^2+2s^2(t^2+(1-t)^2)\)
decreases in both variables in this square.
On each equal rectangle take its exact two corner
bounds. The positive piecewise linear \(\omega\) is
bounded by the maximum of its endpoint values or by
\(\omega(7/3)=47/60\) if the interval contains that
knot. Use the upper endpoint for the positive weight
\(s/(1-s)\). All operations are rational and use
only positive upper errors.

The [integer rectangle checker](check.py) with \(m=1024\)
and upward rounding of each rectangle gives bounds
\(.110529,\ .033539,\ .214979\) respectively for the
rank-two, nongiant rank-three and giant rank-three
integrals. It also checks (6) with the prior rigorous
constants. The [actual \(3.446\) prime upper](../angular_prime_first_composite/Proof.md)
applies to these nonnegative angular source caps, with
the same central \(J\); its unopposed moment times
\(M\) is exactly the normalization of the displayed
integrals. For compact fixed ranks use actual
polynomial floors and Jordan approximation on the
original prime products. Then use the genuine rank
and tiny-factor estimates from §1 for \(A_2,A_4\)
on the true prime source to exhaust those fixed
floors/ranks, in this order: large fixed rank, small
fixed angular floor, then large \(N\). The same
bounds control \(H\) and the actual positive-part
comparison profiles in (5). Thus there is no
conjectural correlation in the use of the angular
integrals. With the exact upper bounds the actual
total unwanted positive sum is \(<1.5364 M+o(M)\).

Combining (4)–(6) proves (1), with room
\(1.8-1.5364>.263\); dividing by the largest coefficient
\(21/5\) proves (2).
The absolute tiny-factor estimate on the same true
prime source, after choosing a sufficiently small
fixed \(\eta>0\), retains both strict lower constants.
For later use, the exact signed negative-arm identity
with \(S=[-H]_+\) has two **favourable** terms
\(\langle\Pi,S\rangle+\langle S,\Pi\rangle\).
The present lower is on these terms for the same
physical \(H\), but only as part of a full negative-arm
ledger: it controls neither its ordinary debit
\(\mathfrak S(N)\sum S\), nor the genuine joint overlap
\(\langle S,S\rangle\), nor the distribution of this
prime rebate between the rough and nonrough ranks.
