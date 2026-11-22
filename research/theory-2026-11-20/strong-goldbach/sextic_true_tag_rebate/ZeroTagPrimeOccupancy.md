# Mandatory prime occupation of the full complementary signed arm

Use the original target and score \(S=G_b+W,\ b=.003\),
the fixed central interval \(J\), unit pairing, \(L=\log N\)
and \(M=|J|N\mathfrak S(N)\) of the
[full zero-tag comparison](FullZeroTagAffineSelf.md).
Let \(I_0=1_{P^->N^{.080}}\),
\(U=I_0 S\), and \(Y=(1-I_0)S\), on their literal supports.
Write \(Y_\pm=[\pm Y]_+\) for the actual original signs.
Thus \(Y\) is the whole complementary arm with at least one
genuine prime in \((N^{.003},N^{.080}]\), including the
original clipping. All later tag-count masks are absent
from this statement; it holds on the union, not separately
with the same reserve in each tag count.

**Proposition.** Both target orientations have actual weighted
prime occupation
\[
 \begin{split}
  \langle\Pi,Y_-\rangle
    &>\langle\Pi,Y_+\rangle+1.472M+o(M),\\
  \langle Y_-,\Pi\rangle
    &>\langle Y_+,\Pi\rangle+1.472M+o(M).
 \end{split}
\]
These are genuine prime-opponent statements, with the same
fixed \(N\); no lower is claimed for the covariance of the
nonprime exterior. The displayed credit is a single occupancy
constraint on the whole mixed zero-tag union.

## 1. The reflected signed prime cross, now lower as well as upper

Keep the physical \(V_0\) of the
[full zero-tag comparison, §1](FullZeroTagAffineSelf.md#1-the-physical-expansion-and-its-cap).
With exactly the same actual divisor layers, linear functions
and affine bounds as
[the exact linear refinement](ExactLinearZeroTag.md),
one has
\[
                   \langle\Pi,V_0\rangle>3.25555M+o(M),           \tag{1}
\]
and the same reflected lower. Indeed take the actual lower
on **even** divisor labels in the true prime-source linear
sieve, and the actual upper on **odd** labels.
At the even \(d=1\) atom use \(k_1(.499)\).
For a non-atomic cell of upper angle \(s_+\), put
\(\Delta=.499-s_+\) as in the original proof.
At \(\Delta>0\) the negative of its lower is bounded by
\[
                        F(s)(U_1O-k_1 E).
\]
A second valid upper on that negative is \(F(s)O C_2\):
discard the even positive part and use the existing
true \(q+dr=N\) prime-only augmented Selberg upper on
the odd labels. This bound is valid up to \(s=.500\),
including cells where the sub-root transfer is not
available. Take the smaller **outward** upper in
each cell, and use only the actual affine estimate
when \(\Delta\le0\). Both signs are estimated before
they are combined, with actual target coprimality
and the same restored square and own-log errors.
Nothing has changed in the physical weights or levels.

The attached outward checker reuses the exact linear
delay and affine routines by hash. Its lower in (1)
is \(3.255556007576\ldots\).

## 2. All tiny, clipping and prime-pair terms

Write \(T=1_{P^-\le N^{.003}}H\). The original \(Q\)
is supported on \(I_0\). The physical \(W\) is supported
on \(1-I_0\) (its two least prime angles have sum at
most .065), and \(T\) is also supported on \(1-I_0\).
Thus
\[
              Y=H-(V_0-\Pi)+W-T
\]
exactly on central arguments: \(V_0-\Pi=I_0H\)
since every central prime passes \(I_0\).
The native true-prime calibration is
\(\langle\Pi,H\rangle=M-R_J+o(M)\)
from [the sextic proof](Proof.md#1-calibration-and-physical-limits);
the other orientation holds on \(1-J\). Therefore there
is exact cancellation of the actual \(R_J\) terms, giving
\[
     \langle\Pi,Y_-\rangle-\langle\Pi,Y_+\rangle
     =\langle \Pi,V_0\rangle-M-\langle\Pi,W\rangle
                              +\langle\Pi,T\rangle+o(M).          \tag{2}
\]
This is an identity on the whole unchanged complementary arm,
not a fresh lower bound on prime-pair mass.

By [the full medium proof, §2](FullMediumCohort.md#2-ordinary-mass-and-genuine-positive-receiver-for-the-full-weight),
the actual positive \(W\) receiver has \(U_W<.52844\)
against a genuine compact nonnegative prime-product source.
It applies to the actual prime source \(\Pi\), of
ordinary mass 1, giving \(\langle\Pi,W\rangle<.52844M+o(M)\).
For the exact tiny cutoff .003 use the
[proved sign split](ImprovedTinyCovariance.md#4-replacement-in-the-identical-signed-ledger)
and notation \(T=A+E+Z\), with \(Z=V-D\) of that proof
(its \(V\) is the stopped remainder, not our \(V_0\)).
It gives actual \(\langle\Pi,A\rangle=c_A M+o(M)\),
\(\langle\Pi,E\rangle=o(M)\), and genuine ordinary masses
\[
    |c_A|<.228,\quad |m(Z)|<10^{-7},\quad
    m(|Z|)<.009042+.006657 .
\]
The same true \(3.446\) prime receiver applied to \(Z_-\)
bounds \(-\langle\Pi,Z\rangle\) by
\[
      3.446\,m(Z_-)M+o(M)
      \le 3.446\,(\,.009042+.006657+10^{-7}\,)\,M/2+o(M).
\]
It follows that \(\langle\Pi,T\rangle>-.25506 M+o(M)\).
All three estimates hold with the reflected interval,
using its equal genuine length. Inserting them into
(2) proves the proposition.

In a common physical ambient this really removes rows
from a potential adverse zero-tag receiver: for example
let \(U_{\ell,+}\) be the positive part of \(U\) on
completed ranks at most seven. Then
\(U_{\ell,+}+\Pi\le L I_0\) pointwise, by the actual
rank-two, rank-three and rank-four positive caps, the
negative ranks five through seven, and \(H=0\) on primes.
Consequently
\[
  \langle U_{\ell,+},Y_-\rangle
    \le \langle L I_0,Y_-\rangle
                -\langle\Pi,Y_+\rangle-1.472M+o(M)
\]
on the same actual mixed support, and in reverse. This
does not pay the high positive ranks, the entire mixed
covariance, or any particular selected subchamber. In
particular one cannot take the same occupancy reserve
again after removing a subchamber without keeping its
true overlap.

Run:

    python3 -OB check_zero_tag_prime_occupancy.py
