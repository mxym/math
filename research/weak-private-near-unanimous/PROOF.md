# Constant-size shares for the weakly private near-unanimous threshold

## 1. Scope and result

For a secret \(s\in\{0,1\}\), the dealer outputs a tuple of
\(n\) shares. Define a set of parties to be authorized exactly
when its size is at least \(n-1\). Perfect correctness means that
for every secret and every dealer random choice, the secret
is determined by each authorized set's shares. For every
unauthorized \(A\), every possible \(A\)-view \(z\), and
each \(s,t\in\{0,1\}\), \(p\)-weak privacy requires
\[
 \Pr[\mathrm{View}_A=z\mid s]\ \ge\
 p\,\Pr[\mathrm{View}_A=z\mid t].
 \tag{1}
\]
This is the definition in ePrint 2025/1978, Definition 2.2.
The alphabet measure there is \(\max_j\log_2|\mathcal S_j|\).

**Theorem.** For every \(n\ge4\), there is a perfectly correct
\((n-1)\)-out-of-\(n\) scheme for a one-bit secret with alphabet
\(\mathbb F_2^2\) at every party and with \(p=1/3\). It uses
exactly \(2n-3\) fair random bits in worst-case polynomial time.
Its own best parameter in (1) is exactly \(1/3\).
For \(n=2,3\), a perfectly private corresponding scheme has
share size at most two bits. For every \(n\ge3\), no such
scheme with \(p>0\) has alphabets of size at most two at all
parties, so two bits is optimal when lengths are rounded up
to integers. This does not rule out the unrounded
\(\log_2 3\) possibility for \(n\ge4\).

## 2. A balanced coloring of double-parity words

Take \(n\ge4\), set \(N=n-1\), and use only share tuples
in the double-parity code
\[
 \mathcal C=\{((a_1,b_1),\ldots,(a_n,b_n)):\;
       \textstyle\sum_{i=1}^n a_i=\sum_{i=1}^n b_i=0\}.
 \tag{2}
\]
All operations over \(\mathbb F_2\) are additions or
multiplications mod 2. A tuple in \(\mathcal C\) is determined
by two free length-\(N\) columns \(a=(a_i)_{i=1}^N\),
\(b=(b_i)_{i=1}^N\); the last share is their two coordinate sums.

Let \(L\) be the \(N\times N\) lower triangular matrix of ones
on and below its diagonal, with just entries \((1,3)\) and
\((3,1)\) toggled. In particular its top-left \(3\times3\)
block is
\[
 \begin{pmatrix}
 1&0&1\\
 1&1&0\\
 0&1&1
 \end{pmatrix},
\]
and its first three rows have zeros beyond that block.
As a result
\[
 L_{ii}=1,\quad L_{ij}+L_{ji}=1\ (i\ne j),\quad
 r^{\mathsf T}L=0,\quad r=e_1+e_2+e_3.
 \tag{3}
\]
The dealer's coloring of \(\mathcal C\) is
\[
                  f(a,b)=a^{\mathsf T} L b+a_1 .
                  \tag{4}
\]
The translation \(a\mapsto a+r\) toggles \(f\), including
the linear term \(a_1\), and keeps \(b\) fixed.
It partitions the free words into pairs with opposite colors.
Thus both color classes have size \(2^{2N-1}\); in particular
both are nonempty.

**Exact dealer rule.** Draw \(a\) uniformly subject to \(a_1=0\)
and \(b\) uniformly without restriction, independently. If
\(f(a,b)\ne s\), replace \(a\) by \(a+r\). Then add the two
last parity bits. Each pair has exactly one representative
with \(a_1=0\) and exactly one point of the desired secret
color, so the resulting distribution is exactly uniform
on \(f^{-1}(s)\) within \(\mathcal C\).
The number of fair bits is \((N-1)+N=2n-3\).
Computing (4) directly is polynomial time; it can also be
done by prefix sums of \(b\), with the two toggled terms
and \(a_1\) added afterwards.

Any \(n-1\) shares determine the missing share by the
two parity checks, and then (4) reconstructs \(s\).
If all shares are present the same rule reads them directly.
For inputs outside the dealer's support the reconstruction
map can be defined arbitrarily. The distribution never
leaves that support for any dealer random bits, so
correctness is perfect, not asymptotic.

## 3. Exact likelihood-ratio guarantee

Fix an arbitrary set of \(n-2\) observed coordinates,
with the two missing positions \(i<j\). Every observed
tuple in \((\mathbb F_2^2)^{n-2}\) has exactly four completions
in (2): choose the two bits in one missing position,
then the parity determines the other. Equivalently,
starting from one completion, change both missing shares
by the same \((u,v)\in\mathbb F_2^2\).
In terms of the first \(N\) coordinates this changes
\(a\) by \(u h\) and \(b\) by \(v h\), where
\[
 h=e_i+e_j\quad(j<n),\qquad h=e_i\quad(j=n).
\]
The restricted polynomial (4) is a constant plus a linear
function of \((u,v)\) plus \(uv\,h^{\mathsf T} Lh\).
By (3), the mixed coefficient equals one, since for
\(h=e_i+e_j\) it equals \(1+1+(L_{ij}+L_{ji})=1\).
So the four completions have colors
\(uv+\alpha u+\beta v+\kappa\) for some bits
\(\alpha,\beta,\kappa\). After translating \(u,v\) this
is \(uv\) or \(uv+1\), with color counts \((3,1)\)
or \((1,3)\).

Each such observed view therefore has probability either
\(3/2^{2N-1}\) or \(1/2^{2N-1}\) under each secret,
with the larger probability under exactly one of the two.
This is (1) with \(p=1/3\), and every view of every maximal
unauthorized set attains the ratio in its smaller direction.
It applies also to an arbitrary smaller unauthorized set:
extend the set to size \(n-2\) and sum the inequality over
all extra coordinates. Thus the construction's exact worst
parameter is \(1/3\). In particular both secrets remain
possible at every unauthorized view, but their distributions
are not in general identical.

## 4. Small cases and a binary-alphabet obstruction

For \(n=2\), give both parties the secret itself. The only
unauthorized set is empty and has identical views.
For \(n=3\), pick a uniformly random \(R\in\mathbb F_2^2\)
and three pairwise distinct offsets \(q_i\in\mathbb F_2^2\).
Give party \(i\) the share \(R+s q_i\).
Each individual share is uniform regardless of \(s\), and
the sum of any two shares equals \(s(q_i+q_j)\) with a
nonzero factor, so any two recover \(s\).
This gives perfect privacy at the small boundaries.
The \(n=3\) example is an elementary threshold-two scheme,
not a new small-case result.

For the lower bound, suppose instead all alphabets have size
at most two, and label their symbols by bits (padding dummy
symbols if needed). Let \(C_0,C_1\subseteq\{0,1\}^n\)
be the supports of the two conditional distributions.
They are nonempty. Opposite-color words have Hamming
distance at least two: if they agreed outside one coordinate,
that authorized set would be unable to reconstruct uniquely.
For any \(x\in C_s\) and distinct \(i,j\), weak privacy with
\(p>0\) requires some \(y\in C_{1-s}\) agreeing with \(x\)
outside \(i,j\). The distance bound and binary alphabets force
\(y=x+e_i+e_j\). This conclusion is valid even for padded
alphabets, since the opposite word must be in the support.
Thus every two-coordinate flip is available and changes color.

Take three distinct positions \(i,j,k\). Starting at any
supported word, flipping \(\{i,j\}\) then \(\{i,k\}\) changes
the color twice. Their sum is the single flip \(\{j,k\}\),
which changes it once. The resulting word would have both
colors, contradicting correctness. The proof uses only
equality of projection supports for unauthorized sets, and
does not assume uniformity, a linear dealer, or any
quantitative bound beyond \(p>0\).
