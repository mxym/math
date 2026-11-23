# The true explicit-tiny intersection with the negative-arm removal

Use the same original sharp cubic–quintic \(H\) and one fixed
\(J\Subset(1/3,2/3)\) throughout. The notations, target units,
\(M\), and actual \(R_J\) are those of
[the sharp detector](CubicQuinticSharp.md).
Use these three physical subsets of the same reflected pairing:
\[
 \begin{split}
 \mathcal P&=\{\text{both arguments squarefree of rank 2 or 3
                         and both least factors }>N^{.123}\},\\
 \mathcal A&=\{\text{some argument has }H<0\text{ and }P^->N^{.105}\},\\
 \mathcal I&=\{\text{some argument has }P^-\le N^{1/5000}\}.
 \end{split}
\]
The first support is disjoint from each of the others. The last two
supports are not disjoint.

**Theorem.** The complete signed contribution on
\(\mathcal I\cap\mathcal A\) is less than \(.218M+o(M)\).
Consequently the original literal covariance satisfies
\[
 R_J\ge .130M+
  \sum_{(x,y)\notin \mathcal P\cup\mathcal A\cup\mathcal I}
                  H(x)H(y)+o(M).
 \tag{1}
\]
The complement is not estimated here. In particular there is no
claim of a sufficient unconditional bound on it, or of a prime pair.

Use the magnitudes \(A=[-H]_+1_{P^->N^{.105}}\) of
[the negative-arm proof](NegativeArmUnion.md), and retain the exact
\(b=1/5000,T,C,D,E,V,X,Y,m_b\) of
[the explicit tiny theorem](ExplicitTinyUnion.md).
On a true intersection row the tiny arm and the negative
\(.105\)-rough arm must be opposite, since \(b<.105\). Both
orientations are included and do not overlap. Thus the sought
intersection is exactly \(-\langle T,A\rangle-\langle A,T\rangle\).
In either orientation the genuine stopped and defect transfers give
\[
 -\langle T,A\rangle/M
  \le (-m_b+U_D)m(A)+\langle |V|,A\rangle/M+o(1).
 \tag{2}
\]
This uses \(T=C+E+V-D\), the zero transfer of \(E\), and the
**actual** positive bound \(\langle |D|,A\rangle\le U_Dm(A)M+o(M)\).
No opposed prime term is assumed.

We apply Cauchy to the actual row weights. On each actual integer,
Cauchy on its certificate labels gives \(|V|\le L\sqrt{XY}\)
because the absolute signed certificate sum is at most the
certificate count. For every genuine compact nonnegative source
\(A_j\) below, weighted Cauchy on the very same fixed-target pairs
therefore gives
\[
  \langle |V|,A_j\rangle
       \le \{\langle LX,A_j\rangle\langle LY,A_j\rangle\}^{1/2}.
 \tag{3}
\]
In the receiver bound for \(LY\), every actual certificate prime other than the
distinguished genuine least prime has angle \(\ge u_0\), and the real
certificate product \(h\) has angle \(\le c+b=(11/2)b\). The same
true quotient upper sieve and target units as in the explicit tiny
theorem work here, with ratio at least
\((.499-(11/2)b)/b>5\). Since the linear upper function is decreasing,
we can use \(e^{-\gamma}F_1(5)<.565\) instead of \(2/3\).
For this number the exact delay formula is
\(5e^{-\gamma}F_1(5)=2+\int_3^5 2\log(s-2)/(s-1)\,ds\);
the attached rational checker uses upper numerators and lower
denominators on mesh \(1/1000\). In the true certificate ordinary
sum the other-label density is bounded by \(.6/x_0\) on its
width-\(x_0\) window, with \(x_0=u_0/b\), just as in the explicit
tiny theorem. Thus the real conditional upper for \(LY\) is
\((.678/b)m(A_j)M+o(M)\), from
\(.565\cdot.6\int_0^1x_0^{-1/2}dx_0=.678\).
For \(LX\), use the actual receiver of the negative-arm proof
\(\langle LX,A_j\rangle \le U_j\,m(LX)M+o(M)\), with
\(m(LX)\le B_X^2\).
First work on the artificial positive floor and fixed ranks
of the explicit tiny proof, then remove the truncations in its
specified order. These Cauchy and conditional sieve operations
require no formal product measure on the paired rows.

Use three disjoint sources \(A_j\). The middle
\(N^{.105}<P^-\le N^{.150}\) range excluding rank 8 has cap
\(.915L\) and the genuinely opened least-prime receiver
\(U_1<1.7902\) from §3 of the negative-arm proof, because the
ranks are disjoint before that upper. Its ordinary mass is
at most the full middle upper \(.077983212\). The high range has
\(U_2=(40/9).915\), using the true \(.150\)-rough receiver,
and ordinary mass \(<.00672821\). The middle rank 8 source has
ordinary mass \(<.000001073\) and positive cap \(1.2L\);
use the ordinary real \(.105\)-rough conditional upper with
ratio \(>.4999/.106>3\), or directly \(.499/.105>3\), giving
\(U_3=(2/(3\cdot.105))1.2\).
All numbers on these true source/receiver weights use the same
actual fixed target and reflected interval.
The total ordinary mass \(m(A)<.08472\) and
\(-m_b<.0063885,\ U_D<.0111568,\ B_X<.0033960\) by the
explicit tiny checker. Hence (2)–(3) give a two-orientation
upper less than \(.218M+o(M)\); the checker upper is
\(.2172742268\ldots\).

Finally use only the existing genuine \(.804M\) combined
lower for the disjoint \(\mathcal P,\mathcal A\) from
[the wider positive block](WiderPositiveBlock.md), and the
original \(-.456M\) lower on the whole actual \(\mathcal I\).
The unique overlap charged when combining them is exactly the
one just bounded above. Inclusion–exclusion gives (1).
The earlier whole \(.150\)-rough lower is not used, and no new
copy of \(R_J\) occurs on the right.

Run:

    python3 -OB check_explicit_tiny_negative_overlap.py
