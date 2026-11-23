# The actual tiny-factor union for the sharp cubic–quintic score

Use the same sharp \(F(t)=2(1-2t)_+^3-(1-2t)_+^5\), squarefree
score \(H=V-\Pi\), genuine target-unit pairing \(x+y=N\) in the
actual intervals \(NJ,N(1-J)\), and \(L,M,R_J\) of
[the cubic–quintic detector](CubicQuinticSharp.md).
For a small fixed \(b>0\) put
\[
 I_b(n)=1_{\{P^-(n)\le N^b\}},\qquad T=I_bH,\qquad
 m_b=-32b+288b^2-\tfrac{2720}{3}b^3+\tfrac{3040}{3}b^4.
\]

**Theorem.** In the following bounds, first take the limit through
individual even \(N\) for each fixed \(b\), and only then let \(b\)
decrease. The constants in \(O_J\) do not depend on small \(b\):
\[
\begin{split}
  \langle T,H\rangle,\ \langle H,T\rangle
       &=m_bM+O_J(b^{3/2}M)+o_{J,b}(M),\\
  \langle T,T\rangle
       &=m_b^2M+O_J(b^{3/2}M)+o_{J,b}(M).
\end{split}                                                     \tag{1}
\]
In particular the complete signed contribution on the literal union
where either arm has a prime factor \(\le N^b\) is
\[
 \bigl(2m_b-m_b^2+O_J(b^{3/2})+o_{J,b}(1)\bigr)M
       \ge -65bM+o_{J,b}(M)
\]
for all sufficiently small fixed \(b\). The bound is not asserted
for an explicit numerical value of \(b\).

Let \(\mathcal E_b\) be the real complementary region with both
least factors \(>N^b\) and at least one \(\le N^{.150}\).
The sharp square identity and the literal rough positive block give
\[
              R_J\ge (.515-65b)M+
                     \sum_{\mathcal E_b}H(x)H(y)+o_{J,b}(M).
                                                               \tag{2}
\]
The score is unchanged on the exterior. No part of (1) or of the
genuine rough block puts a copy of \(R_J\) on the right of (2);
the remaining signed exterior is not estimated here.

## 1. The four-mark approximation on the actual paired support

Use the taper \(F_h\) of §1 of the cubic–quintic proof with
\(h=5b\), and its own-log score \(H_h\). Our constants below are
uniform for small \(b\). The original Fourier dilation argument
proves an absolute error \(O_J(b^{3/2}M)\) on replacing any
sharp score by its taper, against either score or a genuine
prime leg, even after multiplying the arms by actual indicators.
Indeed choose phase exponent \(3/2\) in that proof:
\(\int |\widehat{F_h-F}(\xi)|(2+|\xi|)^{3/2}\,d\xi\ll h^{3/2}\).
The tapered transform has a uniform
\((1+|\xi|)^{-4}\) majorant, from the same rescaled difference
bound and the original sharp transform.

We give the two physical truncations used here. They apply with
either the sharp or tapered profile, in the true pairing and
in the ordinary single-arm mass. A fixed factor
\(\nu^{\omega(n)}\), \(\nu>1\) sufficiently close to \(1\), can
be included in the phase envelope of that proof without changing
the chosen exponent \(3/2\): its local coefficient changes the
prime-harmonic constant to at most
\(\nu(4/\pi+\epsilon)<3/2\). Thus ranks beyond a fixed \(K\)
may be discarded at cost tending to zero as \(K\to\infty\).
This also handles any fixed power of the number of true factor
subsets with at most four labels, by making a second arbitrarily
small adjustment in \(\nu\). To discard a tiny least factor,
open its actual prime \(p\mid x\), \(p\le N^\eta\), retain its
phase factor once, and put \(x=pv\). Reset all positive
\(p\)-powers in the multiplicative weight of the quotient to
one; there is no second factor at \(p\). At the prime \(p\) only the
quotient form can vanish, since \((p,N)=1\) on genuine rows.
The true two-form envelope for \(v,N-pv\), or its one-form
counterpart in the ordinary mass, has the reciprocal \(1/p\).
Indeed the actual interval has length \(\asymp_J N/p\) and the
bad leading prime produces just one missing root, a bounded
Euler factor; primes of \(N\) remain excluded by the actual units.
These are the same physical marked form bounds as in
[the sextic small-tag calculation](../sextic_true_tag_rebate/WholeTinyRoughCompensation.md#1-a-true-taper-narrow-enough-for-both-whole-small-tag-opens),
with the cubic–quintic Fourier decay in place of that profile.

For \(u\in(0,1)\) and \(T_0=|\xi|\) the needed bound is
\[
 \sum_{\substack{p\le N^u\\p\ {\rm prime}}}
       \frac{|1-e^{i\xi\log p/L}|}{p}
 \ll
 \begin{cases}
     uT_0,&uT_0\le1,\\
     1+\log(uT_0),&uT_0>1 .
 \end{cases}                                                    \tag{3}
\]
Use the prime log harmonic in the first case and split at
\(N^{1/T_0}\) in the second; if the split is below 2 then the full
reciprocal harmonic satisfies the displayed bound. Thus the
additional factor in the phase integral is at most
\(O_\gamma(\eta^\gamma(2+|\xi|)^\gamma)\) for any fixed
\(0<\gamma<1\). In particular the true paired and ordinary
loss from one such factor is \(O_J(\eta^{1/8})\), even with
the small rank tilt above. The paired assertion is for the
absolute product of the scores, not just one-arm average.

Take the actual bank \(\mathcal B=(N^a,N^b]\) of primes,
\(a=b^{16}\). Replace \(I_b\) by its true bank-hit, at cost
\(O_J(a^{1/8}M)=O_J(b^2 M)\). Let \(\omega_\mathcal B(n)\)
count its distinct literal prime factors. The first four
nonempty inclusion–exclusion terms for this hit have absolute
pointwise remainder at most \(\binom{\omega_\mathcal B(n)}5\).
If an absolute remainder appears on either or both arms, name
the five actual distinct primes on that arm and extract their
five phases. Fixed products \(h_1,h_2\) of these actual marks
satisfy that \(h_1,h_2\) are coprime target units and that
\(h_1v+h_2w=N\). A missing arm uses product one. The primitive
two-form fibre has length \(\asymp_J N/(h_1h_2)\), no large
coefficient obstruction at fixed small \(b\), and resultant \(N\).
At primes of the leading coefficients just one quotient root
remains; all named-prime multiplicative weights in the quotients
are reset as above. These changes cost at most an absolute
constant for the at most ten named primes, and target primes
are kept in the singular series. The genuine paired phase
majorant is consequently of size \(M/(h_1h_2 L^2)\) times its
usual two phase powers. All constants are uniform here, since
\(h_1,h_2\le N^{5b}\) and the two affine scales have fixed
polynomial slack for all small \(b\), including \(a\downarrow0\).

Use (3) with \(u=b\) for the five actual reciprocal phase
weights. The normalized single-arm error integral is at most
\[
 C_J\int_0^\infty (1+T_0)^{-5/2}
 \left[bT_0\,1_{\{bT_0\le1\}}+
          (1+\log(bT_0))1_{\{bT_0>1\}}\right]^5dT_0
       \ll_J b^{3/2}.
\]
For two remainders the actual propagated error is bounded by
the sum of the single remainders plus their product: the hit
itself is at most one, and each expansion differs from it by
its stated absolute remainder. The bound for the product
factorizes in these two absolute phase integrals, giving
\(O_J(b^3M)\). We have therefore replaced the actual \(T\)
by the four opened, tapered mark layers in both intended
pairings at cost \(O_J(b^{3/2}M)\). None of these steps uses
independent angular distributions on the actual paired rows.

## 2. The full true single and double main terms

For a marked squarefree product \(h_1\) with \(s\) distinct
bank primes, \(1\le s\le4\), open the exact marked divisor
profile on \(x=h_1v\):
\[
     g_{h_1}(t)=\sum_{e\mid h_1}\mu(e)
                      F_{5b}\!\left(t+\frac{\log e}{L}\right).
\]
This is after changing the smooth tapered own-log denominator
and prefactor to \(L\), which costs \(o_{J,b}(M)\) at fixed \(b\).
To see this for the opened mark sums, first retain the literal
compact positive-floor rank truncation of §1; the product
weights are bounded and the Fourier dilation or ordinary
Lipschitz change applies. Then remove the truncation using
the actual phase bounds with the fixed-power subset tilt.
On the true squarefree quotient \((v,h_1)=1\), and the variable
Möbius divisor \(d\mid v\) is coprime to \(h_1\). When
temporarily expanding the squarefree correction on \(v\),
rows with a square of a mark prime cost
\(O(N^{1-a+o(1)})=o(M)\) by literal square divisibility
and bounded divisor powers. Retain the square label \(e_0\)
only through \(N^{\min(a,b)/4}\). The omitted actual squares
again cost \(o(M)\) by integer multiples and divisor powers.
There is never a prime term on the marked arm. Its actual
modulus is \([h_1d,e_0^2]\le N^{.5-b/2}\), since
\(h_1\le N^{4b}\), \(d\le N^{.5-5b}\). This allows both
ordinary true product BV in the single-mark direction
and direct CRT with total floor \(N^{1-b+o(1)}\) for the
double-mark direction. All grouped modulus multiplicities
are fixed divisor powers, with the usual true target-unit
opening in CRT.

For the single tiny term test the entire opposite \(H\):
on compact positively rough finite-rank product boxes it is
a bounded true angular weight times \(\log n\), both signs
permitted by splitting; its rank-one score is zero. Standard
[genuine product BV](../halfzero_detector/OneArmRoughDebit.md#3-genuine-signed-transfer-and-a-genuine-upper-of-the-overlap)
at the stated strict level gives the reduced principal. The
actual source unit factor is kept in the completed local
harmonic, before its harmless \(1+o(1)\) restoration: a prime
of a genuine source label at fixed floor \(N^\eta\) costs at most
a logarithmic power times \(\sum_{p\mid y,\ p>N^\eta}1/p=o(1)\),
and a shared mark is likewise negligible in the reciprocal
model. The actual squarefree completion and its first-log
moment are just those of §2 of the cubic–quintic proof,
with masks enlarged by the polynomial mark labels:
the local correction at a named prime is \(1+O(1/p)\);
the factors at the small target primes are kept exactly.
Thus the principal of a fixed opened layer is
\[
    \frac{-g_{h_1}'(0)}{\varphi(h_1)}
               \mathfrak S(N)\sum_{y}H(y),
\]
with genuine compact truncations first. The physical bounds
of §1 then remove the finite floor/rank truncations for the
opposing signed \(H\). Its ordinary signed mass in units
\(|J|N\) is \(1+o(1)\): the raw \(V\) has mass \(-F'(0)=2\)
by ordinary integer residue averaging and the first-log
squarefree Möbius completion, while the true PNT prime atom
has mass \(1\). In the ordinary raw local model at \(p\nmid N\)
the factor is \(1-p^{-2}-(1-1/p)p^{-s}\), \(s\) near 1.
At \(s=1\) after extracting the inverse zeta it equals one.
At \(p\mid N\) the factor \(1/(1-1/p)\) cancels the
outside true unit density. This checks the ordinary constant;
it is not the signed mass zero of the sextic.

For the double-mark term use the actual coprime moduli at each
opposite pair, with the same squarefree factors as in §2 of
the CQ proof, and the compatible target units. As in the
[whole tiny CRT comparison](../sextic_true_tag_rebate/WholeTinyRoughCompensation.md#3-both-genuine-tiny-arms-at-once),
the ordinary pair of signed first-log moments gives the multiplier
\(\mathfrak S(N)/(\varphi(h_1)\varphi(h_2))\) times \(1+o(1)\).
At a named prime only its own arm is forced and its square or
opposite divisor is excluded; each remaining local factor is
\(1+O(1/p)\). The squarefree completion, including shared
square and Möbius labels on their *own* arm, uses their actual
least common modulus. In the reciprocal main term only, a
cross-shared genuine named prime has power-small summed
reciprocal cost; no incompatible row is ever restored to CRT.
The two factors are \((-g'_{h_1}(0))(-g'_{h_2}(0))\).
This evaluates the double main without any prime atom.

Summing over \(s\) named labels uses their true ordinary
prime reciprocals, with the factor \(1/s!\) for unordered
distinct labels. With \(\Delta_{\boldsymbol u}=\prod_j(1-\mathcal T_{u_j})\)
and \(\mathcal T_t f(v)=f(v+t)\), the net one-arm coefficient is
\[
 -\sum_{s=1}^4 \frac{(-1)^{s+1}}{s!}
     \int_{(a,b]^s}\Delta_{\boldsymbol u}F'(0)
                        \prod_i\frac{du_i}{u_i}.
\]
All shifts in \(g'_{h_1}(0)\) lie in the unchanged polynomial
part for sufficiently small \(b\); \(F'\) is degree four there.
Every finite difference is \(O(\prod u_i)\), so extending
\(a\downarrow0\) in this main costs \(O(a)=o(b^{3/2})\).
Equivalently the sum is \(\mathbf E[F'(S)]-F'(0)\)
under the formal convolution exponential with cumulants
\(b^j/j\), \(1\le j\le4\). Its first four moments are
\(b,\frac32b^2,\frac{17}{6}b^3,\frac{19}{3}b^4\).
The polynomial \(F'(t)=-2-32t+192t^2-320t^3+160t^4\)
therefore gives exactly \(m_b\). The reflected direction has
the same calculation on the actual opposite interval and
the same length; no symmetry of \(J\) is assumed. The two
main coefficients multiply in the double CRT calculation,
giving \(m_b^2\) with the bounded propagated errors of §1.
This proves (1).

Finally \(I_b(x)+I_b(y)-I_b(x)I_b(y)\) is exactly the indicator
of the union; the main \(2m_b-m_b^2=-64b+O(b^2)\) proves the stated
strict small-\(b\) debit. The tiny union is disjoint from the
unchanged bilateral \(.150\)-rough block for \(b<.150\), so the
original identity \(\langle H,H\rangle=R_J+o(M)\) gives (2).
