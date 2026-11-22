# The projected bilinear comparison at tiny tag scales

Let \(N\) be the actual target, \(L=\log N\), and \(\ell=\log L\).
Retain the statement, actual unit supports, fixed-ratio polynomial
bilinear packets, and full projected major term of
[the reflected comparison](../target_slope_switch/Proof.md).
Only the tag alphabet and the requisite roughness are changed.
Fix real exponents and a positive separation
\[
  1<\theta_- \le \theta_1<\cdots<\theta_K\le\theta_+<2,\qquad
  \theta_{\nu+1}-\theta_\nu\ge c_K>0.
\]
The \(K\) disjoint colors consist of target-unit primes in
\[
       [\exp(\ell^{\theta_\nu}),\,\exp(2\ell^{\theta_\nu})],
       \qquad \tfrac14\le V_\nu=\sum_{p\text{ in color }\nu}1/p
                           \le\tfrac12 .
\]
Each tag \(a\) is the product of one actual prime per color;
\(Y\) is a nonempty fixed-ratio tag shell. The two true source
factors are \(z=\exp(\ell^2)\)-rough, not necessarily rough at
the much larger scale required by the original application.
Then for every fixed \(R>0\), with \(K\) fixed sufficiently large
after \(R\) and the fixed polynomial-packet data,
\[
                       Q_Y-\mathcal M_N=O_R(NY L^{-R}) .          \tag{1}
\]
This is still the **full-target** projected major term, with its
genuine congruence modulo \(N\). The estimate allows a product
of fixed bounded multipliers on individual tag primes. Here and
below the fixed exponent windows are separated, with gaps that may
depend on the chosen fixed \(K\). Each \(\theta_\nu\) may vary inside
its fixed window, uniformly in \(N\) and in the family.

The full projected major bound from
[the small-radical proof, §2](../small_radical_projection/Proof.md)
also holds with these tags whenever its signed source coefficient
and distinct-character Gram inputs hold at the same moduli. In
particular this gives a conditional-on-the-source-input
\(Q_Y=O_R(NY L^{-R})\), not an estimate for arbitrary rough
prime-like coefficients. No result about the original shift-one
major arcs of Jiang--Lau--Lü is needed.

## 1. Rescaling the proof, not the printed tag hypothesis

We audit [Jiang--Lau--Lü v2, §§5–6](https://arxiv.org/html/2611.12467v2)
inside the full-target determinant and starting-frame proof just
cited. Their printed (4.1) and Lemma 6.11 do **not** include these
tiny tags. Keep their unchanged amplification and moment depths
\[
 J_0=\lfloor L^{.01}\rfloor,\qquad m_0=J_0+1,\qquad
 T=2\lceil L^{1/2}/2\rceil.
\]
These are lengths of auxiliary tuples and paths, not lengths
of actual factorizations in the original additive sum.

Write \(p_0\) for the least alphabet prime, \(D\) for the
product of the shared auxiliary labels, \(d_0\) for its narrow
dyadic-bin scale, and \(H=d_0Y\). Uniformly on nonempty shells,
\[
 \log Y\gg\ell^{\theta_-},\quad \log Y\ll_K\ell^{\theta_+},
 \quad p_0\ge\exp(\ell^{\theta_-}),\quad
 \log H=O_K(m_0\ell^{\theta_+})=o(T).
\]
The tags and all shared labels are units modulo the target.
The initial endpoints, their shear into a unimodular real
lattice, and the scalar \(t=(c mn-a rs)/N\) are unchanged.
The nonzero condition follows from bank avoidance and
\((a,c)=1\). The gcd of each physical endpoint is a target
unit dividing \(t\); its other factor is \(z\)-rough, and
\(5Y<z\), so the endpoint is primitive. Source coefficients
still vanish on every nonselected bank divisor, giving the
same exact fibre constancy and normalized \(O(UV L^{O(1)})\)
coefficient norm in the notation of the comparison.

**Separation and exceptional edges.** Use (5.11) of JLL with
\(L^{\vartheta_s}\) replaced there by \(\ell^{\theta_s}\).
The possible shared products after one omission per color
number at most \(m_0^K\), not the number of all possible
initial tuples. Thus the actual set of lower-color choices
at a fixed tuple satisfies
\[
 \log|\mathcal N_s|
       \le K\log m_0+2\sum_{\nu<s}\ell^{\theta_\nu}
       =o_K(\ell^{\theta_s}).
\]
The first separation failure has real \(r\)-measure
\(O_K(m_0^K Y^{-1/2})\) by the same union over the
\(lD\) frequencies. For the second, for each fixed \(F\)
multiplication by the nonzero integer \((n-n')F\) preserves
circle measure. The pair union has measure
\(\exp(-\ell^{\theta_s}+o_K(\ell^{\theta_s}))\).
Average in \(F\) with its normalized reciprocal weights and
apply Markov at \(\exp(-\ell^{\theta_s}/4)\), as in Lemma 6.13.
The total nonseparated measure is
\(O_K(\exp(-c\ell^{\theta_-}))\), arbitrarily small in
powers of \(L^{-1}\). Repeated shared labels and common
endpoint tags still cost only \(O_K(J_0^2/p_0)\) in the real
reciprocal and the integer pair counts, respectively, by
the same distinct prime counts in Prop. 6.15. The fixed
log-power losses from the \(\theta\)-arc measure and divisor
square moments on the literal target progressions are
unchanged and are absorbed by both savings.

**Geometry and the arithmetic-to-lines comparison.** The
choices in (5.19)–(5.22) are still finite and bounded by
the same displayed powers of \(L\): positions of a path
are \(O(TH)\), the number of distinct active label occurrences
is \(O_K(m_0+T)\), their product has logarithm
\(O_K((m_0+T)\ell^{\theta_+})\), and logarithms of total
absolute path coefficients and counts are
\(O_K(T(\log(2TH)+m_0\ell^{\theta_+}))=o(L)\).
More precisely these fit \(O_K(L^{.70})\) and
\(O_K(L^{.73})\), respectively. The size and the number
of separation frequencies in the proof of Lemma 6.2
have logarithms \(O_K(\log(2T)+m_0\ell^{\theta_+})\),
hence remain within \(O_K(L^{.21})\); opening the
weighted separation indicator changes only at their
endpoints. The box and rational-slope boundaries retain
their same bounded degree. Therefore the inverse-polynomial
cube mesh and the original full-target arithmetic frame count
apply, with the same power-small error after summing paths.
This also applies to the one-edge exceptional calculation.
There is no use here of equidistribution separately in each
slope and no new restriction on the radical of the target.

**Real operator.** Lemma 6.7 uses only the stated separation
in \(Y\), unchanged. In the proof of Lemma 6.8 the actual
large sieve bound is \(O(L^{-A_1}+Y^{-\sigma})\) at any fixed
\(\sigma>0\); the smooth Fourier tail \(|s|>L^{A_1}/2\) is
arbitrary-log small. These statements remain true because
\(Y\) exceeds every fixed power of \(L\), so Dirichlet
denominators between \(L^{A_1}\) and \(Y/L^{A_1}\) and
the same disjoint rational arcs are valid. This proves
the identical small norm for the \((\boldsymbol\epsilon,
\boldsymbol\delta)=0\) block (6.10). Parseval in its tag
frequency still uses the literal integer product, uniquely
determined by the colors. Enlarging the diagonal in this
block costs \(O_K(p_0^{-1}(1+L^{3A_0}))\), as before.

For every other block the row and column argument of Lemmas
6.10–6.11 is unchanged. The only lower-scale changes are that
the separation exception is now
\(\exp(-\ell^{\theta_s}/4)\) in (6.12) and the bad entering
prime uses \(p_*^{-1}\le p_0^{-1}\). In particular its
nonzero memory pattern has small row or column factor
\[
 O_K\!\left(B_*m_0^{-K}
      +B_*^K e^{-\ell^{\theta_-}/4}\right),\qquad B_*=KT .
\]
The other factor has the same bounded \(t=c-a\) row bound;
the \(\mathfrak M\)-parts cost
\(O_K(L^{3A_0}(1+B_*)^K(p_0^{-1}+Y^{-1}))\) on the small
side and the ordinary log bound on the other side. Schur
therefore gives the same prescribed power of \(L^{-1}\) once
\(K\) is chosen large. Bounded tag multipliers at the two
endpoints are diagonal contractions in the zero-memory
block and do not increase absolute row/column estimates for
other blocks. In the flat-path identity one can thus insert
the usual Fejér variables on fresh entering labels as well,
with the same bounded multiplier cost. Neither \(m_0\) nor
\(T\) was decreased: \(m_0=o(T)\), the Fejér endpoint cost
\(2^{K m_0}\) is harmless in the \(T\)-th root, and the
reach cost \((1+TH)^{1/T}\) is bounded as above.

These are all lower tag-scale uses in the proof of the
minor comparison, including Fourier cutoff, repeated and
nonseparated labels, and the path/mesh allowances. They
give (1) by the same moment inequality; the count of
shared-product bins is still \(O_K(L)\).

## 2. Full target character projection

Use the actual full-ring projection, its literal
polylogarithmic rational residues, and the log-power
separations of the cited full major proof. All tag primes
are larger than every fixed power of \(L\); all source
factors here are \(z\)-rough and also units on those small
arc denominators. The projector coefficient bound
\(1/\varphi(N)\) is unchanged.

The only potential new lower-scale cost is the
high character moment of the tiny tag polynomial. At a
full modulus \(M=N b\), \(b\le L^{O(1)}\), choose
\(j=\lfloor\log(M/2)/\log(2Y)\rfloor\). Products of \(j\)
actual tags in the shell are less than \(M\); equality
modulo \(M\) is equality as positive integers. Each such
product has multiplicity at most \((j!)^K\). For bounded
tag coefficients, Markov at threshold \(Y L^{-E}\)
therefore bounds the number of exceptional characters by
\[
 \exp\!\big(O_{E,K}(\log Y+j\log j+j\log L)\big)=N^{o(1)}.
\]
Here \(j\ll L/\ell^{\theta_-}\) and \(\theta_->1\).
Off these exceptional characters, the same full product
Parseval applies; on them, the assumed uniform source
character cancellation and restricted Bessel via the
distinct-character Gram bound give arbitrary-log saving.
No theorem about \(\Lambda\) in a general high conductor
is being assumed in (1) or this conditional full bound.

One may supply disjoint banks of this kind in number
\(O_K(\log\ell)\), with a positive constant times \(\log\ell\)
attainable by subdividing the fixed separated exponent windows
with fixed-ratio ranges for \(\log p\) and the prime harmonic
law in \(1\bmod 4\). Omitting target prime divisors costs
\(O(L/p_0)=o(1)\) in reciprocal mass. In contrast there is
only \(O(\log\ell)\) total prime harmonic mass on this tiny
scale, not the \(O(\ell)\) mass of the original bank range.
