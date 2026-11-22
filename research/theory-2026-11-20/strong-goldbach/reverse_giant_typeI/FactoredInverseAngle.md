# A factored-modulus inverse rectangle above the root

Use the actual \(\mathcal D_I\) of [SecondTypeI.md](SecondTypeI.md),
with \(N\) a prescribed even integer and \(I\subset[N^{1/2+\varepsilon},B]\).
All numbers in exponent intervals below are exact decimals.
Restrict to the following simultaneous, literal labels:
\[
\begin{split}
 N^{.24995}\le a\le N^{.25005},\qquad
  N^{.37495}\le m,k\le N^{.37505},\qquad
 N^{.50025}\le b\le N^{.50240}.
\end{split}                                                       \tag{1}
\]
In addition \(b\) must admit a factorization \(b=b_0b_1b_2b_3\),
where the \(N\)-exponents of the four factors lie respectively in
\[
 [.18945,.18955],\quad [.09445,.09455],\quad
 [.10845,.10855],\quad [.10750,.11020].                             \tag{2}
\]
These are conditions on the actual \(b\); it is counted once, not
once per possible factorization.

**Theorem.** The restriction of \(\mathcal D_I\) to (1)–(2)
is \(O_{A,\varepsilon,J_0}(NL^{-A})\) for every fixed \(A>0\),
with no radical restriction on \(N\).
No absolute bound on the raw weighted mass or any sign of
the remaining sum follows. This range is separate from the
previous [sub-root](ConductorHalf.md) and
[balanced over-root](OverRootAngles.md) ranges:
here \(t=\max(\log_N a,\log_N(mk))\) is near \(.75\).
It is outside all three [elementary rectangles](IntegerRectangles.md):
\(1.5\log_N b\ge .750375>.75010\), and \(b\) exceeds
both \(m,k\) by fixed powers. The physical giant exponent
\(\log_N(ak)\) is near \(.625\). The region is a
fixed-width, factored-modulus example, not an estimate
on every modulus in the indicated \(b\)-range.
The modulus condition has positive fixed harmonic width: one
can take each \(b_i\) prime in a fixed smaller exponent interval
about \((.18950,.09450,.10850,.10950)\). The intervals are
disjoint and the resulting \(b\)'s have exponent near \(.502\).
Prime Mertens gives a fixed positive lower bound for their
\(\sum 1/b\); omitting prime factors of \(N\) costs \(o(1)\).
This does not assert a lower for the signed remainder.

## 1. Actual shifted inverse rectangles

Because its exterior coefficient is \(\mu(b)\), every
contributing \(b\) is already squarefree. Fix any such \(b\)
and one factorization from (2). Let \(U,V\) be arbitrary
shifted integer intervals of positive coordinates at scales
at most \(N^{.37505}\). For \(c\) a unit modulo \(b\), let
\(R(c)\) count \(u\in U,v\in V\) with \(uv\equiv c\bmod b\).
Fourier expansion in \(u\) gives the principal
\(|U|\#\{v\in V:(v,b)=1\}/b\), up to the single
cardinality floor if \(|U|\) denotes real length.
The nonzero part is bounded by
\[
 \sum_{j\bmod b,\ j\ne0}
 \frac{|\widehat{1_U}(j)|}{b}
 \left|\sum_{\substack{v\in V\\(v,b)=1}}
               e_b(jc\overline v)\right| .
\]
If \(g=(j,b)\), the sum of the normalized Fourier
magnitudes at the indices in this group is
\(O(\log(2b)/g)\), by the elementary geometric series.
Put \(q=b/g\). Open \((v,g)=1\) by \(e\mid g\);
then set \(v=e v'\). Squarefreeness gives
\((e,q)=1\). The true numerator in the inverse
exponential is \((j/g)c\overline e\bmod q\),
a unit at the reduced conductor \(q\).
The interval \(V/e\) is still an arbitrary shifted interval.

If \(g\ge N^{.005}\), completed Weil and complete
periods bound each reduced inverse sum by
\(q^{1/2+o(1)}+O((|V|+1)/(e q))\).
Indeed the zero-completion sum at a unit numerator
is a Ramanujan sum of absolute value at most 1.
The bound holds even if \(|V|>q\).
With the weight \(1/g\) above, this contributes at most
\[
 N^{o(1)}(b^{1/2}N^{-.0075}+N^{.37505}/b)
           \ll N^{.24371+o(1)}.                               \tag{3}
\]

If \(g<N^{.005}\), then \(q\gg N^{.49525}\), larger
than \(N^{.37505}\), so the interval-size condition of
[Irving, Theorem 1.3](https://arxiv.org/pdf/1403.8031v2)
holds with the upper length \(K=N^{.37505}\).
Use exactly the factorization
\(q_i=b_i/(b_i,g)\), \(0\le i\le3\), of \(q\).
That theorem gives, with arbitrary fixed \(\epsilon_0>0\),
\[
 q^{\epsilon_0}
 \left\{
   \sum_{j=1}^3 K^{2^{-j}} q^{1/2-2^{-j}}q_{4-j}^{2^{-j}}
   + K^{1/8} q^{3/8}q_0^{1/16}
   + q^{1/2}q_0^{-1/16}
 \right\}
\]
as an upper bound for the absolute reduced inverse sum,
up to its fixed implied constant. This is the
incomplete *inverse-sum* theorem, not an application
of a complete divisor-function asymptotic to a
truncated rectangle.

For the four terms with nonnegative exponents of the
factors one can use \(q\le b,q_i\le b_i\).
For the final term use
\[
 (b/g)^{1/2}(b_0/(b_0,g))^{-1/16}
       \le b^{1/2}b_0^{-1/16}.
\]
Thus directed upper exponents in \(N\) before
\(q^{\epsilon_0}\) are
\[
\begin{array}{c|c}
\text{Irving term}&\text{upper exponent}\\ \hline
j=1&(.37505+.11020)/2=.242625\\
j=2&.37505/4+.50240/4+.10855/4=.246500\\
j=3&.37505/8+3(.50240)/8+.09455/8=.247100\\
q_0\text{ positive}&.37505/8+3(.50240)/8+.18955/16=.247128125\\
q_0\text{ negative}&.50240/2-.18945/16=.239359375 .
\end{array}
\]
The sums over \(g,e\), and the geometric Fourier weights,
cost \(N^{o(1)}\). Choose \(\epsilon_0\) with fixed spare
power. The bound for the nonzero part, including (3),
is \(O(N^{.2473})\) for all sufficiently large \(N\).
The one-variable unit floors convert the principal to
\(\varphi(b)|U||V|/b^2\), with an additional
\(N^{o(1)}(1+(|U|+|V|)/b)\); this is negligible.

One may impose literal \((uv,N)=1\) on the same boxes.
Open the two exclusions by exact inclusion–exclusion
over divisors \(f_1,f_2\) of \(\operatorname{rad}(N)\).
They are coprime to \(b\) since \((b,N)=1\).
The new residue is \(c\overline{f_1f_2}\bmod b\)
and the interval lengths only decrease.
Neither the conductor \(b\), nor any \(q_i\) above,
changes because of these target exclusions.
The \(N^{o(1)}\) cost from \(\tau(N)^2\) is permitted
by keeping the spare fixed power in the errors.
The exact resulting principal is
\[
       |U||V|\frac{\varphi(b)}{b^2}
                         \left(\frac{\varphi(N)}N\right)^2 .
                                                                  \tag{4}
\]
This is uniform for all shifted intervals, including
ones shortened to a small edge and ones in which a
large opened target divisor leaves no integer.
In particular its error is \(O(N^{.2474})\).

## 2. Exact cutoffs and the signed principal

Fix the actual \(a,b,d\), opening \(d\mid m\) from
\(Q_y(m)\) with \(d<T_y\) and \(d\ll S\). All three
are target units. Put \(m=d u,\ k=v\).
A row is impossible if \((ad,b)>1\); otherwise the
exact unit class is \(uv\equiv N\overline{ad}\bmod b\).
Apply the preceding count on a fixed relative
\(L^{-F}\) mesh in the two coordinates \(m,k\).
The cutoffs in \(m,k\), including \(d<T_{amk}\),
\(b>Z(N/(mk))\), and the physical central and giant
intervals, are axes or affine linear contours in
log coordinates. Each contour has boundary area
\(O(MK_0 L^{-F})\) in a dyadic box of
coordinate scales \(M,K_0\).
The positive version of (4) counts actual integer
rows on all the boundary boxes. Interior log
weights vary by \(O(L^{2-F})\), by centrality of
\(N-amk\). Thus the arithmetic error is absorbed
before restoring the literal domain in the model.

Indeed summing the uniform count error even over
all \(a,b,d\), all boxes and the log weights costs at
most \(N^{.25005+.50240+.24740+o(1)}=N^{.99985+o(1)}\),
so this has a fixed power saving.
The model volume errors cost at most \(N L^{-F+O(1)}\):
their actual factor at fixed \(a,b,d\) is \(1/(bd)\)
times \(MK_0 L^{-F}\), and \(aMK_0\asymp N\).
Choose \(F\) large at the requested log precision.

After changing \(u\) back to \(m\), (4) has the exact
factor \(1/d\) from interval length. All real domain
conditions other than \(d<T_y\) are independent
of \(d\). At fixed \(a,b,m,k\) the principal signed
small-divisor coefficient is therefore
\[
     \sum_{\substack{d<T_y\\(d,bN)=1}}\frac{\mu(d)}d
                       =O_A(L^{-A})
\]
uniformly at \(T_y\asymp S\), as in
[IntegerRectangles.md](IntegerRectangles.md), (4).
The outside \((a,b)=1\) is kept and is independent of
\(d\). The exact density for the two free coordinates
is (4), with no further unit factor on
\(j=(N-amk)/b\), which is already a target unit.
The remaining sums over \(a,b\) cost only reciprocal
harmonics and log powers after centrality.
This gives the claimed signed deletion.
