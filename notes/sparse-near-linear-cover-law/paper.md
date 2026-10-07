# An asymptotic cover law for sparse nearly linear intersecting hypergraphs

Research continuation, 7 October 2026. We give a cover bound depending on
the edge/rank ratio, without a partite assumption, and describe its
equality regime. The proof uses a cited published colouring theorem.
There is no mathematical priority claim or claim of full formalization.

## 1. Statements and conventions

Let \(H\) be a finite **simple** intersecting \(r\)-uniform hypergraph,
\(r\ge2\). Vertices are restricted to the union of its edges. Write
\(m=|E(H)|\), \(t=\tau(H)\), and
\[
 I(H)=\sum_{\{A,B\}\subset E(H)}(|A\cap B|-1).
 \tag{1}
\]
Pairs in this sum are unordered and distinct. Its summands are
nonnegative. For an empty family set \(t=I(H)=0\). An intersecting
family is linear exactly when \(I(H)=0\). No partite assumption is made.

Define the continuous concave function
\[
 h(x)=\min_{k\ge1}\left\{\frac{k-1}{k+1}
                         +\frac{x}{k(k+1)}\right\},\quad x\ge0.
 \tag{2}
\]
On \([k-1,k]\) its displayed minimum is attained by \(k\). In
particular \(h(x)=x/2\) for \(0\le x\le1\), and
\(h(a)=a/(a+1)\) for positive integers \(a\). It is the piecewise
linear interpolation of these values, and
\[
 h(x)\le\frac{x}{1+x}. \tag{3}
\]

**Theorem 1 (finite envelope inequality).** Fix \(C\ge1\), put
\[
 K=\max\{2,\lceil C\rceil\},\quad L=K(K+1),\quad
 D=L-1,\quad G_C=\frac{(D-1)(D-2)}2.
\]
For every \(\varepsilon>0\) there is a finite constant
\(B_{C,\varepsilon}\), independent of \(H,r\), such that, if
\(m\le Cr\), then
\[
 t\le r h(m/r)+G_C\frac{I(H)}r+
                      \varepsilon r+B_{C,\varepsilon}. \tag{4}
\]
The constant is defined through the threshold in Input K below. No
effective growth rate for that threshold is asserted.

**Corollary 2 (the sparse near-linear regime).** Suppose
\(r_j\to\infty\), \(m_j/r_j\to c<\infty\), and
\(I(H_j)=o(r_j^2)\). Then
\[
 \limsup_j\frac{\tau(H_j)}{r_j}\le h(c)\le\frac{c}{1+c}.
 \tag{5}
\]
More generally the harmonic bound holds along a sequence with bounded
\(m_j/r_j\), without requiring convergence of that ratio.
Consequently, if \(\tau(H_j)/r_j\to1\) and
\(I(H_j)=o(r_j^2)\), then \(m_j/r_j\to\infty\).

The last assertion applies both to partite Ryser equality families
\(\tau\ge r-1\) and to nearly linear families in the unrestricted
Erdős--Lovász problem \(\tau=r\). It concerns a restricted class;
it does not contradict the unrestricted linear-in-\(r\) upper bounds
for the Erdős--Lovász problem, or decide the analogous general partite
conjecture.

**Theorem 3 (integer equality rigidity).** In the setting of Corollary 2,
suppose \(c=a\) is a positive integer and
\(\tau(H_j)/r_j\to a/(a+1)\). Let \(n_j\) be the number of active
vertices and \(d_j(v)\) their degrees. Then
\[
 \frac{n_j}{r_j^2}\longrightarrow\frac{a}{a+1},\qquad
 \sum_{v}(d_j(v)-a-1)^2=o(r_j^2). \tag{6}
\]
For every prime power \(a+1\) these conclusions are attained by the
explicit affine-geometric families in Section 7. The interval
\(0\le c\le1\) in (5) is also attained.

**Theorem 4 (noninteger obstruction to equality).** If \(c>1\) is not
an integer, no sequence in Corollary 2 can have
\(\tau(H_j)/r_j\to h(c)\). In fact for each such \(c\) there exists
\(\zeta_c>0\) such that every sequence in that corollary satisfies
\[
 \limsup_j\tau(H_j)/r_j\le h(c)-\zeta_c. \tag{7}
\]
An explicit, conservative choice is given in Section 6.1. It is not
claimed to be optimal. The full envelope is therefore a universal
bound with attained integer endpoints, rather than a claim of a sharp
frontier at every real ratio.

## 2. Published input and finite thresholds

We use Kahn's small-codegree hypergraph edge-colouring theorem in the
form stated in Kang--Kelly--Kühn--Methuku--Osthus [KKKMO, Theorem 3.1].
For every fixed rank \(D\) and \(\eta>0\), there is
\(\gamma>0\) such that a hypergraph of rank at most \(D\), maximum
degree at most \(A\), and maximum pair codegree at most \(\gamma A\)
has chromatic index at most \((1+\eta)A\). Their stated theorem gives
list colouring, of which ordinary colouring is a consequence.

The source explicitly allows parallel edge copies (Section 1.2):
distinct edge identities may have the same vertex set. Copies count
towards degrees and codegrees and cannot share a colour. This convention
is needed in Section 3. Choose an integer \(q_0=q_0(D,\eta)\ge2\)
such that \(D-1\le\gamma(q-1)\) for every \(q\ge q_0\).
Input K thus applies with the *upper bound* \(A=q-1\); it does not
require the actual maximum degree to equal this bound. Empty auxiliary
graphs cause no difficulty. We neither re-prove nor formalize Input K.

Peeling, pair-excess deletion and matching covers are related to the
tools in Sivashankar [S, Section 4]. The earlier partite notes in this
repository use replicated blocks with multiplicity \(d-3\). Here
multiplicity \(d-1\) bounds the replicated degree by \(q-1\) and
permits a counting argument without parts. None of the mathematical
claims in OpenAI/math are used as an input.

## 3. A bounded-degree residual lemma

Let \(J\) be intersecting and \(r\)-uniform, with \(q\) edges,
maximum vertex degree at most a fixed integer \(D\ge3\),
\(T=I(J)\), and \(n\) active vertices. Let \(x_d\) count its
degree-\(d\) vertices. Double counting gives
\[
 \sum d x_d=qr,\quad
 \sum\binom d2x_d=\binom q2+T,\quad
 \sum d^2x_d=q(q+r-1)+2T. \tag{8}
\]
Let \(g_d=(d-1)(d-2)/2\). The exact total weight is
\[
 F:=\sum g_d x_d=\binom q2+T-qr+n. \tag{9}
\]

View the \(q\) original edges as points. Every original vertex of
degree \(d\ge2\) defines its incidence block of size \(d\); retain
block identities, including repeated blocks. Their total pair excess
is exactly \(T\). Repeatedly delete a block containing a pair of
codegree at least two. The pair excess decreases by at least one per
deletion and never increases. After at most \(T\) deletions the
retained original blocks are linear. A deletion loses at most
\(g_D\) weight, so retained weight satisfies
\[
 F'\ge\binom q2-qr+n-(g_D-1)T. \tag{10}
\]
Only auxiliary blocks are deleted: original edges, their cover number
and the counts in (8) are not changed by this operation.

Replicate a retained size-\(d\) block \(d-1\) times and give each
copy weight \((d-2)/2\). Its total copy weight is exactly \(g_d\).
Since the original blocks are linear, the degree of a point in the
replicated system is
\(\sum_{B\ni p}(|B|-1)\le q-1\). Its pair codegree is at most
\(D-1\). Its rank is at most \(D\). Also
\[
 0\le F'\le\sum_B\binom{|B|}2\le\binom q2. \tag{11}
\]

For \(q\ge q_0\), Input K colours these copies with at most
\((1+\eta)(q-1)\) colours. If \(F'=0\), take the empty matching;
otherwise some class has weight at least
\(F'/((1+\eta)(q-1))\). That class is a matching of original blocks
and never uses two copies of the same block. Select the corresponding
original vertices and pair all remaining original edges. Each pair
has an intersection vertex. The matching saves \((d-2)/2\) per
size-\(d\) block over the pairing baseline; the rounding cost is at
most \(1/2\). From (10)--(11) it follows that
\[
 \tau(J)\le\frac{qr-n}{q-1}
       +(g_D-1)\frac{T}{q-1}+\frac{\eta q}{2}+\frac12.
 \tag{12}
\]
Indeed replacing the factor \(1/(1+\eta)\) by \(1\) costs at most
\(\eta F'/(q-1)\le\eta q/2\). This reasoning is valid also when
the lower bound in (10) is negative.

For every positive integer \(k\), the integer inequality
\((d-k)(d-k-1)\ge0\) gives
\[
 n\ge\frac{2kqr-q(q-1)-2T}{k(k+1)}. \tag{13}
\]
If \(q>r\), insert (13) into (12). The main terms are
\[
 r\left(\frac{k-1}{k+1}+\frac{q/r}{k(k+1)}\right),
\]
plus \(r(k-1)/((k+1)(q-1))\le1\). The excess coefficient is
\(g_D-1+2/(k(k+1))\le g_D\), and \(q-1\ge r\).
Minimizing over \(k\) gives
\[
 \tau(J)\le rh(q/r)+g_D\frac Tr+\frac{\eta q}{2}+B_0,
 \qquad B_0=q_0/2+2. \tag{14}
\]
For \(q\le r\), pairing gives
\(\tau(J)\le q/2+1/2=rh(q/r)+1/2\). For \(q<q_0\), pairing
gives \(\tau(J)\le q_0/2\). These cases justify (14) for *all*
\(q\ge0\); no colouring theorem is applied below its threshold.

For later use Cauchy--Schwarz applied to (8) gives a second lower bound:
\[
 n\ge\frac{q^2r^2}{q(q+r-1)+2T},\qquad q>0. \tag{15}
\]

## 4. Peeling and the envelope inequality

Select a vertex of current degree at least \(L=D+1\), delete its
current incident edges, and continue until the residual \(J\) has
maximum degree at most \(D\). Let \(b\) vertices have been selected
and \(q\) edges remain. Then
\[
 m\ge q+Lb,\qquad \tau(H)\le b+\tau(J),\qquad I(J)\le I(H).
 \tag{16}
\]
Deleting edges preserves intersecting uniformity; an empty residual
is covered by the conventions above. Since \(q\le m\le Cr\),
every slope of \(h\) on \([0,C]\) is at least
\(1/(K(K+1))=1/L\). Thus
\[
 \frac{m-q}{L}+rh(q/r)\le rh(m/r). \tag{17}
\]
Equivalently, restrict the minimum in (2) to \(1\le k\le K\):
each of these affine functions has slope at least \(1/L\), so their
minimum has the same lower slope bound. Now combine (14), (16), (17),
and choose \(\eta=2\varepsilon/C\). This proves (4) with
\(B_{C,\varepsilon}=q_0(D,2\varepsilon/C)/2+2\).

For clarity the breakpoints in (2) follow from
\[
 h_k(x)-h_{k+1}(x)=\frac{2(x-k)}{k(k+1)(k+2)}.
\]
Comparison with the harmonic curve is also exact:
\[
 \frac{x}{1+x}-h_k(x)
 =\frac{(x-k+1)(k-x)}{k(k+1)(1+x)},\quad k-1\le x\le k.
 \tag{18}
\]
Corollary 2 follows by dividing (4) by \(r\), using boundedness of
the edge/rank ratio, and then letting \(\varepsilon\downarrow0\).
If that ratio fails to tend to infinity while \(\tau/r\to1\),
there is a bounded-ratio subsequence, contradicting (5).

## 5. Integer equality and degree concentration

We first record a peeling fact used twice. Suppose \(m_j/r_j\to c\)
and \(\tau(H_j)/r_j\to h(c)\). Choose a fixed \(C>c\) and a
fixed \(D\) so large that
\(1/(D+1)<1/(K(K+1))\), with \(K=\max\{2,\lceil C\rceil\}\).
Run the degree-\(D+1\) peeling without depending on \(\eta\).
Apply (14) for this fixed \(D\) and arbitrary \(\eta>0\).
The strict version of (17) is
\[
 rh(m/r)-\left(\frac{m-q}{D+1}+rh(q/r)\right)
 \ge\left(\frac1{K(K+1)}-\frac1{D+1}\right)(m-q).
 \tag{19}
\]
Its coefficient is fixed and positive. Because \(I=o(r^2)\), first
take limits with \(D,\eta\) fixed, and then let \(\eta\downarrow0\).
Equality forces \(m-q=o(r)\), hence \(b=o(r)\), \(q/r\to c\),
and \(\tau(J)/r\to h(c)\). No uniformity of the colouring threshold
in \(D\) or \(\eta\) is required.

Now take \(c=a\) integer. Inequality (12), with arbitrarily small
fixed \(\eta\), implies
\[
 \limsup n(J)/r^2\le a-a\frac{a}{a+1}=\frac{a}{a+1}.
\]
Inequality (15) gives the reverse lower limit. Removing \(m-q=o(r)\)
edges can remove at most \(r(m-q)=o(r^2)\) active vertices, so the
original active-vertex count has the same limit. Finally the exact
identity on the original family is
\[
 \sum_v(d(v)-a-1)^2
 =m(m-1)+mr+2I-2(a+1)mr+(a+1)^2 n. \tag{20}
\]
Divide by \(r^2\) and insert the established limits. Its limit is
zero, proving (6).

## 6. Why equality fails between integer endpoints

Suppose instead \(k-1<c<k\) with \(k\ge2\), and assume equality
in (5). The peeling fact above and inequalities (12)--(13) imply
\[
 \frac{n(H)}{r^2}\longrightarrow
       \frac{c(2k-c)}{k(k+1)}.
\]
The lower limit uses (13), and the upper limit uses (12); passage
from residual to original vertices again costs at most \(r(m-q)\).
Using (8) on the original family, we obtain
\[
 \sum_v(d(v)-k)(d(v)-k-1)=o(r^2). \tag{21}
\]
All summands are nonnegative because degrees are integers. Call a
vertex bad if its degree is outside \(\{k,k+1\}\). For fixed \(k\),
both \(d^2\) and \(d|d-k|\), for bad positive integers \(d\), are
bounded by a fixed multiple of \((d-k)(d-k-1)\). To see this, the
ratio is bounded as \(d\to\infty\), and the remaining bad integers
form a finite set with strictly positive denominator. Therefore
\[
 \sum_{v\ {m bad}}d(v)^2=o(r^2),\qquad
 \sum_{v\ {m bad}}d(v)|d(v)-k|=o(r^2). \tag{22}
\]

Use the original \(m\) edges as auxiliary points and let \(Q\)
consist of the blocks of vertices of degree exactly \(k+1\). For
an original edge \(A\), write
\(i_A=\sum_{B\ne A}(|A\cap B|-1)\), so
\(\sum_A i_A=2I=o(r^2)\). Its degree in \(Q\) satisfies the exact
identity
\[
 d_Q(A)=m-1-(k-1)r+i_A-
                     \sum_{v\in A,\ v\ {m bad}}(d(v)-k).
 \tag{23}
\]
Consequently, with \(\theta=c-k+1\in(0,1)\),
\[
 \sum_A|d_Q(A)-\theta r|=o(r^2). \tag{24}
\]
This uses (22), \(\sum i_A=2I\), and \(m/r\to c\); it is an
\(L^1\) estimate, not an assertion that every point is regular.

The pair excess of \(Q\) is at most \(I(H)\). Delete at most
\(I(H)=o(r^2)\) blocks to make it linear, as in Section 3. This
changes the total degree sum by at most \((k+1)I=o(r^2)\), so
(24) still holds for the resulting \(Q'\). Each point has degree
at most \(r\), since its blocks correspond to vertices in one
original \(r\)-edge. Fix \(\xi>0\). Remove every block meeting a
point of degree greater than \((\theta+\xi)r\). By (24), there are
\(o(r)\) such points, and this removes \(o(r^2)\) blocks. The
remaining linear \((k+1)\)-uniform auxiliary graph has
\[
 \Delta\le(\theta+\xi)r,\qquad
 |E|=\frac{m\theta r}{k+1}+o(r^2),\qquad \Delta_2\le1.
 \tag{25}
\]

For fixed \(\eta,\xi>0\), Input K applies to (25) for all
sufficiently large \(r\). A largest colour class is a matching
of size at least
\[
 \frac{m\theta}{(k+1)(1+\eta)(\theta+\xi)}+o(r).
\]
Its defining original vertices, followed by pairing all remaining
original edges, give a cover of size at most
\(m/2-(k-1)|M|/2+1/2\). Let \(r\to\infty\) first and then
\(\eta,\xi\downarrow0\). It follows that
\[
 \limsup\tau(H)/r\le\frac{c}{k+1}<h(c),\qquad
 h(c)-\frac{c}{k+1}=\frac{(k-1)(k-c)}{k(k+1)}>0.
 \tag{26}
\]
This contradicts the assumed equality.

### 6.1 An explicit gap

For \(k-1<c<k\), \(k\ge2\), define
\[
 P=k(k+1),\quad\theta=c-k+1,\quad
 \Delta=\frac{(k-1)(k-c)}P,\quad
 A=2(k+2)P^2,\quad J=1+\frac{k+A(k+2)}{2\theta}.
 \tag{27}
\]
We can take
\[
 \zeta_c=(\Delta/J)^2>0. \tag{28}
\]
Here is a quantitative version of the previous argument. Pass to a
subsequence on which \(\tau(H)/r\to\alpha\) is its upper limit,
and put \(\delta=h(c)-\alpha\). Theorem 1 gives \(\delta\ge0\),
and \(\alpha\ge0\) gives \(\delta<1\). Fix the peeling threshold
\(D+1=2P\). For all sufficiently large indices, \(m/r<k\), and
every slope of \(h\) up to \(m/r\) is at least \(1/P\). The
residual bound (14), followed by \(\eta\downarrow0\), therefore
gives
\[
 \limsup (m-q)/r\le 2P\delta. \tag{29}
\]

We claim
\[
 \limsup n(H)/r^2\le c(1-h(c))+2P\delta. \tag{30}
\]
To verify it, pass further to a subsequence with
\((m-q)/r\to z\), so \(0\le z\le2P\delta\) and \(q/r\to c-z\).
Peeling gives \(\liminf\tau(J)/r\ge\alpha-z/(2P)\). If
\(c-z>0\), (12), again with fixed errors sent to zero after limits,
gives
\[
 \limsup n(J)/r^2\le(c-z)(1-\alpha+z/(2P)).
\]
Adding at most \(r(m-q)\) lost vertices bounds the original limit by
\(c-(c-z)(h(c)-\delta-z/(2P))\). This is at most
\[
 c(1-h(c))+(2c+2P h(c))\delta
 \le c(1-h(c))+2P\delta,
\]
because \(2c+2P h(c)=2k(k-1)+4c\le2P\). If \(c-z=0\), use
\(n(J)\le qr=o(r^2)\); the same bound follows by the same
expression with its zero factor. Subsequence selection proves (30).

The original integer degree polynomial now yields
\[
 \limsup\frac1{r^2}\sum_v(d(v)-k)(d(v)-k-1)\le2P^2\delta.
 \tag{31}
\]
For every bad positive integer degree,
\[
 d|d-k|\le(k+2)(d-k)(d-k-1).
\]
For \(d\ge k+2\), divide by \((d-k)(d-k-1)\): the ratio is
\(d/(d-k-1)\le k+2\). For \(d\le k-1\) the ratio is
\(d/(k+1-d)\le(k-1)/2\). Thus (23) gives
\[
 \limsup\frac1{r^2}\sum_A|d_Q(A)-\theta r|\le A\delta.
 \tag{32}
\]
Deleting the \(o(r^2)\) blocks needed for linearity changes (32) by
\(o(1)\) after normalization. For a fixed \(\xi>0\), the number
of points with degree above \((\theta+\xi)r\), divided by \(r\),
has upper limit at most \(A\delta/\xi\). Removing all their blocks
costs at most \((A\delta/\xi+o(1))r^2\) blocks. The remaining
linear \((k+1)\)-uniform graph has maximum degree at most
\((\theta+\xi)r\) and edge count with lower limit, divided by
\(r^2\), at least
\[
 \frac{c\theta-A\delta}{k+1}-\frac{A\delta}{\xi}.
\]
Colouring and pairing as before, and then letting the fixed colouring
error tend to zero, give
\[
 \alpha\le\frac{c}{k+1}+
 \frac{k-1}{2(k+1)}\,
 \frac{c\xi+A\delta(1+(k+1)/\xi)}{\theta+\xi}.
 \tag{33}
\]
This inequality remains valid if the edge-count lower bound is
negative: a matching of nonnegative size still satisfies that lower
bound.

If \(\delta=0\), send \(\xi\downarrow0\) in (33) to contradict
\(h(c)>c/(k+1)\). Otherwise choose \(\xi=\sqrt\delta\). Since
\(\delta<1\), \(c<k\), and \((k-1)/(2(k+1))\le1/2\), (33)
implies
\[
 \Delta\le\delta+
 \frac{k\sqrt\delta+A\delta+A(k+1)\sqrt\delta}{2\theta}
 \le J\sqrt\delta.
\]
Therefore \(\delta\ge(\Delta/J)^2\). This proves (7)--(28) for
every subsequential upper limit, hence for the original sequence.

## 7. Explicit equality families

Let \(s\) be a prime power and \(V=\mathbb F_s^N\), \(N\to\infty\).
For each one-dimensional direction, create a part consisting of all
affine lines in that direction. A point of \(V\) defines the edge
containing its line in every direction. Two distinct points lie on
exactly one common affine line. Thus the resulting hypergraph is
simple, intersecting, linear and partite, with
\[
 m=s^N,\quad r=\frac{s^N-1}{s-1},\quad
 n=r s^{N-1},\quad d(v)=s.
\]
Every original vertex covers exactly \(s\) edges, while all lines
in one parallel class cover the point set. Hence
\(\tau=s^{N-1}\), proving
\[
 m/r\to s-1,\qquad \tau/r\to(s-1)/s,
 \qquad n/r^2\to(s-1)/s.
\]
These families attain Theorem 3's integer endpoint and degree profile.

For any \(0<c\le1\), choose \(m/r\to c\) with \(r\ge m-1\).
Start with \(m\) edges indexed by \(1,\ldots,m\). Give each pair
\(i,j\) its own vertex incident only with edges \(i,j\), and add
private vertices to each edge until it has size \(r\). The family
is simple and linear, and every active vertex has degree at most two.
Thus \(\tau\ge\lceil m/2\rceil\); pairing attains this value.
It gives \(\tau/r\to c/2=h(c)\). The endpoint \(c=0\) follows,
for example, with bounded \(m\) and increasing \(r\). This last
construction need not be partite; no such requirement is made here.

## 8. Verification scope and remaining questions

The universal proof is Sections 2--6. The code supplies exact incidence,
block-deletion, replication and matching-cover diagnostics, including
nonpartite examples. Lean checks selected universal scalar identities
and inequalities, with the exact exported statements recorded in the
source. It does not formalize Input K, finite hypergraph covers, the
asymptotic arguments or the entire theorems. Hashes record the payload;
hash consistency itself is not mathematical verification.

The unresolved questions include the best gap in (7), the true
upper frontier between integer ratios, effective growth rates in the
near-linear Erdős--Lovász edge minimum, and the general nonlinear
partite minimum. The theorem supplies no bound when the excess is
uncontrolled and supplies no counterexample to Ryser's conjecture.

## References

[KKKMO] D. Y. Kang, T. Kelly, D. Kühn, A. Methuku and D. Osthus,
*Solution to a problem of Erdős on the chromatic index of hypergraphs
with bounded codegree*, Proceedings of the London Mathematical Society
**129** (2024), no. 6, e70011. Primary manuscript
<https://arxiv.org/abs/2110.06181>, Section 1.2 and Theorem 3.1
(Kahn's small-codegree theorem).

[K] J. Kahn, *Asymptotically good list-colorings*, Journal of
Combinatorial Theory, Series A **73** (1996), 1--59.

[S] V. Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*, 2026 preprint, <https://arxiv.org/abs/2606.24878v2>,
especially Section 4. The degree-peeling/linearization context is
attributed to that source; its degree-three residual lemma is not
used in this note.

[ABW] R. Aharoni, J. Barát and I. M. Wanless, *Multipartite hypergraphs
achieving equality in Ryser's conjecture*, Graphs and Combinatorics
**32** (2016), 1--15; <https://arxiv.org/abs/1409.4833>.

[Previous] Repository note *Near-linear Ryser equality families require
superlinear edge counts*, frozen at commit `ea1f13d`, and its cited
predecessors. The present statements drop the partite restriction,
strengthen the bounded-ratio cover gap, and address equality regimes.
