# The genuine least-prime profiles in the unchanged full completion

This is an addendum to the [adaptive first-three completion](Proof.md).
Here the **original full-completed arithmetic score is unchanged**:
we do not use the adaptive score, a smaller completion cutoff,
or the earlier fixed-payer score. The first-one and first-two
claims below take advantage of this fixed full completion. They
are different from the nonzero \(F_1,F_2\) when the *completion*
cutoff itself shrinks to W in the adaptive theorem.

Use the reciprocal [wide score](../wide_gap_all_terminal/Proof.md)
with \(N=2x\), \(L=\log x\), \(\ell=\log L\), \(J=xJ_0\subset[x,1.5x]\),
\(P=N-y\) an actual prime, and
\[
 \ell^{-2}\le\chi\le\ell^{-1},\qquad
 z=x^\chi,\qquad U=\ell^{-1/4},\qquad
 w=U/(100\log\ell),\qquad W=x^w .
\]
The distinct gate W is used **only** to restrict the first genuine
prime factors, not to select the cofactor weights. The actual
full completion cutoff remains \(C_y=y/x^{1-\epsilon}\).
Take \(0<\epsilon<.005\) fixed, or \(\ell^{-\alpha}\le\epsilon\le.005\)
for a fixed \(0<\alpha<1/8\).
Let \(\mathcal R^{\rm all}_{U,\epsilon}(y)\) be the actual full
score, with all the genuine cofactor weights below \(C_y\).

For \(k=1,2,3\), let \(\mathcal Y(p_1,\ldots,p_k)\) consist
of the true \(z\)-rough squarefree partners whose first
k actual prime factors, in increasing order, are exactly
\(p_1<\cdots<p_k\). Uniformly in the even target,
\[
 \sum_{z<p_1<\cdots<p_k\le W}
  \left|
    \sum_{\substack{y\in J\cap\mathcal Y(p_1,\ldots,p_k)\\
                              P=N-y\ {\rm genuine\ prime}}}
         \log P\,\mathcal R^{\rm all}_{U,\epsilon}(y)
  \right|
    \ll_{J_0} \epsilon^{-2}w^k x\mathfrak S(N)
         +O_{A,\alpha,J_0}(x\mathfrak S(N)\ell^{-A})              \tag{1}
\]
for each fixed A, with fixed \(\epsilon\) allowed throughout.
In particular already \(k=1\) removes the **entire signed score**
on genuine y with an actual prime in \((z,W]\), at
\(o(x\mathfrak S(N))\) cost. Thus the remaining actual signed score
may be restricted to \(P^-(y)>W\), although its full cofactor
cutoff remains \(C_y\). This holds for the whole signed class,
not its unsigned contributions or a separate exterior/safe
piece. It does not sign the fully W-rough residual.

## 1. Exact conditioning and literal prime progressions

Use the pinned-prime argument from [the main note, §1](Proof.md),
now with \(k=1,2,3\) actual least tags.
Write \(v=\log p_k/L\), \(e=\log C_y/L\), \(A=p_1\cdots p_k\).
For an actual subset I of the pinned tags in the short divisor
\(d=A_I s\), put \(j=\log A_I/L\) and \(D_y=\log y/(2L)-U\).
Then \(s\le x^{D_y-j}\), and when \(y=A s b\) both the
remaining s and the free b are \(x^v\)-rough, **not**
\(C_y\)-rough. This is exactly the actual first-k predicate.
Every selected tag is \(<C_y\) eventually, since \(w<e\).

The genuine remaining short small product is
\(S_s=\prod_{p'\mid s,\ p'<C_y}p'\).
The full free coefficient for I is exactly
\[
                 (-1)^{|I|}\mu(S_s)(\log s-2\log S_s-Lj).
\]
For fixed s this weight can change only at actual y positions
\(p'x^{1-\epsilon}\) for primes \(p'\mid s\), with \(O(L)\)
thresholds and total variation \(O(L^2)\). This fits the maximal
prefix reserve and is not an assumption about marks in b.
The short raw coefficient is
\((-1)^{|I|}\mu(s)(\log y-Lj-\log s)\).

Open the free roughness with the dimension-one fundamental lemma
only to \(x^v\). On sieve support \(h\le x^{U/2}\) the genuine
prime modulus, including the pinned tags on **either** leg,
is \(A s h\), at most
\(\sqrt{1.5x}\,x^{-U/2+3w}\).
The density is \(1/p'\) at a sieve prime dividing the pinned A,
\(1/(p'-1)\) otherwise, and zero at primes dividing N, just as
in the main note. The first of these is a real repeated-modulus
prime, not a mistaken coprimality factor; its Euler correction
is \(1+O(z^{-2})\).
Ordinary maximal weighted BV has arbitrary-log margin, including
all divisor multiplicities, actual parameter cutoffs and masks.
Squareful rough y and nonunit target rows are negligible as before.

The unsigned harmonic main over pinned tags costs at most
\(O(x\mathfrak S(N)\chi^{-2}(1+\log\ell)^3)\), using actual
reciprocal prime tags, residual r-rough harmonics and \(O(L)\)
weights. The smallest fundamental-lemma parameter is now
\(U/(2w)=50\log\ell\), so its relative error saves every fixed
power of \(1/\ell\) even after this envelope. Upper/lower
replacement applies per sign; the actual \(\ell^1\) sum of
the errors over pinned tuples satisfies the error term in (1).
After the true AP mean is extracted the short raw \(\mu(s)\) moments
give the same constant in every allocation before its
\((-1)^{|I|}\) sign, by (6) of the main note. For every \(k\ge1\)
that constant sums to zero, and the uniform tails contribute
only the error term in (1). No binary prime y occurs in any family.

## 2. Fixed full harmonic and the short k-th difference

Write \(\nu_a=1_{u>a}du/u\) on nonnegative exponents.
Let \(Q_e\) be the cumulative of \(\exp^*(2\nu_e)\) and \(q_e\)
the density of its non-atomic part.
The signed harmonic of the actual residual small weight
\(\mu(S_s)\) has continuum cumulative
\[
 A_{v,e}(t)=\rho(t/v)+\int_0^t\rho(u/v)\,q_e(t-u)\,du,
\]
from \(\exp^*(-\nu_v+2\nu_e)\).
The log-mark harmonic divided by L is
\(B_{v,e}(t)=\int_0^{t-v}A_{v,e}(u)\,du\), since the true mark
on each allowed prime is its own sign times its logarithm,
making the marked measure positive \(1_{u>v}du\).
The quantitative replacement including the actual squarefree
tuples, the unit atom and the moving cutoff is precisely the
[prime-harmonic lemma](../completed_gap_two_true_sectors/Proof.md).
Only a variable interval endpoint moves; this costs no new
assumption on the true prime P.

For clarity about all possible piecewise-density walls, a
marked slot in the convolution exponential gives the exact
identity \(t q_e(t)=2Q_e(t-e)\) for \(t>e\).
The right side is smooth up to \(j\) derivatives when
\(t>(j+1)e\): first note that \(Q_e\) is continuous away
from its atom at zero, then iterate the identity after one
differentiation with \(Q'_e=q_e\). On the intervals
\(t\in[.3,.7]\), for \(j\le3\), the recursion stays
bounded away from zero in each denominator, even at a
threshold resonance \(t=ne\) for larger n.
Since \(Q_e(t)\ll e^{-2}\) on \(t\le1\) by its positive
Euler harmonic bound, this proves
\(\|q_e^{(j)}\|_\infty\ll_j e^{-2}\) there.
Crude global density \(O(e^{-3})\) on \([0,1]\)
follows from the same mark identity, as \(q_e=0\) for \(t<e\).

On a fixed neighborhood of \(D_y\), restrict the
convolution in \(A_{v,e}\) to \(u\) below a sufficiently
small fixed positive constant. The \(\rho(t/v)\) term
and discarded tail save every \(1/\ell\) power uniformly
because \(v\le w\), even after the global polynomial
\(e^{-3}\) cost in the moving range.
The retained smooth approximation and its first three
derivatives cost \(O(v e^{-2})\), from
\(\int\rho(u/v)\,du=e^\gamma v\).
Obtain the analogous local smooth approximation to
\(B_{v,e}\) using its derivative \(A_{v,e}(t-v)\) and
a common constant. No derivatives of the discarded
tail need to be taken.

Thus the actual allocation function, divided by L,
\[
                 G(j)=B_{v,e}(D_y-j)-jA_{v,e}(D_y-j)
\]
is approximated at all \(2^k\) endpoints by a smooth
function with any of its first k derivatives bounded by
\(O(v e^{-2})\). In particular the third derivative of
\(jA(D_y-j)\) is \(3A''(D_y-j)-jA'''(D_y-j)\);
the lower derivatives obey the same bound.
Taking the k-th signed finite difference costs
\(O(v e^{-2}\prod_{i=1}^k(\log p_i/L))\).
The fundamental theorem of calculus yields this bound by
integrating the k-th derivative over the actual k interval lengths.
The genuine prime AP model has factor
\(L V_N(x^v)/A\ll\mathfrak S(N)/(vA)\),
so v cancels. Finally
\((\sum_{z<p\le W}(\log p)/(pL))^k\ll w^k\)
by actual prime Mertens, and \(e\asymp\epsilon\) uniformly
on J. These estimates prove (1), including its absolute
values over the pinned tuples and the moving-\(\epsilon\)
range stated above. For the least-prime case,
\(\epsilon^{-2}w=o(1)\) on that range.
No comparison on a signed subset of the outer pairs,
nor any conjectural target-wise positivity, is used.
