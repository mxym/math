# Two-eigenvalue APPT purity in all dimensions and an absolutely separable polytope

## 1. Scope and notation

Let `2 <= m <= n`, `D=mn`, and let `Gamma` be partial transpose in the second
factor of `C^m tensor C^n`. A density matrix is positive semidefinite and has
trace one. It is **absolutely PPT (APPT)** when `(U rho U*)^Gamma` is positive
semidefinite for every global unitary `U`. It is **absolutely separable (AS)**
when every such conjugate is a convex combination of product states.

Write `p(rho)=Tr(rho^2)`. For the purity results below assume `m >= 3`, and set

\[
R=\frac{m(m-1)}2,\quad S=\frac{m(m+1)}2,\quad
 t=\left\lceil\frac{(m-1)n}2\right\rceil,
\]
\[
P_1=\frac{D+8}{(D+2)^2},\qquad
P_t=\frac{D(m-1)^2+4mt}{[D(m-1)+2t]^2},\qquad M=\max(P_1,P_t).
\]

These candidate values and spectra are not new predictions: they are the
maximum of the inscribed polytope in [AKW, Theorem 6.3]. Conjecture 6.7 there
asserts the same value for the entire APPT set. We prove this maximum for all
two-eigenvalue spectra, together with an additional multi-level subclass.
We do not assume the full conjecture or that a maximizer has two eigenvalues.

**Theorem A (all multiplicities, two eigenvalues).** For every `3 <= m <= n`,

\[
\max\{p(\rho):\rho\text{ is APPT and has at most two distinct eigenvalues}\}=M.
\]

The possible maximizing spectra within this class are precisely the following
families whose displayed purity equals `M`:

\[
\frac{(3,1,\ldots,1)}{D+2},\qquad
\frac{(\underbrace{m+1,\ldots,m+1}_{t},
\underbrace{m-1,\ldots,m-1}_{D-t})}{D(m-1)+2t}.
\]

**Theorem B (few eigenvalues above a flat minimum).** Every APPT density matrix
whose smallest eigenvalue has multiplicity at least `D-m+1` has purity at most
`P_1`. Equality holds exactly at the rank-one-spike spectrum above.

**Theorem C (inner-polytope absolute separability).** For every `2 <= m <= n`,
let `P_{m,n}` be the permutation-invariant spectral polytope whose ordered
section satisfies

\[
2\lambda_D+\sum_{j=1}^{m-1}\lambda_{D-j}
 \ \geq\ \sum_{j=1}^{m-1}\lambda_j.
\tag{1}
\]

Every density matrix with spectrum in `P_{m,n}` is AS. This is a deduction using
the two established separability criteria stated in Section 6, not a claim
of a new separability criterion replacing them.

## 2. Physical test vectors and two-level purity

For a unit vector in Schmidt form

\[
\psi=\sum_{i=1}^{m}s_i|ii\rangle,\qquad s_i\geq0,\quad \sum_i s_i^2=1,
\]

the Hermitian matrix `W_psi=(|psi><psi|)^Gamma` has eigenvectors `|ii>` with
values `s_i^2`, the symmetric and antisymmetric vectors
`(|ij> +/- |ji>)/sqrt(2)` with values `+/- s_i s_j`, and zero on the remaining
product-basis coordinates. This follows directly by transposing matrix units.
In particular `Tr W_psi=1`.

Partial transpose is self-adjoint for the trace pairing. Thus

\[
\langle\psi,(U\rho U^*)^\Gamma\psi\rangle
 =\operatorname{Tr}(U\rho U^*W_\psi).
\tag{2}
\]

All projections of a given rank are unitarily conjugate. Consequently, if
`rho=b I+(a-b)P`, `a>b>=0`, and `rank P=k`, its APPT property implies

\[
b+(a-b)\operatorname{Tr}(P'W_\psi)\geq0
\tag{3}
\]

for every rank-`k` projection `P'` and every unit `psi`. Conversely, positivity
of these expressions for all such `P'` and all `psi` is exactly APPT.
This uses the actual unitary orbit, not an assumed spectral characterization.
It suffices to express arbitrary test vectors in Schmidt bases, because those
bases can be absorbed into the global unitary in (2).

If `b>0`, put `c=(a-b)/b`. Trace normalization gives

\[
p(\rho)=F_+(D,k,c)
 =\frac{D+2kc+kc^2}{(D+kc)^2}
 =\frac1D+\frac{k(D-k)c^2}{D(D+kc)^2}.
\tag{4}
\]

For `0<k<D`, this is increasing in `c>=0`, strictly so for `c>0`, since

\[
\partial_c F_+=\frac{2k(D-k)c}{(D+kc)^3}.
\tag{5}
\]

For the complementary parametrization let `l=D-k`, `a>0`, and
`delta=(a-b)/a`, so `0<delta<=1` and `rho=a(I-delta Q)` with `rank Q=l`.
Then

\[
p(\rho)=F_-(D,l,\delta)
 =\frac{D-2l\delta+l\delta^2}{(D-l\delta)^2}
 =\frac1D+\frac{l(D-l)\delta^2}{D(D-l\delta)^2}.
\tag{6}
\]

This is increasing in `delta>=0`, with derivative
`2l(D-l)delta/(D-l delta)^3`. All denominators here are positive, including
when the least eigenvalue is zero: `D-l delta >= D-l > 0`.

## 3. Few high eigenvalues: 1 <= k < R

We need an elementary graph construction, not a graph spectral-radius
classification.

**Lemma 3.1.** If `1<=k<m(m-1)/2`, there are exactly `k` distinct pairs of
indices from `{1,...,m}` and a nonnegative unit vector `s` such that

\[
\sum_{\{i,j\}\in E}s_i s_j\geq\frac{\sqrt{k}}2.
\tag{7}
\]

**Proof.** For `k=1` use one edge and amplitudes `(1,1)/sqrt(2)`. For `k=2`
use a two-edge star with amplitudes `(1/sqrt(2),1/2,1/2)`. For `k=3`, use a
triangle with equal amplitudes on its vertices. For `k=4`, use that triangle
and one further edge to a zero-amplitude vertex. The latter case has `m>=4`
because `k<R`. These sums are `1/2`, `sqrt(2)/2`, `1`, and `1`, respectively.
For `k=5`, use five edges on four equal-amplitude vertices; the sum is `5/4`,
which is at least `sqrt(5)/2`.

For `k>=6`, let `q` be the largest integer with `q(q-1)/2<=k`. We have `q>=4`
and `q<=m-1`. Take a complete graph on `q` vertices, add arbitrary further
edges to obtain exactly `k` edges, and put amplitude `1/sqrt(q)` on those
`q` vertices and zero elsewhere. The edge sum is at least `(q-1)/2`.
Maximality gives `k<=q(q+1)/2-1`, while

\[
(q-1)^2-\left(\frac{q(q+1)}2-1\right)
 =\frac{(q-1)(q-4)}2\geq0.
\]

This proves (7). There are enough extra edges since `k<R`. QED.

Choose in (3) the projection onto the `k` antisymmetric vectors indexed by
these edges. APPT implies

\[
b\geq (a-b)\frac{\sqrt{k}}2.
\tag{8}
\]

In particular `b>0` for a nonzero normalized state. Thus `c<=2/sqrt(k)` and
(4)--(5) give

\[
p(\rho)-\frac1D
\leq\frac{4(D-k)}{D(D+2\sqrt{k})^2}
\leq\frac{4(D-1)}{D(D+2)^2}=P_1-\frac1D.
\tag{9}
\]

The second inequality is strict when `k>1`: its numerator strictly decreases
and its positive denominator strictly increases. Equality for `k=1` requires
`c=2`, which is exactly the first spectrum in Theorem A.

## 4. Intermediate multiplicities: R <= k <= D-S

Use a maximally entangled Schmidt-rank-`m` vector. Its partially transposed
projector has `R` negative eigenvalues `-1/m`, `S` positive eigenvalues `1/m`,
and `D-m^2` zeros. Put all `R` negative eigenvectors and `k-R` zero
vectors in `P'`; the hypothesis on `k` is exactly what permits this. Equation
(3) gives

\[
b\geq\frac{m-1}{2}(a-b),\qquad c\leq\frac2{m-1}.
\tag{10}
\]

Again `b>0`. This contrast bound is also sufficient, in every rank. Indeed,
for an arbitrary unit Schmidt vector the total magnitude of the negative
eigenvalues of `W_psi` is

\[
\sum_{i<j}s_i s_j=\frac{(\sum_i s_i)^2-1}{2}\leq\frac{m-1}{2}.
\]

For any projection `P'`, `Tr(P' W_psi)` is at least the sum of all negative
eigenvalues: writing `W_psi` in an orthonormal eigenbasis reduces this to
weights in `[0,1]`. Consequently (10) implies (3) for every physical test.

At the largest permitted contrast the purity is

\[
f(k)=\frac{D(m-1)^2+4mk}{[D(m-1)+2k]^2},\qquad
f'(k)=\frac{4m[(m-1)n-2k]}{[D(m-1)+2k]^3}.
\tag{11}
\]

The continuous maximum is at `k_*=(m-1)n/2`. It lies in `[R,D-S]`; more
precisely, `k_*-R=(m-1)(n-m)/2` and
`D-S-k_*=(m+1)(n-m)/2`. Its ceiling also lies in this interval: when `n=m`
these are equal integer endpoints; otherwise the right margin is at least 2.

The only possible integer maximizers are the floor and ceiling of `k_*`.
If they differ, put `H=(m^2-1)n`. Direct arithmetic gives

\[
f(\lceil k_*\rceil)-f(\lfloor k_*\rfloor)
 =\frac{4m}{(H^2-1)^2}>0.
\tag{12}
\]

Hence the unique integer maximizing rank is `t=ceil(k_*)`, and this regime
has exact maximum `P_t`. Strictness of (5) supplies the stated equality
conditions on the contrast.

## 5. Many high eigenvalues: k > D-S

Set `l=D-k`, so `1<=l<S`, and use (6). For a maximally entangled
Schmidt-rank-`q` vector, with `1<=q<=m`, the positive eigenvalues of `W_psi`
are `q(q+1)/2` copies of `1/q`. Put as many of them as possible in `Q'` and,
if necessary, pad with zeros. There are enough nonnegative eigenvectors:

\[
l<S\leq D-\frac{q(q-1)}2,
\]

where the non-strict inequality follows from `D>=m^2` and `q<=m`.
The APPT test `1-delta Tr(Q'W_psi)>=0` therefore gives

\[
\delta\,\frac{\min\{l,q(q+1)/2\}}q\leq1.
\tag{13}
\]

Let `r` be the smallest positive integer with `l<=r(r+1)/2`. Thus
`r(r-1)/2<l<=r(r+1)/2`, and `r<=m`.

### 5.1 The main tail range r >= 3

Taking `q=r` and `q=r-1` in (13) yields

\[
\delta\leq\min\{r/l,2/r\}.
\tag{14}
\]

For `l<=r^2/2`, use `delta<=2/r`. The function
`h(l)=l(D-l)/(rD-2l)^2` has positive derivative on this interval: its numerator
is `D[rD-2(r-1)l]`, and `D>=m^2>=r^2` makes this strictly positive. For
`l>=r^2/2`, use `delta<=r/l`; the resulting expression
`r^2(D-l)/[D l(D-r)^2]` decreases with `l`. Evaluating both bounds at `r^2/2`
(which need not be an integer) gives

\[
p(\rho)\leq\frac1D+\frac{2D-r^2}{D(D-r)^2}.
\tag{15}
\]

Here `D-r>0`, since `r>=3` and `D>=r^2`. This upper bound is strictly below
`P_1`. Indeed its difference from `P_1` is

\[
\frac{B(D,r)}{(D-r)^2(D+2)^2},\quad
B(D,r)=2D^2+(r^2-8r-12)D+8r^2+8r-8.
\tag{16}
\]

With `D=r^2+x` and `r=3+y`, `x,y>=0`, the numerator is exactly

\[
2x^2+5xy^2+22xy+9x+3y^4+28y^3+86y^2+92y+7>0.
\tag{17}
\]

This explicit positive-coefficient identity proves (16) in the entire
unbounded parameter range; no finite testing is needed for the implication.

### 5.2 The small tail ranges

For `l=1`, the unconstrained bound `delta<=1` already gives
`p(rho)<=1/(D-1)<P_1`, using

\[
P_1-\frac1{D-1}=\frac{3(D-4)}{(D-1)(D+2)^2}>0.
\]

If `r=2`, then `l=2` or `l=3`. For `l=3`, (13) with `q=2` gives
`delta<=2/3`, whence `p(rho)<P_1` because

\[
P_1-\frac{D-8/3}{(D-2)^2}
 =\frac{8(D-4)^2}{3(D-2)^2(D+2)^2}>0.
\]

For `l=2` and `D>=12`, the bound `delta<=1` gives `p(rho)<=1/(D-2)`, and

\[
P_1-\frac1{D-2}=\frac{2(D-10)}{(D-2)(D+2)^2}>0.
\]

The only remaining product dimension under `3<=m<=n` is `D=9`.
For this case choose Schmidt coefficients `(2,1,0)/sqrt(5)`. The two largest
positive eigenvalues of `W_psi` are `4/5` and `2/5`, so (2) with a rank-two
`Q'` gives `delta<=5/6`. Exactly,

\[
F_-(9,2,5/6)=\frac{127}{968}
 <\frac{136}{968}=P_1.
\tag{18}
\]

This handles every high-multiplicity case, including rank-deficient states.

### 5.3 Attainment and completion of Theorem A

For any unit vector `v`, `(I+2|v><v|)/(D+2)` is APPT. Under any global unitary
its rank-one part is still a unit-vector projector, and every such partially
transposed projector has least eigenvalue at least `-1/2`, since `2s_i s_j<=1`.
Its trace-square is `P_1`.

For any rank-`t` projection `P`, the state

\[
\frac{I+\frac2{m-1}P}{D+\frac{2t}{m-1}}
\]

is APPT by the sufficient estimate following (10), and its purity is `P_t`.
Thus both candidates are genuine states, without an assumed APPT equivalence.
Equations (9), (11)--(12), and the strict high-tail bounds prove Theorem A,
including its equality classification. The uniform state has purity `1/D`,
strictly smaller than both candidates. QED.

## 6. Proof of Theorem B and the absolutely separable polytope

### 6.1 An additional multi-level class

Suppose the least eigenvalue `b` has multiplicity at least `D-m+1`. Write

\[
\rho=bI+\sum_{j=1}^{k}d_jP_j,\quad d_j>0,\quad k\leq m-1,
\]

where the `P_j` are orthogonal rank-one projections. If `k=0`, the state is
maximally mixed and the desired bound is strict; hence assume `k>=1`. Put these projections
on the antisymmetric Schmidt pairs `{0,j}`. If `Q=sum_j d_j^2>0`, choose
Schmidt amplitudes `s_0=1/sqrt(2)` and `s_j=d_j/sqrt(2Q)`. Equation (2) gives

\[
b-\frac{\sqrt Q}{2}\geq0.
\]

This also proves `b>0` unless the state is zero, which trace normalization
excludes. Let `x_j=d_j/b`, `q=sum_j x_j^2<=4`, and `s=sum_j x_j`. Then

\[
p(\rho)=\frac{D+2s+q}{(D+s)^2},\qquad s\geq\sqrt q.
\]

For fixed `q`, differentiation in `s` gives `-2(s+q)/(D+s)^3<=0`. Replacing
`s` by `sqrt(q)` and using (5) with `k=1` proves `p(rho)<=P_1`.
Equality requires `q=4` and `s^2=q`, so at most one `x_j` is nonzero. Thus
only the rank-one spike attains equality. This proves Theorem B. QED.

### 6.2 Two external separability inputs

We use exactly the following established sufficient conditions:

- The **Gurvits--Barnum ball**: a bipartite density matrix of total dimension
  `D` with purity at most `1/(D-1)` is separable [GB]. Since purity is unitary
  invariant, every such matrix is AS.
- The **spectral-ratio criterion** [Kondra+26, Supplemental Lemma 2]: a bipartite
  density matrix with `lambda_max/lambda_min <= (m+1)/(m-1)` is separable,
  where `m` is the smaller local dimension. The minimum eigenvalue is positive
  here. Because the condition is spectral, it also implies AS.

Both are used as cited mathematical theorems. They are not Lean-formalized
in this continuation. For the third ingredient we provide an explicit proof.

### 6.3 Pure spikes are absolutely separable, explicitly

Let `v=sum_i s_i |ii>` be a unit Schmidt vector of rank `q<=m`. Independently
let each `omega_i` range over the three cube roots of unity, and define

\[
z_\omega=\left(\sum_i\sqrt{s_i}\,\omega_i|i\rangle\right)
 \otimes\left(\sum_j\sqrt{s_j}\,\overline{\omega_j}|j\rangle\right).
\]

Orthogonality of the characters of `(Z/3Z)^q` gives the finite average

\[
\frac1{3^q}\sum_\omega |z_\omega\rangle\langle z_\omega|
 =|v\rangle\langle v|+\sum_{i\ne j}s_i s_j|ij\rangle\langle ij|.
\tag{19}
\]

For completeness, the coefficient of `|ij><kl|` survives exactly when
`e_i-e_j-e_k+e_l` is zero modulo 3. Each coordinate of this integer vector is
between `-2` and `2`, so this is equivalent to equality over the integers.
The surviving cases are `i=j,k=l` or `i=k,j=l`, with their overlap counted
only once. This proves (19), including zero Schmidt coefficients.

Now subtract twice the diagonal correction from the identity. The remaining
coefficients are `1-2s_i s_j>=0` for `i!=j`, `1` on `|ii>`, and `1` on
product-basis coordinates outside the Schmidt support. Thus `I+2|v><v|` is
an explicit sum of positive product projectors. Normalization proves that
the rank-one spike is separable for every unit `v`, hence AS. Local Schmidt
basis changes preserve this product decomposition.

### 6.4 All vertices of the polytope are AS

The vertices of the ordered probability simplex are
`u_k=(1/k,...,1/k,0,...,0)`. Let `h(lambda)` be the left side of (1) minus
the right side. Direct summation gives

\[
h(u_D)=2/D,\quad h(u_{D-1})=0,
\]
\[
h(u_k)=
\begin{cases}
-1,&1\leq k\leq m-1,\\
-(m-1)/k,&m\leq k\leq D-m,\\
-(D-k-1)/k,&D-m+1\leq k\leq D-2.
\end{cases}
\tag{20}
\]

Empty ranges are simply omitted. Cutting a simplex by a single halfspace
introduces vertices only on its edges. Here the nonnegative old vertices are
`u_D` and `u_{D-1}`; new vertices are the intersections of `[u_k,u_D]` with
`h=0`, `1<=k<=D-2`. This also follows by noting that a vertex of the cut simplex
in barycentric coordinates has at most two nonzero coordinates unless the cut
constraint is inactive. Edges ending at `u_{D-1}` contribute no new point.

The resulting spectra have two levels `a` (multiplicity `k`) and `b`
(multiplicity `D-k`):

* If `k<=m-1`, they are `(I+(2/k)P_k)/(D+2)`. This is the average of `k`
  rank-one-spike states from Section 6.3, and is therefore AS for every
  eigenspace, even an entangled one.
* If `m<=k<=D-m`, their eigenvalue ratio is `(m+1)/(m-1)`, so [Kondra+26] applies.
* If `k=D-l` with `2<=l<=m-1`, their levels are
  `a=(l+1)/[D(l+1)-2l]` and `b=(l-1)/[D(l+1)-2l]`. Their purity lies in the
  separable ball, as witnessed by the exact identity

\[
\frac1{D-1}-F_-(D,l,2/(l+1))
 =\frac{D(l-1)^2}{(D-1)[D(l+1)-2l]^2}\geq0.
\tag{21}
\]

The retained vertex `u_{D-1}` is on the separable-ball boundary and `u_D` is
maximally mixed. All vertices are thus AS. The AS set is convex and invariant
under global unitary conjugation. Taking convex combinations in a common
eigenbasis proves Theorem C for the ordered section, and permutations prove
it for the whole polytope. QED.

In particular, the maximum purity over **two-eigenvalue AS states** also equals
`M` for `m>=3`, because AS implies APPT and both attaining spectra in Theorem A
are AS. Equal maxima do not establish equality of the two full state sets.

## 7. A precise obstruction to an insufficient relaxation

Equal-amplitude Schmidt vectors of every rank `2<=q<=m` imply the necessary
spectral inequalities

\[
\sum_{i=1}^{q(q-1)/2}\lambda_i
 \leq\sum_{i=D-q(q+1)/2+1}^{D}\lambda_i.
\tag{22}
\]

They are not sufficient, even jointly. Consider

\[
\lambda=\frac{(3,2,1,\ldots,1)}{D+3},\qquad 3\leq m\leq n.
\]

For `q=2`, both unnormalized sums in (22) equal 3. For `q>=3`, the high
sum is `q(q-1)/2+3`, the low sum is `q(q+1)/2`, and the difference is `q-3>=0`.
Thus (22) holds for every allowed rank.

Nevertheless this spectrum is not APPT. Let `P_01` and `P_02` project onto
`(|01>-|10>)/sqrt(2)` and `(|02>-|20>)/sqrt(2)`. The state
`rho=(I+2P_01+P_02)/(D+3)` has that spectrum. For
`psi=(2|00>+2|11>+|22>)/3`, equation (2) yields exactly

\[
\langle\psi,\rho^\Gamma\psi\rangle
 =\frac{1-2(4/9)-2/9}{D+3}=-\frac1{9(D+3)}<0.
\tag{23}
\]

For example, in `m=n=4`, its purity is `27/361`, which exceeds the conjectured
maximum `2/27` by `7/9747`, despite satisfying every inequality (22).
This is a counterexample to the **relaxation**, not to the APPT conjecture.
It identifies why a proof using only maximally entangled test vectors would
be invalid. Unequal Schmidt amplitudes are essential.

## 8. Remaining global obligation and provenance

Theorem A does not imply that every APPT state is a convex combination of
APPT states with two eigenvalues. That representation has not been proved
here, and known curved boundaries make it inappropriate to assume it.
Theorem B excludes another large class but still leaves spectra with three
or more levels and a smaller least-eigenvalue multiplicity. A proof or exact
counterexample in that remaining class is required for the general conjecture.

The results are analytic. `check.py` checks only supporting exact polynomial
identities, explicit coefficient signs, discrete rank arithmetic, and the
finite character identity. Its bounded regression sweep is clearly separated
from the unbounded arguments above. No optimizer output is a premise.
The checker rejects a changed constant in (17); failure of that control for
an unrelated reason would not validate the certificate.

This continuation makes no blanket priority claim. The two candidate spectra
and the conjectured formula are credited to [AKW]. The polytope containment
uses the pre-existing [GB] and [Kondra+26] criteria. The completed qutrit proof and
its published preprint are separate fixed artifacts; they do not certify
Theorems A--C of this new note in Lean.

## References

[AKW] Jennifer Ahiable, Naga Bhavya Teja Kothakonda, Andreas Winter,
*The geometry of absolute separability and other convex matrix properties from
spectrum*, arXiv:2608.03390v1 (4 August 2026), Theorems 6.2--6.3, Conjecture
6.7, and Section 7. https://arxiv.org/html/2608.03390v1

[Kondra+26] Tulja Varun Kondra, Pedro Barrios Hita, Justus Neumann, Hermann Kampermann,
Dagmar Bruß,
*Fundamental limitations on entanglement extraction from purity*,
arXiv:2605.29197v1 (2026), Supplemental Lemma 2.
https://arxiv.org/html/2605.29197v1

[GB] Leonid Gurvits, Howard Barnum, *Largest separable balls around the maximally
mixed bipartite quantum state*, Physical Review A 66, 062311 (2002),
arXiv:quant-ph/0204159. https://arxiv.org/abs/quant-ph/0204159
