# Eleven-point quartic symmetry breaking: the sharp transitive value and a connected counterexample

For a spherical $60^\circ$ code $X$, let
\[
 h(X)=\min_{p_i\geq0,\,\sum p_i=1}\sum_{i,j}p_i p_j f(x_i\cdot x_j),\qquad f(t)=t^4-t^2/4 .
\]
This measures a weighted quartic interaction, not the maximum possible number of kissing points or the optimal minimum angle of an eleven-point set.

**Theorem.** Across **all dimensions**, the maximum of $h(X)$ among point-transitive eleven-point codes is
\[
 H_{11}=0.13060126556\ldots .
\]
Up to isometry there is exactly one maximizing point set. It consists of two real Fourier planes and spans dimension four. A six-dimensional **nontransitive** code satisfies $0.13091705<h(X)<0.13091707$, even though its strict graph (inner product below $-1/2$) is connected and factor-critical. Thus unrestricted optimizers in every dimension at least six cannot be geometrically point-transitive. The exact unrestricted optimum is **not** determined.

**A separate unweighted consequence.** For any ordered eleven-point kissing code in any dimension, the mean of $-x_i\cdot x_{i+1}$ around the cycle is at most $0.85379942850\ldots$. Equality forces exactly the same ordered rank-four configuration up to isometry. The sharp minimum consecutive-edge strength has the same value. These are mean and minimum statements about eleven consecutive pairs; the stronger transitive claim above is about all 121 ordered pairs and optimized weights.

## The algebraic winner

Put $V_{jk}=\cos(2\pi jk/11)$ for $1\le j\le5$ and $0\le k\le5$. Define
\[
 a=\frac{1/2-V_{24}}{V_{25}-V_{24}},\qquad x_j=(1-a)V_{j4}+aV_{j5}.
\]
Then $0<a<1$, $x_2=1/2$, $-0.854<x_1<-0.853$ and $|x_3|,|x_4|,|x_5|<0.14$. The stated sharp constants are exactly
\[
 H_{11}=\frac{3/4+2\sum_{j=1}^5 f(x_j)}{11},\qquad A_{11}=-x_1 .
\]
Unit vectors realizing these lags are indexed by $s\in\mathbb Z/11$:
\[
 \big(\sqrt{1-a}\cos(8\pi s/11),\,\sqrt{1-a}\sin(8\pi s/11),\,
 \sqrt a\cos(10\pi s/11),\,\sqrt a\sin(10\pi s/11)\big).
\]
On this rank-four cyclic orbit the uniform masses minimize the energy. In fact $[f(x_i\cdot x_j)]$ is positive semidefinite in dimension six and hence for codes embedded in it: use the zonal decomposition $f(t)=(t^4-\frac35t^2+\frac3{80})+\frac7{20}(t^2-\frac16)+\frac1{48}$, all coefficients of the normalized zonal kernels being positive. Averaging the masses over the cycle cannot increase the quadratic form. We do **not** assume that this kernel is positive semidefinite in arbitrarily high dimension: to upper-bound any competitor it suffices to test its uniform masses.

## The all-dimensional upper bound

The permutation image of a transitive isometry group on 11 points contains a full 11-cycle, by orbit-stabilizer and Cauchy's theorem. In cyclic order the Gram is circulant and positive semidefinite with diagonal one; its five lags are $g_j=\sum_{k=0}^5V_{jk}p_k$ with $p_k\ge0$, $\sum p_k=1$. Conversely every such vector gives a real circulant Gram, eligible whenever all $g_j\le1/2$.

The set of strong directed differences $S=\{\pm j:g_j<-1/2\}$ is sum-free: $a,b,a+b\in S$ would give three distinct vectors with squared sum negative. Among the 32 symmetric subsets of the ten nonzero residues mod 11, every nonempty sum-free one is equivalent under multiplication by a unit to $\{\pm1\}$ or $\{\pm1,\pm3\}$. With no strong lag the uniform energy is at most $(3/4)/11$.

**One strong lag.** Relabel it as 1. Eliminating $p_4,p_5$ with the mass sum and $g_2$ gives
\[
 g_j-x_j=B_j\cdot(p_0,p_1,p_2,p_3,1/2-g_2).
\]
Writing $d_j=(V_{j5}-V_{j4})/(V_{25}-V_{24})$, the first four coefficients are $V_{jk}-V_{j4}-d_j(V_{2k}-V_{24})$ and the last is $-d_j$. Every entry of $B_1$ is positive and, coordinatewise, $\sum_{j=3}^5|B_j|<24B_1$. These are strict inequalities between specified algebraic numbers, verified by rational intervals below. They hold independently of which lags are strong. In particular $\delta=g_1-x_1\ge0$, with equality only at the displayed winner.

If $g_1\ge-0.85$, drop the four nonpositive weak costs; even $(3/4+2 f(-0.85))/11$ is strictly below $H_{11}$. Otherwise $\delta<0.004$, so $|g_j|<0.14+24(0.004)<0.24$ for $j=3,4,5$. In that interval $|f'|\le 1/(3\sqrt{24})<0.07$; on $[x_1,-0.85]$ we have $f'<-2$. The loss at the strong lag therefore exceeds $2\delta$ when $\delta>0$, while the total possible gain at lags three through five is at most $24(0.07)\delta$. The saturated lag contributes $f(g_2)\le f(1/2)=0$. This proves strict optimality off the indicated Fourier vertex. Simply bounding the weak-lag derivatives on their full intervals would not give the required sensitivity margin.

**Two strong lags.** Take them to be 1 and 3. On each column of $V$ the following three inequalities hold, hence also for every convex combination:
\[
 g_1+.8g_2+.58g_3>-.68,\quad
 g_3+.22g_1>-.88,\quad
 g_1+g_3+.715g_2>-1.016.
\]
Using $g_2\le1/2$ and $g_1,g_3\le-1/2$ gives $g_1,g_3>-.8$ and $g_1+g_3>-1.38$. On $[-.8,-.5]$,
$f(t)=t^2(.5-t)(-.5-t)\le(.8)^2(1.3)(-.5-t)$. Thus the uniform energy is at most $(.75+2(.8)^2(1.3)(.38))/11<H_{11}$. This finishes the transitive classification.

## Rigidity without a transitivity hypothesis for the ordered mean

For an arbitrary ordered configuration, average its Gram matrix over cyclic shifts. Its lag one is the original mean consecutive inner product. The positive $B_1$ calculation bounds that mean below by $x_1$. At equality the averaged matrix has Fourier support $T=\{4,5,6,7\}\bmod11$, and every original lag-two entry is $1/2$ since their mean saturates that upper bound. Positive semidefiniteness forces the original Gram onto the same Fourier support: a vector in the kernel of the positive average is killed by every summand.

The diagonal and the lag-two diagonal determine a symmetric matrix on this support. In its two-index Fourier expansion, group unordered indices $k,l\in T$ by $k+l\bmod11$; each group has at most two pairs. The two diagonal observations, after absorbing the unordered-pair multiplicities, have multipliers $1$ and $(\zeta^{2k}+\zeta^{2l})/2$, where $\zeta=\exp(2\pi i/11)$. Two distinct pairs at fixed sum have distinct second multipliers: their products $\zeta^{2(k+l)}$ agree, so equality of sums would give identical unordered roots; doubling is invertible mod 11. The observations hence determine the matrix uniquely, and the cyclic average already has them. In particular equality for the original mean does not allow a hidden asymmetric realization.

## A connected six-dimensional witness above the transitive optimum

The [standalone exact verifier](verify_kissing_eleven_symmetry.py) lists eleven integer six-vectors to normalize individually. It verifies rank six and every off-diagonal inner product strictly below $1/2$ by signed integer comparisons. The strict graph consists of precisely these three internally disjoint paths, in zero-based labels:
~~~
0—1—10
0—2—3—4—5—10
0—6—7—8—9—10
~~~
Deleting any one vertex leaves a perfect matching. Thus the excess over the transitive bound does not come from putting smaller codes in unrelated orthogonal subspaces.

All squared inner products are rational, hence so is the entire cost matrix $F$. Exact elimination checks its positive pivots and that $z=F^{-1}\mathbf1$ is strictly positive. The minimizing weights are $z/(\mathbf1^Tz)$, giving $h(X)=1/(\mathbf1^Tz)$ in the interval stated above. Approximate Gram optimization was used only to discover the integer vectors.

As an application, no eleven-point component in either of the [remaining six-dimensional 75-point matching templates](https://github.com/mxym/math/blob/b6aced61e83a9f6c6b8956aa59f2f53241d96e38/research/euclidean-tensor-geometry/KissingSixHybridCycleComplement.md) that contain an eleven can be geometrically point-transitive: its charge would be at least $1/H_{11}$, whereas the other components already contribute at least $40.541078$. Their sum exceeds 48. This does not eliminate an arbitrary asymmetric eleven or either template. The [nine-point result](https://github.com/mxym/math/blob/0af4adc189728c7d1abe67825746bc5a9c4be53c/research/euclidean-tensor-geometry/KissingNonagonSymmetryBreaking.md) has a different Fourier extremizer and does not imply this two-strong-lag case.

Run **`python3 verify_kissing_eleven_symmetry.py`** (standard library). The checker isolates the five roots of $t^5+t^4-4t^3-3t^2+3t+1$, brackets its largest root $2\cos(2\pi/11)$ by bisection, generates the cosine lags by recurrence, and checks all scalar bounds, strong difference sets, and integer-vector claims including positivity of the minimizing masses.
