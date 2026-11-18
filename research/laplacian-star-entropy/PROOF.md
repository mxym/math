# Extremal entropy of the trace-scaled combinatorial graph Laplacian

For a finite simple undirected connected graph G of order n≥2 and size m, put
ρ=L(G)/(2m), L=D−A. Use natural logs (conversion to bits is a positive factor).
Write S for Shannon/von Neumann entropy of its eigenvalue distribution, and
H_z=(1−z)⁻¹ log tr(ρ^z). Candidate conclusions:

* S(G) ≥ S(K₁,ₙ₋₁), with equality only for the star.
* H_z(G) ≥ H_z(K₁,ₙ₋₁) for every real z>1, with the same equality condition.
* Over trees of order n the unique maximizer of S is Pₙ.

These address Conjectures 1.2, 3.3 and 1.3, respectively, **in the arXiv
version** of Dairyko et al., arXiv:1609.00420 (published LAA 521 (2017),
240–253). The tree maximum is a direct consequence of older results; it
is not a new coefficient extremal theorem. No assertion for 0<z<1, for
weighted/multiple edges, or for the symmetric normalized Laplacian.
This AI-assisted draft has passed independent internal AI review; it has not received external peer review. No priority claim is made.

## 1. Entropy order and compression

For two nonnegative lists λ,γ of equal length, with equal sum, one has
[
 -\sum_i λ_i\log λ_i +\sum_i γ_i\log γ_i
 =\int_0^\infty \log\frac{\prod_i(t+λ_i)}{\prod_i(t+γ_i)}\,dt.
\tag{1}
]
Indeed integrate each log on [0,R] with antiderivative (t+v)log(t+v)−(t+v).
At 0 use 0log0=0. At R the common size and first moment cancel and the
remainder is O(1/R). Thus increasing the elementary symmetric functions
with fixed first sum can only increase entropy, strictly if some coefficient
strictly increases. This entropy fact is prior (Jozsa–Mitchison); (1)
avoids any question about interpolation through real-rooted polynomials.

Use [P. Csikvári, *Applications of the Kelmans transformation: extremality of
the threshold graphs*, Thm 8.1](https://real.mtak.hu/14004/1/application_Kelmans.pdf):
moving every private neighbor of v (other than u) from v to u does not
increase the absolute coefficients of det(tI−L). Vertex and edge counts are
unchanged. By (1), S cannot increase: either apply (1) to ρ or divide the
unnormalized difference by 2m.

Arbitrary compression may disconnect; we require a connected endpoint.
Fix vertex u. While it is not universal choose a path from u to a nonneighbor
and a neighbor v of u adjacent to a nonneighbor (e.g. first three vertices
of a shortest path). Compress v to u. The edge uv remains, moved neighbors
can still get to v through u, the graph stays connected and deg u increases.
After finitely many steps u is universal. Keep it universal. On the other
vertices compress both neighborhoods whenever neither contains the other
off the two chosen vertices. A shared neighbor u never moves.
If the two private sets have sizes p,q>0, the sum of squared degrees
increases by 2pq; degrees of all other vertices are unchanged. This terminates.
The induced graph H on the n−1 remaining vertices has totally comparable
open neighborhoods after removing each pair. Such a graph is threshold:
if there are no isolated vertices, a maximum-degree vertex v is universal.
Indeed for each w nonadjacent to v take a neighbor z of w; the comparison
of z and v and deg v ≥ deg z force w adjacent to v. This contradiction proves
the claim. Comparability is hereditary, so iteratively delete an isolated or
universal vertex. Reversing gives H by isolated and dominating births.
We have reduced to a connected threshold graph G'=K₁∨H of the same n,m.
This reduction is weak, but we prove strictness below for all m>n−1.
For m=n−1 use the tree comparison of §5 to ensure strictness for every
non-star, even if compression terminates at a star.

## 2. A threshold remainder as a degree distribution

Write N=n−1, s=m−N=e(H). If s=0 this cone is the star. For s>0 let
J⊂{1,...,N−1} be the indices at which a dominating vertex is added after j
prior vertices, starting with one vertex; set k=|J| and s=Σ_{j∈J}j.
Thus s≥k(k+1)/2. In the orthogonal basis of prefix contrasts
e_j=(1,...,1,−j,0,...,0) with j initial entries 1 (plus the constant vector),
the star on a new vertex j+1 with its j older neighbors has eigenvalue 1 on
e_i for i<j, j+1 on e_j, and 0 on e_i for i>j or the constant.
The contrasts span the constant-vector orthocomplement and all increments
are simultaneously diagonal. Let μ₁,...,μ_{N−1} denote the resulting eigenvalues
there, including any zeros. Sum μ_i=2s. A further universal birth, at j=N,
gives the nonzero eigenvalues of the cone:
[
 N+1,\qquad 1+μ_1,\ldots,1+μ_{N-1}.
\tag{2}
]

On indices 1,...,N−1 form an auxiliary undirected graph with loops: each
j∈J contributes one loop j→j (degree two) and the j−1 simple edges ij for
1≤i<j. There are s edges including k loops. Its exact degree sequence in
the given ordering is (μ_i); rank r=#{i:μ_i>0}=max J≤min(s,N−1).
Sample a uniformly random edge of this auxiliary graph, with either of its
two formal directions equiprobable, and let X,Y be its ordered endpoints.
Each marginal is μ_i/(2s); the joint probabilities equal 1/(2s) on 2(s−k)
ordered nonloop pairs and 1/s on k loop pairs. By Shannon subadditivity,
2H(X)≥H(X,Y)=log(2s)−(k/s)log2. Therefore
[
 \sum_i μ_i\log μ_i\le s\log(2s)+k\log2.                 \tag{3}
]
Using the concavity on u>0 of h(u)=(1+u)log(1+u)−u log u, h(0)=0, gives
[
 T:=\sum_i(1+μ_i)\log(1+μ_i)
 \le s\log(2s)+k\log2+r h(2s/r).
\tag{4}
]
R↦R h(2s/R) increases as its derivative equals log(1+2s/R)>0, so one
may replace r in (4) by min(s,N).

## 3. The cone inequality

Let x=s/N>0 and δ_N=(1+1/N)log(N+1)−log N>0. The strict Shannon comparison
between (2) divided by 2(N+s) and the star spectrum (N+1,1,...,1)/(2N)
is exactly
[
 T < 2(N+s)\log(1+x)+\frac{s}{N}(N+1)\log(N+1).
\tag{5}
]
Using (4), (5) follows if
[
 s\{D(x)+δ_N\}> k\log2,                                     \tag{6}
]
where
[
 A(x)=\frac{2(1+x)}{x}\log(1+x)-\log x,\quad
 D(x)=A(x)-\log2-
 \begin{cases} h(2),&0<x\le1,\\ h(2x)/x,&x\ge1.\end{cases}
]
The exact scale in (6) follows by subtracting s log s from (4) and (5).
On (0,1], A'(x)=[x−2log(1+x)]/x²<0, since 2log(1+x)−x is increasing
there and vanishes at 0. For x≥1,
D'(x)=[x+log(1+2x)−2log(1+x)]/x²>0, because
log((1+x)²/(1+2x))=log(1+x²/(1+2x))<x. Thus
D(x)≥D(1)=log(32/27)>0. Further,
D(1/3)=17log2−10log3>log2 since 2¹⁶>3¹⁰. In particular (6) holds
for N≥3s, since k≤s.

For N<3s use Nδ_N=log N+(N+1)log(1+1/N)>log N+1, by
log(1+t)>t/(1+t). Monotonicity of (log N+1)/N on [1,∞) gives
sδ_N>(1+log(3s))/3. For k≥8, s≥9k/2, and
(32/27)^9>4, so sD(1)>klog2 already. For 1≤k≤7, put u=k(k+1)/2.
The needed strict elementary bounds reduce to
[
 6u\,32^{3u}>2^{3k}27^{3u},\qquad 1\le k\le7.             \tag{7}
]
Indeed s≥u and e>2. The floors of the seven exact LHS/RHS ratios are
1,1,1,2,5,21,126 respectively, all strictly greater than one before taking
the floor (use the integer comparisons in verify.py). This proves (6), hence
(5), for every cone with s>0 and therefore every connected graph with m>N.

## 4. Rényi is a corollary of Sakai–Iwata; optional self-contained verification

The higher-order conclusion follows directly from [Sakai–Iwata, Theorem
2, inequality (253)](https://arxiv.org/abs/1605.00019). In dimension N
their distinguished comparator is v(t)=(1−(N−1)t,t,...,t), 0≤t≤1/N.
For fixed S(p) they prove that H_z(p)≥H_z(v(t)) for every z>1, where
t is uniquely chosen to match S(p). Along this curve S and every H_z,
z>1, are strictly increasing in t for 0<t<1/N: the Shannon derivative
is (N−1)log((1−(N−1)t)/t)>0; the derivative of the z-power sum is
z(N−1)[t^(z−1)−(1−(N−1)t)^(z−1)]<0. The star is v(a), a=1/(2N).
Thus the strict graph Shannon comparison implies t>a and the strict graph
Rényi comparison, including the case t=1/N by continuity and interior
strict monotonicity. For N=1 there is only one graph. The same existing
Theorem 2 applied with fixed order 2 immediately gives all orders >2
from the original H₂ result. The new graph step is the Shannon inequality,
not a new fixed-Shannon-to-Rényi entropy comparison.

Here is an optional self-contained alternative to the Sakai–Iwata deduction:

Let p₁,...,p_N be the positive spectrum of a connected nonstar ρ (exactly N
positive terms). The star has b=(N+1)/(2N) once and a=1/(2N) with
multiplicity N−1. We have max p_i<b: from L(G)+L(complement)=nI−11ᵀ,
λ_max(L)≤n. This is strict after normalization if m>N. For m=N
equality would imply a disconnected complement: indeed λ_max(L)=n exactly
when the complementary Laplacian has a nonconstant kernel vector. Then G
contains all edges between two nonempty parts; a tree cannot have both parts
of size ≥2 (a four-cycle), so has a universal vertex and is a star. This
also handles small orders, for which there is no nonstar tree.

Consider the real exponential polynomial
F(z)=Σp_i^z−(N−1)a^z−b^z. It is nonzero and negative for sufficiently
large z since b>max p_i. In increasing order of distinct bases the coefficient
sequence after combining ties and deleting zeros has ≤3 sign changes: only
at a or b can a coefficient be negative, and the last coefficient is −1.
The generalized rule of signs gives ≤3 real zeros, counted with multiplicity.
For completeness: for an exponential sum with increasing exponents divide
by the smallest exponential, leaving the constant c₁ first; the derivative
has the remaining coefficient signs. At −∞ the normalized function has
sign c₁ and its derivative has the sign of c₂. Rolle with multiplicities
gives at least one fewer derivative zero than function zeros; if c₁ and c₂
have the same sign and there is a first zero, the derivative has an extra
zero before it (the function was initially moving away from zero). Induction
on the number of terms proves the bound; endpoint asymptotics imply all
zeros lie in a bounded interval, and analyticity makes them finite.

We have F(0)=F(1)=0, and F'(1)=S(star)−S(G)<0 by §§1–3 and §5. Hence F
is negative just right of 1, and negative eventually. A zero strictly after
1 requires at least two more zeros counting multiplicity (an even tangency
or crossings followed by a return). Impossible. Thus F(z)<0 for every z>1,
which is the desired strict Rényi comparison. No conjecture at 0<z<1 is
used. This provides a short independent verification of the stated application of the prior entropy-comparison theorem.

## 5. Trees: direct corollary including strictness

By the Zhou–Gutman coefficient theorem (see
[Mohar, *On the Laplacian coefficients of acyclic graphs*](https://doi.org/10.1016/j.laa.2006.12.005)),
each absolute Laplacian coefficient of a tree is at least its star value
and at most its path value. All trees have trace 2N, so (1) proves both
entropy comparisons. They are strict except at the corresponding extremal
trees: e₂=((2N)²−2N−Σd_i²)/2. Among positive integer degree sequences of
sum 2N and length n, Σd_i² is uniquely maximal at (N,1,...,1) by shifting
excess to the largest coordinate, and uniquely minimal at (2,...,2,1,1)
by balancing. Those sequences force star and path respectively. For n=2
the single tree is both, with the formula for the path sequence understood
as (1,1). This proves strictness required in §4.

## What is known / what to audit

Original published input: strict H₂ star minimum was already Theorem 3.8
of the original arXiv version; the almost-all Shannon result, plus tree
and small-order numerics, are theirs. The path result here is only a direct
application of old tree coefficients and entropy monotonicity. The novel
candidate core is the threshold remainder as endpoint marginals, plus
the uniform scalar comparison for every possible size. No graph
enumeration or floating numerical evidence is needed in the proof.
