# Quantitative symmetry breaking above 72 points in six dimensions

Let $C$ be a unit-vector kissing code in $\mathbb R^6$: distinct vectors have inner product at most $1/2$. Split the space into **any** three orthogonal real two-planes. Let $R_i$ rotate plane $i$ by $120^\circ$ and fix its complement. Set
\[
 e_i=\max_{x\in C}\min_{y\in C}\|R_i x-y\|.
\]
This measures how far the rotated points miss the set. It does not require any rotation to preserve $C$ or any nearest point to be a prescribed one.

**Theorem.** Every such code with more than 72 points satisfies
\[
                e_1^2+e_2^2+e_3^2>\frac3{41}.
\]
In particular, for some $i$ and some $x$ the rotated point lies at distance **greater than $1/\sqrt{41}$** (about $0.156$) from every member of $C$. This rules out approximate as well as exact independent third-turn symmetry. It does not rule out arbitrary 73-point codes or assert that the constant is optimal.

Two facts prove the theorem. First, even if the allowed maximum inner product is relaxed from $1/2$ to **$43/80$**, a code exactly invariant under the three rotations still has at most 72 points; 72 remains attainable by the classical $E_6$ code. We do not assert rigidity of its 72-point maximizers with the relaxed angle. Second, a finite-group averaging argument with a product-variance bound transfers sufficiently small nearest-point errors into that relaxed model.

## 1. Orbit bound with relaxed angle

Put $t=43/80$ and $r^2=2(1-t)/3=37/120$. The squared distance to a point rotated in just one nonzero coordinate is three times the squared radius there, so each nonzero radius is at least $r$. Supports have sizes 1, 2, 3, with orbit sizes 3, 9, 27. A phase is viewed modulo $120^\circ$, with nearest separation in $[0,60^\circ]$. For distinct orbits their largest inner product maximizes the cosine on each common coordinate independently.

Each axis still contains at most six points: seven points on a circle have a gap at most $360^\circ/7<52.5^\circ$, and $\cos52.5^\circ\ge(\cos45^\circ+\cos60^\circ)/2>3/5>t$ by concavity. On each pair support there are at most two orbits. The radius pairs $(a,b)$ lie on the unit circular arc from $(r,\sqrt{1-r^2})$ to its swap, so $aa'+bb'\ge2r\sqrt{1-r^2}$. With three orbits some two first-coordinate phases are within $40^\circ$. Their largest product is at least
\[
     r\sqrt{1-r^2}+(\cos40^\circ-1/2)r^2>t .
\]
Here $\cos40^\circ>3/4$ since $4u^3-3u$ is increasing on $[1/2,1]$ and its value at $3/4$ is $-9/16<\cos120^\circ$. Also $\sqrt{37\cdot83}>277/5$. This proves the claim and gives $3\cdot6+3\cdot2\cdot9=72$ if there are no triples.

There are at most two triple orbits: out of three, some two first-coordinate phases would be within $40^\circ$, giving maximum product at least $r^2(1+\cos40^\circ)>t$. In fact any two triple orbits must differ by more than $40^\circ$ on *each* phase circle, by that same estimate. For phases at separation $\delta>40^\circ$, the sum of their two nearest cosines to a third phase is at least $1/2+\cos(60^\circ-\delta)>7/5$. The minimum over the third phase is at an antipode: the two cosines are concave on each of the arcs cut out by those antipodes. Here $\cos20^\circ=\sqrt{(1+\cos40^\circ)/2}>9/10$. If two triples exist, a pair orbit of radii $a,b$ would therefore have summed largest products to them strictly greater than
\[
 (7/5)r(a+b)\ge(7/5)(r^2+r\sqrt{1-r^2})>2t .
\]
A pair is impossible, so this branch gives at most $54+18=72$.

With **one triple** we need the stronger bound of one pair orbit on each support. The [closed-box verifier](verify_kissing_six_approximate_third_turns.py) proves this by a six-variable interval calculation. For one pair write $\alpha,\beta\in[0,60^\circ]$ for phase separations from the triple phases on its two coordinates. Scale coordinates by $\sqrt{240}$: the pair radii are
\[
  A=\sqrt{74+92u},\qquad B=\sqrt{166-92u},\qquad 0\le u\le1 ,
\]
and each scaled triple radius is at least $\sqrt{74}$. A second pair uses primes. Necessary inequalities are
\[
 \sqrt{74}(A\cos\alpha+B\cos\beta)\le129,\qquad
 \sqrt{74}(A'\cos\alpha'+B'\cos\beta')\le129,
\]
\[
 AA'\cos d(\alpha,\alpha')+BB'\cos d(\beta,\beta')\le129,\qquad
 d(v,w)=\min(v+w,120^\circ-v-w).
\]
The distance $d$ takes the most favorable of the two choices of relative phase sign; it dominates $|v-w|$. The individual necessary inequalities remain valid when the two actual triple radii are unequal.

In the cube $(u,\alpha/60^\circ,\beta/60^\circ)$ the verifier uses closed boxes, rounds each radius and cosine downward, and tests the three lower bounds. On the double-phase term, an upper bound for $d/60^\circ$ is the minimum of 1, the sum of the upper endpoints and 2 minus the sum of the lower endpoints. Square roots use integer square roots; the cosine uses the degree-ten alternating Taylor lower polynomial at the upper angle given by $\pi<355/113$, and the exact value at $60^\circ$. An equality is never discarded. On dyadic widths $1/4$ through $1/512$, the successive numbers of surviving unordered pairs are **102, 27, 38, 75, 40, 36, 6, 0**. Both orbits lying in the same box are explicitly allowed. This proves the pair claim, and $27+3\cdot9+18=72$ finishes the relaxed bound.

## 2. From approximate rotations to a nearby invariant code

Suppose $\sum e_i^2\le3/41$. The inequalities $2e_i<1$, $3e_i<1$, and $2(e_i+e_j)<1$ hold for all distinct $i,j$ (use Cauchy–Schwarz for the last). The minimum chordal separation of $C$ is one. Thus for each $i$ the nearest-point map $\pi_i$ of $R_iC$ into $C$ is unique and injective, hence permutes $C$. Applying it three times stays within $3e_i$ of the original point, so $\pi_i^3=1$. The two orders of application of $\pi_i,\pi_j$ end within $2(e_i+e_j)$ of each other since $R_i,R_j$ commute, forcing those permutations to commute. We have an actual permutation action $\pi$ of $G=C_3^3$ on the original labels, without assuming that the permutations preserve any inner products. Inverse steps have the same pointwise error by bijectivity and orthogonality.

For a label $x$ and uniform $g\in G$ put $Z_x(g)=g^{-1}\pi(g)x$ and $b_x=\mathbb E_g Z_x(g)$, where $g$ acts on the ambient space by the given third turns. Then $b_{\pi(h)x}=h b_x$. The centered variance
\[
   V_x=\mathbb E\|Z_x-b_x\|^2\le \sum_i e_i^2/3=:v .
\]
Indeed on each three-element fiber in coordinate $i$, all three pairwise distances of $Z_x$ are at most $e_i$ by the one-step and inverse-step bounds. The fiber variance is the sum of these three squared distances divided by 9. Product variance is at most the sum of the expected coordinate-fiber variances. One proof is to split off one independent coordinate by the law of total variance and apply induction; averaging over that coordinate cannot increase a remaining fiber variance, by Jensen's inequality applied to pair differences.

Since all $Z_x(g)$ are unit, $\|b_x\|^2=1-V_x\ge1-v>0$. For distinct labels $x,y$, the two permuted labels stay distinct for every $g$, giving $\mathbb E\langle Z_x,Z_y\rangle\le1/2$. Cauchy–Schwarz on the covariance gives
\[
 \langle b_x,b_y\rangle\le1/2+\sqrt{V_x V_y}\le1/2+v .
\]
Hence the normalized $b_x$ have pairwise inner products at most $(1/2+v)/(1-v)\le43/80$, using $v\le1/41$. They are all distinct, and equivariance makes the resulting code exactly invariant under $G$. Part 1 bounds its size by 72, proving the stated lower bound on symmetry error.

The [exact $60^\circ$ independent-third-turn classification](https://github.com/mxym/math/blob/4b782c9cb9f76b74fbb231d9fce0c91e7523a83d/research/euclidean-tensor-geometry/KissingThreeIndependentThirdTurns.md) has the stronger conclusion of a unique $E_6$ completion above 60 *for exactly invariant kissing codes*. Here neither input symmetry nor the relaxed-angle equality classification is assumed.

**Replay.** `python3 verify_kissing_six_approximate_third_turns.py`, using ordinary standard Python. The proof of the variance estimate is analytic; the finite verifier is for the single-triple exclusion and exact elementary margins.
