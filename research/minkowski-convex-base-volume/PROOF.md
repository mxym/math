# An exterior comparison for Minkowski sums

Research draft, independently reviewed by AI; not externally peer-reviewed. All volumes below are Lebesgue volumes in the ambient Euclidean space; the sets in the statements are nonempty compact subsets of R^d (d ≥ 1). No convexity, interior, or boundary regularity is presumed unless stated. The convention of nonempty summands matters: e.g. the inequality is not meant to quantify over an empty B.

## Target

Fradelizi–Madiman–Marsiglietti–Zvavitch (EMS Surveys Math. Sci. 5 (2018), Proposition 4.15 and Remark 4.16(1)) ask about the all-dimensional extension of their one-dimensional inequality, including the special case of a convex base. Fradelizi–Madiman–Zvavitch (IMRN 2024, §3.3, Conjecture 3.11 and the immediately preceding paragraph) pose both versions again. Their Theorem 3.12 proves the convex-base version if one of the other summands is a zonoid. This note proposes the unrestricted compact-summand result.

**Theorem 1 (exterior volume).** For compact E,B and compact convex K,

$$
 |(E+B)\setminus(K+\operatorname{conv}B)|\;\ge\;|E\setminus K|.
$$

There is no containment hypothesis between E and K.

## Proof by metric projection

**Finite B.** List the distinct elements of B as b₁,…,bₘ. For x outside K put p=P_K(x), the Euclidean nearest point, and n=x−p. The projection exists by compactness and is unique by strict convexity of squared Euclidean distance on a convex set. It satisfies ⟨n,k−p⟩≤0 for every k in K (differentiate squared distance at t=0 along the segment from p to k). Conversely, this variational inequality at p implies p is the unique nearest point, by expansion of squared distance. The projection is continuous: for convergent xᵢ, any cluster point of their projections minimizes distance at the limit by compactness and continuity, so uniqueness forces convergence.

Let j(n) be the least index maximizing ⟨n,bⱼ⟩ and put $T(x)=x+b_{j(n)}$ for x in E∖K. The pieces of this partition are Borel: they are finite intersections of weak and strict comparisons between continuous functions, restricted to E∖K. Write Q=K+conv B, y=T(x), $b=b_{j(n)}$ and q=p+b. For every z=k+b′ in Q,

$$
 \langle y-q,z-q\rangle=\langle n,k-p\rangle+\langle n,b'-b\rangle\le 0.
$$

The support bound for the second term uses linearity on conv B, not just on B. Thus P_Q(y)=q, and y is outside Q because y−q=n≠0. The image is in E+B by definition. Moreover, y uniquely determines n=y−P_Q(y), hence j(n), and then $x=y-b_{j(n)}$. T is injective, including on ties; fixing j as a function only of n is essential here. Its finitely many translated Borel pieces are pairwise disjoint. Translation invariance and finite additivity give |T(E∖K)|=|E∖K|. This proves the assertion without requiring E⊇K.

**General compact B.** Let D be the closed Euclidean unit ball. For δ>0 choose a nonempty finite δ-net F⊂B, so B⊂F+δD. The set conv F+δD is convex and contains B, hence contains conv B. Consequently

$$
 Q=K+\operatorname{conv}B \subset (K+\delta D)+\operatorname{conv}F.
$$

Also E+F⊂E+B. Taking the complement of the *larger* obstacle on the left in the finite result gives

$$
 |(E+B)\setminus Q|
 \ge |(E+F)\setminus ((K+\delta D)+\operatorname{conv}F)|
 \ge |E\setminus(K+\delta D)|.
$$

As δ=1/m decreases to zero, the final sets increase to E∖K because K is closed. Continuity from below finishes the proof. Compact sumsets and compact convex hulls here are Borel. No continuity of the volume of an arbitrary compact set under Hausdorff convergence is needed. ∎

## Independent proof by ordered halfspaces

This proof, contributed in the independent internal review, handles compact $B$ directly. For a nonempty compact $M$, write $h_M(u)=\max_{z\in M}\langle u,z\rangle$. Take a countable dense sequence of unit directions $(u_i)_{i\ge1}$ (in dimension one the two directions suffice). The support inequality for $K$ in every one of these directions characterizes $K$. Indeed, each exterior point $x$ is strictly separated from $K$ by a unit direction (one choice is $(x-P_K(x))/\|x-P_K(x)\|$). The strict inequality persists on a neighbourhood because the support function is continuous: $|h_K(u)-h_K(v)|\le (\max_{k\in K}\|k\|)\|u-v\|$.

Decompose $E\setminus K$ into countably many disjoint Borel layers $L_i$ according to the **first** direction $u_i$ whose support inequality is violated. Before considering any $x$, fix one point $b_i\in B$ achieving $h_B(u_i)$ for each $i$. No measurable selection over the sphere is needed. For $x\in L_i$ let $y=x+b_i$. Then

$$
 \langle u_i,y\rangle>h_K(u_i)+h_B(u_i),\qquad
 \langle u_j,y\rangle\le h_K(u_j)+h_B(u_j)\quad(j<i).
$$

The strict inequality uses the maximizing property of $b_i$ at direction $u_i$; the earlier inequalities only use $b_i\in B$. Since $h_{K+\operatorname{conv}B}=h_K+h_B$, every such $y$ lies in $(E+B)\setminus(K+\operatorname{conv}B)$. Moreover $i$ is recoverable as its first violated support inequality for the enlarged obstacle. Hence the translates $L_i+b_i$ are pairwise disjoint, each has volume $|L_i|$, and countable additivity proves Theorem 1. ∎

## Consequences for compact summands

**Corollary 2 (hull-corrected supermodularity).** For all compact A,B,C,

$$
 |A+B+C|+|\operatorname{conv}A|\ge |A+B|+|A+C|.
$$

In particular, if A is convex, the same inequality holds with |A| on the left. This is the statement of FMZ Conjecture 3.11 for convex bodies, also allowing lower-dimensional compact convex A.

**Proof.** Pick c₀∈C and replace C by C−c₀; this only translates A+C and A+B+C and does not change any volume. Then E=A+C contains A. Put K=conv A. The set A+B is contained both in E+B and in Q=K+conv B, whereas the exterior part of E+B is disjoint from Q. Thus

$$
 \begin{aligned}
 |A+B+C|=|E+B|
 &\ge |A+B|+|(E+B)\setminus Q|\\
 &\ge |A+B|+|E\setminus K|\\
 &\ge |A+B|+|A+C|-|\operatorname{conv}A|.
 \end{aligned}
$$

The last inequality uses |E∩K|≤|K|, not K⊂E. ∎

**Corollary 3 (increments for nested sets).** If K is compact convex and K⊂E, then |E+B|−|K+B|≥|E|−|K|. Indeed, K+B lies in (E+B)∩(K+conv B), and Theorem 1 applies. This does not assert monotonicity of the increment for arbitrary *nonconvex* reference sets.

**Limits and sharpness.** For B a singleton Theorem 1 is equality. The one-dimensional example of FMMZ Prop. 4.14, A={0,1}, B=C=[0,1], gives |A+B+C|=3, |A+B|=|A+C|=2 and |conv A|=1; replacing |conv A| by |A|=0 fails. No multiplicative (log-submodular), fractional, entropy-power, mixed-volume derivative or weighted-volume result is being asserted. In particular, the additive result does not yield general supermodularity of the set function of all subsums of nonconvex summands, since the common base in such a comparison may be nonconvex.
