# Dempwolff's semibent partial spread has no extension beyond dimension seven

> **Priority addendum (2026-11-27).** After this note was frozen, a terminology-crossing search identified Penttila--Storme's 1998 monomial-flock classification as an earlier route that implicitly yields the same nonextension conclusion. The proof and certificates below remain correct, but priority is **not** claimed for the q-clan trace condition or for the global nonexistence consequence. See [PRIOR_ART_ADDENDUM.md](PRIOR_ART_ADDENDUM.md) for the exact equation map and revised contribution boundary.

**Theorem.** In the family of Theorem 3.5 of Ulrich Dempwolff, where the original space has binary dimension $2n+1$ and $n\ge3$, the specified partial spread extends over a hyperplane to a partial spread in dimension $2n+2$ **if and only if $n=3$**. In particular it never extends for $n\ge5$, answering the question in §4. The negative conclusion concerns preservation of the prescribed subspaces, not arbitrary bent extensions of the associated Boolean function.

**Source and scope.** U. Dempwolff (sole author), [*Geometric and design-theoretic aspects of semibent functions II*](https://link.springer.com/article/10.1007/s10623-011-9511-3), *Designs, Codes and Cryptography* **62** (2012), 241–252. In the [author-posted manuscript](https://www.researchgate.net/publication/220638584_Geometric_and_design-theoretic_aspects_of_semibent_functions_II), Theorem 3.5 gives the spaces; §4, Definition (a), gives the extension considered here; Example 4.2(a),(d) reports the positive $n=3$ and negative $n=4$ cases by computation. The last bullet of Remark 4.3(b) asks: “Decide in dimension ≥ 11 the extension problem for the spreads from Theorem 3.5.” The new range relative to those published results is every $n\ge5$. This question asks only for an extension, not for its completion to a *full* spread as in Definition (b).

## When do the given subspaces lift?

Work throughout over $\mathbb F_2$. Put $F=\mathbb F_{2^n}$, write $\operatorname{Tr}:F\to\mathbb F_2$ for the absolute trace, and take $V=F\times F\times\mathbb F_2$. The prescribed family consists of
\[
 U_\infty=\{(x,0,0):x\in F\},\qquad
 U_b=\{(b x^2,x,\operatorname{Tr}(b x)):x\in F\}\quad(b\in F).
\]
They are $n$-dimensional binary subspaces. For $b\ne c$, equality of a vector from $U_b$ and one from $U_c$ forces equal second coordinates $x$ and then $(b+c)x^2=0$, hence $x=0$; $U_\infty$ also meets each $U_b$ only at zero.

An extension consists of $(n+1)$-spaces $L_i$ in $W=V\times\mathbb F_2$ such that $L_i\cap V=U_i$ and every pair meets only at $0$. Fixing a linear identification of the section hyperplane with $V$ and choosing one vector outside it identifies the ambient binary space with $V\times\mathbb F_2$. Nothing here is asserted for abstract incidence isomorphisms. Since the family has $2^n+1$ members, any such lifted partial spread is exactly of the size whose union indicator is a Dillon $PS^+$ bent function, as required by Dempwolff's §4 definition.

**General lifting criterion.** For any pairwise trivially intersecting $n$-spaces $U_i$ in binary dimension $2n+1$, let $\lambda_{ij}$ be the unique nonzero binary linear functional on $V$ vanishing on $U_i+U_j$. Its existence and uniqueness follow from $\dim(U_i+U_j)=2n$. Then an extension exists if and only if some $w_i\in V$ satisfy
\[
       \lambda_{ij}(w_i+w_j)=1\qquad(i\ne j).
\]
Indeed, the points of $L_i$ outside $V$ must be exactly $(w_i+U_i,1)$. Two such cosets intersect if and only if $w_i+w_j\in U_i+U_j$. Conversely the union of $U_i\times\{0\}$ with its chosen outside coset is an $(n+1)$-space. No assumption of an extra group of symmetries or of a full spread is used.

**Reduction for the stated family.** We may take $w_\infty=0$: apply the invertible shear $(v,t)\mapsto(v+t\,w_\infty,t)$, which fixes $V$ pointwise. Replacing $w_b$ by any representative modulo $U_b$ does not change its lift. Since the second coordinate on $U_b$ is bijective onto $F$, write the representative as $w_b=(a_b,0,c_b)$. With zero second coordinate it lies in $U_\infty+U_b$ if and only if $c_b=0$. Hence exactly $c_b=1$ avoids the lifted $U_\infty$.

For $b\ne c$ we now have $w_b+w_c=(d,0,0)$ with $d=a_b+a_c$. It is in $U_b+U_c$ precisely if some $x\in F$ satisfies
\[
   (b+c)x^2=d,\qquad \operatorname{Tr}((b+c)x)=0.
\]
The first equation determines $x$ uniquely. Since the trace is unchanged on squaring, $\operatorname{Tr}((b+c)x)=\operatorname{Tr}((b+c)^2 x^2)=\operatorname{Tr}((b+c)d)$. We have therefore proved the exact criterion
\[
   \operatorname{Tr}\big((b+c)(a_b+a_c)\big)=1
       \quad\text{for every distinct } b,c\in F. \tag{1}
\]
No linearity of the assignment $b\mapsto a_b$ is presumed. Adding a common constant to all $a_b$ lets us take $a_0=0$.

## A seven-subspace obstruction in all higher dimensions

Assume $n\ge4$ and choose four linearly independent field elements
$u_1,u_2,u_3,u_4$.  Put
\[
 S=\{0,u_1,u_2,u_3,u_4,u_1+u_2+u_3+u_4\}.
\]
These six labels are distinct and their sum is zero.  Add equation (1) over
the 15 unordered pairs in $S$.  The coefficient of $a_b$ on the left is
\[
 \sum_{c\in S\setminus\{b\}}(b+c)
   =5b+\sum_{c\in S\setminus\{b\}}c
   =b+b=0 .
\]
Thus the summed left side is zero, whereas the summed right side is
$15=1$ in $\mathbb F_2$, a contradiction.  In fact the six finite members
with labels in $S$, together with $U_\infty$, already cannot be lifted to
seven pairwise disjoint $(n+1)$-spaces.  No global enumeration or dimension
estimate is needed.

## Global rank and ovoid reformulation

On the $2n$-dimensional binary space $F^2$, set $Q(x,y)=\operatorname{Tr}(xy)$ and let $B(u,v)=Q(u+v)+Q(u)+Q(v)$ be its polar bilinear form. If (1) holds, set $v_b=(b,a_b)$ for each $b\ne0$. Then $Q(v_b)=1$ by the equations with $c=0$ and $Q(v_b+v_c)=1$ for distinct nonzero $b,c$. Consequently $B(v_b,v_c)=1$ off the diagonal and $B(v_b,v_b)=0$.

Set $m=2^n-1$. The binary Gram matrix on the $m$ vectors is $I_m+J_m$, with $J_m$ the all-ones matrix. Since $m$ is odd its kernel is exactly the span of the all-ones vector: $(I+J)z=0$ forces $z=(\sum z_i)\mathbf1$, and $\mathbf1$ does lie in the kernel. Its rank is $2^n-2$. On the other hand, in a binary basis the Gram matrix has the form $P^\mathsf{T} M P$, where the columns of $P$ are the vectors and $M$ represents $B$. Therefore its rank is at most $2n$. The necessary inequality $2^n-2\le2n$ fails at $n=4$ and at every subsequent integer. This proves nonexistence throughout the formerly unsettled range without a computer or classification.

**Boundary check, also analytic.** At $n=3$ take $a_0=0$ and $a_b=b^{-1}$ for $b\ne0$. If one index is zero, (1) is $\operatorname{Tr}(1)=1$. Otherwise write $r=b/c\ne1$. The left side of (1) is $\operatorname{Tr}(r+r^{-1})=\sum_{j=1}^6 r^j=1$, since squaring modulo the order $7$ contributes exponents $1,2,4$ and $6,5,3$, and $1+r+\cdots+r^6=0$. Thus the ordinary partial-spread extension exists. This recovers the original positive case directly.

**Why this says nothing negative about unrestricted bent extension.** With $0^{-1}=0$, the indicator of the union of these subspaces is $f(X,Y,z)=1+z+\operatorname{Tr}(X Y^{-1})$: for $Y\ne0$ the unique label is $X/Y^2$, and at $Y=0$ the points in the union have $z=0$. Indeed the unrestricted extension $f(X,Y,z)+zt$ *is bent for every $n$*. The two-variable function $z+zt$ is bent; the $2n$-variable function $\operatorname{Tr}(X Y^{-1})$ is bent because summing its signed Walsh coefficient over $X$ selects the unique $Y$ with a specified inverse, leaving magnitude $2^n$. The Walsh coefficients of the direct sum multiply. Our impossibility theorem is precisely the additional requirement to lift the given geometric decomposition.

## Two independent finite checks

No downloads or nonstandard packages. From this directory use Python 3.10 or later:

~~~sh
python3 verify_trace.py
python3 verify_geometry.py
~~~

The first checks the normalized equations (1) using polynomial-basis multiplication, a Frobenius-sum trace, and binary row reduction on integers. It computes the number of **labeled normalized assignments**, not geometric equivalence classes. Its coefficient/augmented ranks at $n=3,4,5$ are $18/18$, $54/55$, $145/146$.

The second starts again from the original geometric subspaces. It enumerates their points, forms every $U_i+U_j$ explicitly, reads off its annihilator from standard basis membership and checks that annihilator on every point. It solves the unrestricted lift equations with separate vector representatives for all $i$, using symmetric differences of sets, a multiplication-operator trace and a different irreducible polynomial in dimensions $n=3,4,5$. It uses neither the normalized equation (1) nor the Gram obstruction. It verifies the explicit $n=3$ witness by constructing all 9 lifted four-spaces, checking closure, hyperplane sections and pair intersections. Its unnormalized ranks at $n=3,4,5$ are $26/26$, $70/71$, $177/178$. These finite checks corroborate the derivation; the proof for all $n$ is the rank argument.

## Prior-art scope (checked 2026-11-27)

The original paper already gives the $n=3,4$ answers and other families which do extend. Neither those examples nor a new general ovoid bound is claimed here. In fact, [Blokhuis--Moorhouse, *Some p-ranks related to orthogonal spaces*, Theorem 1.3 and Corollary 1.4](https://doi.org/10.1023/A:1022477715988) proved in 1995 that a hyperbolic quadric $Q^+(2n+1,2)$ has no ovoid for $n\ge4$. Their $q=2$ cap bound is exactly $2^n-2\le2n$, the inequality rederived by the Gram calculation above. Equation (1), after homogenizing with two binary coordinates, is equivalently an ovoid of that quadric. The contribution here is the reduction of Dempwolff's specified lift problem to (1), the fixed seven-subspace parity certificate above, and the resulting application to the question posed in §4; no claim is made that the general ovoid obstruction is new. The projective partial-spread extension should not be confused with extending a vectorial bent function by adding an output coordinate, with ordinary Boolean concatenation, or with testing whether a partial spread can be enlarged in the same ambient dimension.

A [forward-citation query in OpenCitations](https://api.opencitations.net/index/v2/citations/doi:10.1007/s10623-011-9511-3) returned three indexed titles: [Grigorescu–Wimmer–Xie](https://doi.org/10.1007/978-3-642-40328-6_39) on isomorphism testing, [Mesnager](https://doi.org/10.1007/s10623-014-9989-6) on vectorial constructions from o-polynomials, and [Zhang–Sun–Pasalic](https://doi.org/10.1007/s10623-021-00943-y) on balanced vectorial semibent functions. None gives this lift obstruction. Recent related literature screened included [Gadouleau–Mariot–Picek](https://arxiv.org/abs/2112.08705) on constructing other partial spreads from recurrences, [Anbar–Kalaycı–Meidl](https://doi.org/10.1007/s12095-026-00903-0) on bent partitions, and [the 2026 preprint arXiv:2611.26011](https://arxiv.org/abs/2611.26011) on constructing partial spreads using evolutionary methods. Searches by title, author, formula and “semibent [partial] spread extension” did not locate an earlier answer for the stated family. This is a bibliographic search result, not a proof of priority.
