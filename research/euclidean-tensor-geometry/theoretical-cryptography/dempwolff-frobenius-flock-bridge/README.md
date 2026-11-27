# A bridge between semibent partial-spread lifts and quadratic-cone flocks

## Claim and scope

Let $F=\mathrm{GF}(2^n)$, $n\ge2$, and let $T$ denote the absolute trace. Fix $1\le k<n$ with $\gcd(k,n)=1$, put $q=2^n$, $s=2^k$, and in $V=F^2\times\mathbb F_2$ define the binary $n$-spaces

$$
U_\infty=\{(x,0,0):x\in F\},\qquad
U_b=\{(b x^s,x,T(bx)):x\in F\},\quad b\in F.
$$

These form a type I.a semibent partial spread with a linear structure; its union indicator has degree $n-k+1$. An ordinary extension preserving the prescribed $q+1$ subspaces exists **exactly when $n-k\le2$**. The quadratic case exists in every dimension in this range; the cubic case requires odd $n$. This is not a result about every representation of the same Boolean function, full spreads, or arbitrary bent extensions.

**Priority.** The existence decision also follows from the **1998** monomial-flock classification of Penttila and Storme once the two settings are identified. O’Keefe and Penttila (2000) subsequently derived the same Frobenius indices explicitly on the flock side, with a stronger classification of second coordinates. Neither the trace formula, its exponent classification, nor any new flock is claimed here. Our purpose is the explicit correspondence, its application to the semibent question, and a short proof restricted to Frobenius exponents. The scalar core is a standard Maiorana–McFarland construction. Dempwolff's Theorem 3.5 and Example 3.4(b) are endpoints, not new families.

## Atoms, type, and Boolean degree

Apply the binary-linear coordinate change $(X,Y,z)\mapsto (X^{2^{n-k}},Y,z)$ and relabel $t=b^{2^{n-k}}$. The resulting atoms are $V_\infty=U_\infty$ and

$$V_t(h)=\{(t x,x,T(h(t)x)):x\in F\},\qquad h(t)=t^s.$$

For the next two sections one can use any normalized oval polynomial $h$: it permutes $F$, $h(0)=0$, $h(1)=1$, and its affine graph has no three collinear points. The Frobenius example has these properties: solutions of $t^s+\lambda t=\mu$ form an affine coset of a kernel of size at most two since $\gcd(s-1,q-1)=1$. The individual atoms have dimension $n$ and meet only in $0$ by their first two coordinates. A hyperplane defined by $T(\lambda X+\mu Y)+\epsilon z=0$ contains a finite atom exactly when $\lambda t+\mu+\epsilon h(t)=0$ and contains the infinite atom exactly when $\lambda=0$. For $\epsilon=0$ there is at most one finite atom (the defining functional is nonzero). For $\epsilon=1$ there are at most two finite atoms, and at most one if $\lambda=0$. Thus no hyperplane contains three atoms; in particular no third atom lies in the sum of two. This is the type I.a incidence property for this size of partial spread.

In the original coordinates the indicator, including the zero vector, is
$$f(X,Y,z)=1+z+T(XY^{q-s}).$$
For $Y\ne0$ the unique candidate label is $X/Y^s$; at $Y=0$ membership means $z=0$. The field power $Y^{q-s}$ permutes $F$ since $q-s\equiv1-s\pmod{q-1}$. Summing the Walsh transform over $X$ pins $Y$ to a unique value and gives absolute value $q$ for the $2n$-variable core. The additional $z$ gives spectrum $0,\pm2q$ and constant derivative $1$ in its direction.

Put $m=n-k$. The exponent $E=q-s$ has $m$ ones. The vector map $Y^E$ has degree at most $m$, being a product of $m$ binary-linear Frobenius powers. If its degree were at most $m-1$, a binary-coordinate expansion would express it as an $F$-linear combination of products of at most $m-1$ linearized coordinate polynomials (each coordinate equals $T(cY)$ for an appropriate $c$). In every positive-power term its exponent modulo $q-1$ is a sum of at most $m-1$ powers of two. Cyclic binary carries preserve the represented residue and strictly reduce the number of summands, so a reduced positive exponent in $[1,q-1]$ has weight at most $m-1$: the zero residue would require all $n$ bits, impossible here. Uniqueness of the degree-$<q$ univariate representing polynomial now contradicts the monomial $Y^E$. Finally $T(XY^E)$ couples independent input bits of $X$ to a basis of coordinate functions of $Y^E$ by a nondegenerate pairing. Some such coordinate has degree $m$, and its multiplication by its own $X$ bit cannot cancel. The degree of $f$ is exactly $m+1\ge2$, an extended-affine invariant in this range. Distinct admissible $k$ at fixed $n$ therefore give inequivalent scalar functions. This statement does not imply that the individual powers or scalar functions were previously unknown.

## Ordinary lift = normalized clan condition

An ordinary lift consists of binary $(n+1)$-spaces in $V\times\mathbb F_2$ with the given atoms as the intersections with $V\times\{0\}$ and with pairwise trivial intersections. The outside slice of each lift is a coset of its atom. By shearing in the last coordinate take the outside coset of the infinite atom to be $V_\infty$ (suppress the outside coordinate $1$). Reduce a finite representative modulo $V_b(h)$ to $(a_b,0,z_b)$; to avoid that outside infinite coset it must have $z_b=1$, and this is sufficient. Two finite outer cosets then meet iff the second coordinates equal a common $x$, $(b+c)x=a_b+a_c$, and $T((h(b)+h(c))x)=0$. Thus the necessary and sufficient condition for a lift is
$$T\!\left(\frac{(h(b)+h(c))(a_b+a_c)}{b+c}\right)=1\qquad(b\ne c).\tag{1}$$
Conversely the outside cosets so obtained, joined to the corresponding inside atoms, are the required linear spaces. We can set $a_0=0$ by subtracting a constant, which changes no difference.

In $\mathrm{PG}(3,q)$, take the quadratic cone $X_1 X_3=X_2^2$ and the planes
$$X_0=h(b)X_1+\sqrt b\,X_2+a_b X_3,\qquad b\in F.$$
They avoid the vertex. Two cone sections meet iff
$Hu^2+\sqrt{b+c}\,uv+Dv^2=0$ has a nonzero projective solution, where $H=h(b)+h(c)\ne0$, $D=a_b+a_c$, and $(X_1,X_2,X_3)=(u^2,uv,v^2)$ up to scaling. A solution must have $v\ne0$; writing $w=Hu/(\sqrt{b+c}\,v)$ gives $w^2+w=HD/(b+c)$, solvable exactly when that trace is zero. Each plane cuts $q+1$ points; there are $q(q+1)$ cone points other than its vertex, so pairwise disjointness is exactly the flock partition condition. This proves both implications, with the same $a_b$. The equivalence is **in the displayed coordinates**, not a claimed equivalence of arbitrary isomorphism classes of spreads and flocks.

## A short exponent argument

Set $d=s-1$, $N=q-1$. For $h(t)=t^s$, (1) reads $T((b+c)^d(a_b+a_c))=1$. Each multiplicative translate $b\mapsto t^d a_{tb}$ is another solution. Sum these solutions for all $t\in F^*$; the right side remains one since $N$ is odd. The result is zero at zero and is $A b^{-d}$ elsewhere, with $A=\sum_{u\ne0}u^d a_u$. Alternatively this is projection to the complementary homogeneous component of (1). Therefore any solution implies some such monomial solution; the converse is immediate. The equations involving zero say $T(A)=1$. For the other pairs, put $r=b/c\in F^*\setminus\{1\}$; the requirement is
$$T(A P(r))=1,\qquad P(R)=(1+R)^d(1+R^{-d})
 =\sum_{j=1}^d(R^j+R^{-j}).$$
The last identity uses the $k$ low binary ones of $d$. The two exponent intervals are disjoint modulo $N$, since $2d<N$. At $r=1$ the left side is zero, so on the multiplicative group the target is the unique reduced polynomial $\sum_{e=1}^{N-1}R^e$, by the geometric sum. Reduction in $F[R]/(R^N-1)$ is unique as a function on $F^*$ (degree $<N$).

Represent each $1\le e<N$ as its $n$-bit word: it is neither all zero nor all one. The positive interval $[1,d]$ is characterized by $m$ leading zeros; its negatives are their bitwise complements, with $m$ leading ones. Modulo $N$, multiplication by two rotates these words cyclically. Hence the coefficient of $R^e$ in $T(AP(R))=\sum_i A^{2^i}P(R)^{2^i}$ sums $A^{2^i}$ exactly for the rotations back by $i$ that start with a constant block of $m$ bits. There is no constant coefficient.
* If $m\ge3$, take an alternating cyclic word when $n$ is even, or an alternating word with a single doubled bit when $n$ is odd. No cyclic run reaches length three. Its coefficient is zero for **every** $A$, contradicting the required one.
* If $m=2$, necessarily $n$ is odd since $\gcd(k,n)=1$. Take $A=1$, so $T(A)=1$. The number of equal adjacent cyclic pairs is $n$ minus the even number of changes, hence odd: every required coefficient is one.
* If $m=1$, all rotations contribute and each coefficient is $T(A)$; choose any $A$ of trace one.

That proves the criterion for all admissible parameters. At $k=n-1$, after the coordinate change $h(t)=\sqrt t$ and $T(\sqrt t\,x)=T(tx^2)$, exactly Dempwolff's Example 3.4(b). At $k=1$ the atoms start in his Theorem 3.5 coordinates. The case $n=3,k=1$ belongs to the cubic endpoint.

## Why the old classification already implies this

[T. Penttila and L. Storme, *Monomial Flocks and Herds Containing a Monomial Oval* (1998)](https://doi.org/10.1006/jcta.1997.2855), §1.3 equation (2) and §2.1 equations (3)–(4), already isolate the exponent $1-e$ when the first coefficient of a flock is the power $t^e$. Their equation (3) is (1) in this paired-monomial case, with coefficient $A$. Their Lemma 3.1, Theorems 3.3 and 4.12 and the proofs of Theorems 5.1–5.2 classify the raw exponents **before** taking projective equivalence. The ordered pairs $(e,1-e)$, in $\mathbb Z/N$, are $(1/2,1/2)$ and, in odd dimension, both orders of $(1/4,3/4)$ and $(1/6,5/6)$. These describe respectively the linear, FTWKB, and Payne examples for paired monomials; we do not assume that the second coefficient of an arbitrary unaveraged solution is monomial.

In our first coefficient $e=2^k$ is fixed, not adjustable by an oval equivalence. For $n\ge3$, $1/2$ forces $k=n-1$, and $1/4$ forces $k=n-2$. The equality $e=3/4$ would rotate one bit to the two in $3$; $e=1/6$ would rotate the two bits of $6$ to one bit. For the remaining odd-dimensional case $e=5/6$, rotating the two cyclically adjacent bits of $6$ cannot produce the nonadjacent bits of $5$ when $n\ge5$. At $n=3$ it merely repeats $k=1$, since $5/6=1/4=2\pmod7$. For $n=2$ the sole admissible index is the linear case. Thus the earlier classification **implies the same criterion** under the displayed bridge. Projective classification of underlying hyperovals alone would not be a valid argument: in the standard oval $\{(1,t,t^e)\}\cup\{(0,1,0)\}$ the assigned point at infinity matters. For $q\ge8$, $e=2$ is the pointed conic orientation, while $e=1/2$ is a conic.

**Stronger explicit antecedent.** [C. M. O’Keefe and T. Penttila, *Characterisations of Flock Quadrangles* (2000)](https://doi.org/10.1023/A:1005153406421), proof of Theorem 1, Steps 1–3, pp. 184–185, especially Step 1, equation (3), p. 184, and Theorems 7–8, pp. 178–181 ([paper text](https://www.academia.edu/17920535/Characterisations_of_flock_quadrangles)), treat precisely a normalized clan with first coefficient $t^\alpha$ for a Frobenius $\alpha=2^i$. Their equation (3) is (1) after moving the factor $(b+c)^{\alpha-1}$ to the denominator. They explicitly deduce $i=n-1$ or $i=n-2$, without assuming the second coefficient is monomial. Steps 2–3 apply their Theorem 8 (stated p. 179): after normalization at zero the second coefficient must be $C t^{1/2}$ with $T(C)=1$ when $\alpha=1/2$, or $t^{3/4}+B^{1/4}t^{1/2}+B^{1/2}t^{1/4}$ with $B\in F$ when $\alpha=1/4$ ($n$ odd). This use concerns exactly these two Frobenius cases, not arbitrary oval polynomials. Thus the clan-side parameter classification is not just implicit in 1998: it is explicit by 2000. The fixed-coordinate link to Dempwolff’s later named question, the Boolean semibent and degree formulation, and the independent short exponent proof are the scope of this note.

[U. Dempwolff, *Geometric and design-theoretic aspects of semibent functions II* (2012)](https://doi.org/10.1007/s10623-011-9511-3), Example 3.4(b), Theorem 3.5, §4 Definition (a), Example 4.2(d), and the closing Remarks (b) after Example 4.3, is the source of the partial-spread formulation and its open question for $k=1$, $2n+1\ge11$. See the [author-posted manuscript](https://www.researchgate.net/publication/220638584_Geometric_and_design-theoretic_aspects_of_semibent_functions_II) and the [1998 paper text](https://www.academia.edu/176593764/Monomial_Flocks_and_Herds_Containing_a_Monomial_Oval). We did not locate an earlier explicit application of this correspondence to that question; negative searches are not a priority guarantee. The 1998 and 2000 articles did not discuss the later question by name.

## Checks

Run with Python 3.10 or later, with no dependencies:

    python3 verify_field.py
    python3 verify_geometry.py

The first enumerates every field parameter $A$ and every ratio for all admissible $k$, $2\le n\le10$, and checks the algebraic degree by full truth table for $n\le6$. The second changes field basis and multiplication/trace implementation, verifies every pair of actual outer cosets for positive cases, and obtains Gauss-elimination contradictions with fully independent, **unaveraged** offset variables in negative cases. Its printed positive number counts pairs checked; its negative number is the number of labels in the inconsistent subsystem, not a claim of smallest support. These are finite regression checks; the proofs above treat unbounded $n$.
