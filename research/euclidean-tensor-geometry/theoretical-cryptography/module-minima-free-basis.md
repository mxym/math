# When independent module minima control free basis lengths

For a fixed number field, does a free module lattice have an integral module basis whose individual lengths are comparable to its corresponding successive independent-vector minima, uniformly over lattices? There is an exact arithmetic criterion: **yes precisely when the maximal order is a principal ideal domain**, already in module rank two. The obstruction is that a saturated shortest line may represent a nontrivial ideal class even though the entire module is free.

This concerns the geometry of worst-case module inputs, not an algorithm for finding short vectors and not a claim about the hardness or security of Ring-LWE or Module-LWE.

## The comparison property

Let $R=\mathcal O_K$ be the maximal order of a number field $K$, with degree $d$. A module lattice here is a finitely generated $R$-submodule $M\subset K^r$ spanning $K^r$, with its canonical Euclidean length; real embeddings have weight one and complex places weight two in the squared norm. Let $\ell_i(M)$ be the least radius containing $i$ $K$-linearly independent vectors of $M$. For cyclotomic $K$, the ordinary Euclidean lattice minima of $M$ satisfy

$$
\lambda_{d(i-1)+1}(M)=\cdots=\lambda_{di}(M)=\ell_i(M).
\tag{1}
$$

Indeed all vectors of norm at most a given radius are stable under multiplying by the primitive root of unity. Hence their $\mathbb Q$-span is a $K$-space. Its rational dimension is $d$ times its dimension over $K$; the real dimension of the embedded span is that rational dimension because independent lattice vectors have rational coordinates in a lattice basis.

Consider the property that, for every free $M$ of rank $r$, there exists an $R$-basis $(b_1,\ldots,b_r)$ with $\|b_i\|\le C_{K,r}\ell_i(M)$ for all $i$. For fixed $K$ and any fixed $r\ge2$, this holds if and only if $R$ is a PID. The condition is on each basis vector relative to its corresponding minimum, not just an upper bound in terms of the last minimum.

## Positive direction with field constants

Let

- $\kappa_K$ be the covering radius of the canonical lattice $R$ in $K_{\mathbb R}$ under the maximum of the absolute embedding coordinates;
- $\alpha_K=\exp(\rho_K)$, where $\rho_K$ is the $\ell_\infty$ covering radius of the logarithmic absolute-value vectors of $R^\times$ in their weighted zero-sum hyperplane (the covering radius is zero for a zero-dimensional hyperplane).

These are finite by compactness for the additive lattice and by Dirichlet's unit theorem for the logarithmic lattice. When $R$ is a PID, there exists an $R$-basis satisfying

$$
\|b_i\|\le \alpha_K\sqrt{1+(i-1)\kappa_K^2}\,\ell_i(M)\qquad(1\le i\le r).
\tag{2}
$$

Choose $K$-independent $v_i\in M$ with $\|v_i\|\le\ell_i(M)$, successively: at each stage the vectors of the stated radius span at least the needed dimension. Set $V_i=\operatorname{span}_K(v_1,\ldots,v_i)$ and $M_i=M\cap V_i$. Each quotient $M_i/M_{i-1}$ is torsion-free of rank one, hence free over a PID. Let $\widetilde b_i$ lift its generator. The projection $\pi_i$ from $(V_i)_{\mathbb R}$ onto the orthogonal complement of $(V_{i-1})_{\mathbb R}$ acts place by place and commutes with real-extended field scalars. As $v_i$ is nonzero in the quotient, there is nonzero $a_i\in R$ with $\pi_i(v_i)=a_i\pi_i(\widetilde b_i)$.

For any $0\ne a\in R$, its log embedding vector after subtracting the average $\log|N_{K/\mathbb Q}(a)|/d$ is in the weighted zero-sum hyperplane. There is a unit $u$ within $\rho_K$ of that vector, so

$$
|\sigma_v(u)|\le \alpha_K \frac{|\sigma_v(a)|}{|N_{K/\mathbb Q}(a)|^{1/d}}
\le \alpha_K|\sigma_v(a)|
$$

at every place $v$. Apply this to $a_i$ and replace $\widetilde b_i$ by $u_i\widetilde b_i$. Its orthogonal component $b_i^*=\pi_i(u_i\widetilde b_i)$ now satisfies $\|b_i^*\|\le \alpha_K\|\pi_i(v_i)\|\le\alpha_K\ell_i(M)$.

Inductively adjust the new lift by $R$-multiples of earlier basis vectors. Process earlier indices $j=i-1,\ldots,1$: write the component along the placewise line of $b_j^*$ with scalar in $K_{\mathbb R}$ and reduce that scalar modulo $R$ into maximum absolute value at most $\kappa_K$. Subtracting a multiple of $b_j$ leaves all higher components unchanged since $b_j$ belongs to $(V_j)_{\mathbb R}$ and has component $b_j^*$ on that line. Each step leaves the chosen quotient generator unchanged. The resulting $b_i$ has orthogonal component $b_i^*$ and all coefficients on the earlier orthogonal components bounded in each embedding by $\kappa_K$. Thus

$$
\|b_i\|^2\le \|b_i^*\|^2+\kappa_K^2\sum_{j<i}\|b_j^*\|^2
\le \alpha_K^2(1+(i-1)\kappa_K^2)\ell_i(M)^2.
$$

The lifts form an $R$-basis by induction on the saturated flag. The proof uses only that the successive quotients of this flag are principal, so (2) also applies to a given flag with this property over a non-PID. The usual $K=\mathbb Q$ size-reduction bound is recovered at $\alpha_{\mathbb Q}=1$, $\kappa_{\mathbb Q}=1/2$.

## Negative direction and sharp leading coefficients

Suppose $I$ is a nonprincipal fractional ideal and $J=I^{-1}$. In rank two use $M_0=I\oplus J$ with the length

$$
\|(x,y)\|_\tau^2=\tau^{-2}\|x\|^2+\tau^2\|y\|^2,\qquad \tau\ge1.
$$

For rational $\tau$ this is the canonical lattice of $(\tau^{-1}I)\oplus(\tau J)$; the covolume is independent of $\tau$. The following determinant criterion is useful. Two columns $(x_i,y_i)\in M_0$ form an $R$-basis if and only if $x_1y_2-x_2y_1$ is a unit of $R$. The forward implication follows because the image of $\bigwedge^2 M_0$ in $K$ is $IJ=R$; the reverse follows directly from the inverse matrix and $IJ=R$.

The module is free without assuming either ideal is principal. One can choose $y_1,y_2$ generating $J$ as an ideal: fix $y_1\ne0$ and use the Chinese remainder theorem to choose $y_2$ with $y_2I$ coprime to $y_1I$, by avoiding zero in $J/\mathfrak p J$ at the finitely many primes $\mathfrak p$ dividing $y_1I$. Then $I y_1+I y_2=R$, so $x_1 y_2-x_2 y_1=1$ for suitable $x_1,x_2\in I$.

A vector $(x,y)$ can be in a basis precisely when $xJ+yI=R$, by the determinant criterion. In particular no vector with $y=0$ can be in a basis: that would make $xJ=R$ and $I$ principal. Write $l(H)$ for the Euclidean lattice minimum of a fractional ideal $H$, and set

$$
g_2(J)=\min\bigl\{\max(\|y_1\|,\|y_2\|):\ y_1R+y_2R=J\bigr\}.
$$

Let $a_\tau$ be the shortest length of a vector belonging to an $R$-basis and $b_\tau$ the least attainable maximum of the lengths of both basis vectors. For all large $\tau$ the two independent minima are $\tau^{-1}l(I)$ and $\tau l(J)$, respectively: the first is realized inside $I$, every vector independent of that line has $y\ne0$, and the second is attained by adding a shortest vector on the $J$-axis. In contrast,

$$
a_\tau=\tau l(J)+O(\tau^{-3}),\qquad
b_\tau=\tau g_2(J)+O(\tau^{-3}).
\tag{3}
$$

For the first estimate any basis vector has $y\ne0$, giving the lower bound. Fix a shortest $y$ in $J$ and choose $x\in I$ by the same local coprimality argument, this time with $xJ+yI=R$, giving the upper bound by one fixed pair. For the second estimate the two $y_i$ must generate $J$ by projection; a pair attaining $g_2(J)$ lifts to a basis of determinant 1 as above, proving the upper bound. The expansions follow by taking square roots. Therefore the first basis length divided by the first lattice minimum diverges like $\tau^2l(J)/l(I)$, even though the best maximum basis length divided by the last independent-vector minimum has a finite limit. In higher rank append $r-2$ copies of $R$ on the long side, with norm weight $\tau^2$ there and $\tau^{-2(r-1)}$ on the short $I$-axis. The full module is free. An $R$-linear functional $M\to R$ cannot take value 1 on a vector in that $I$-axis because such a value would make $I$ principal (the restriction is multiplication by some element of $I^{-1}$). Since every basis vector admits such a functional, every basis vector has a nonzero long coordinate. This proves unboundedness for each fixed $r\ge2$, again at fixed covolume.

**Exact example.** Take $K=\mathbb Q(\sqrt{-5})$, $\omega=\sqrt{-5}$, $I=(2,1+\omega)$, and $J=I/2$. The ideal $I$ has norm two and $I^2=(2)$ by direct multiplication and norms, so $J=I^{-1}$. The equation $a^2+5b^2=2$ has no integer solution, proving nonprincipality. Elements of $I$ are $a+b\omega$ with $a,b$ of the same parity. In canonical normalization, $l(I)^2=8$, $l(J)^2=2$, and $g_2(J)^2=3$ (the elements of $J$ with squared length 2 are just $\pm1$, and $1,(1+\omega)/2$ generate $J$). For $\tau^4\ge4$,

$$
\ell_1^2=8\tau^{-2},\quad \ell_2^2=2\tau^2,\quad
a_\tau^2=2\tau^2+12\tau^{-2},\quad
b_\tau^2=3\tau^2+8\tau^{-2}.
$$

For the third identity, $y=\pm1$ requires $x\notin 2R$ by the criterion $xJ+yI=R$, since the sole prime dividing $yI$ is $I$. The least such squared norm is 12; if $\|y\|^2\ge3$, then $\|x\|^2\ge8$ because $x=0$ cannot be in a basis either. For the fourth identity some $y_i$ necessarily has squared norm at least 3 and its $x_i$ has squared norm at least 8. Both bounds are attained by the determinant-one columns $(1-\omega,1)$ and $(2,(1+\omega)/2)$; the first column is no longer than the second when $\tau^4\ge4$.

**A fixed cyclotomic field with the obstruction.** For $K=\mathbb Q(\zeta_{23})$, its quadratic subfield is $F=\mathbb Q(\sqrt{-23})$. To see the inclusion, the quadratic Gauss sum $G=\sum_{a\ne0}\chi(a)\zeta_{23}^a$ is purely imaginary since $\chi(-1)=-1$; expanding $|G|^2$ with $a=tb$ gives $22-\sum_{t\ne0,1}\chi(t)=23$, so $G^2=-23$. Put $\theta=(1+\sqrt{-23})/2$. In $\mathcal O_F=\mathbb Z[\theta]$ the prime $A=(2,\theta)$ over two is nonprincipal, since $N(a+b\theta)=a^2+ab+6b^2$ cannot equal two. The distinct conjugate prime is $(2,\theta-1)$. The element $\theta-2$ has norm eight and is divisible by $A$ but not by its conjugate, so $(\theta-2)=A^3$. If $I=A R$ became principal, its ideal norm down to $F$ would give $A^{[K:F]}=A^{11}$ principal, impossible for an ideal class of order three. Thus the negative example works in a fixed cyclotomic field, with the exact multiplicities (1), rather than requiring a growing field or nonfree module.

## Relation to prior work and proof scope

[Fieker–Stehlé, §§4.1–4.3](https://perso.ens-lyon.fr/damien.stehle/downloads/OKLatRed.pdf) use saturated subspaces, size reduction and coefficient ideals to construct short pseudo-bases, including an almost-free representation. Those tools are the relevant precedent; pseudo-basis vectors and their coefficient ideals are not required to give an ordinary free basis with each entry short. Here the specific comparison is entry-by-entry against the independent-vector minima, with a PID criterion and an explicit fixed-covolume gap in the non-PID case. This is not an exhaustive priority claim.

[Langlois–Stehlé, §2 and §§3–4](https://perso.ens-lyon.fr/damien.stehle/downloads/MSIS.pdf) formulate Mod-SIVP using independent Euclidean lattice vectors; their worst-case input representation is an underlying lattice basis. These are different notions from asking for a free basis over $R$ whose individual lengths track the minima. Accordingly the counterexample does not change their hypothesis, their reduction, or the corresponding rank-one Ring-LWE results. It identifies which short-basis substitution would require additional assumptions.

[De Micheli–Micciancio–Pellet-Mary–Tran](https://opencryptology.org/2023/886) study reductions between arbitrary modules and free modules for several well-defined algorithmic tasks. This note neither analyzes those reductions nor equates freeness with the existence of a basis whose entries track the independent-vector minima.

The accompanying verifier checks the explicit quadratic norm and determinant witness, plus finite identities in the quadratic subfield used for the cyclotomic example. The general criterion follows from the proof rather than enumeration.
