# Exactly when one phase removes Gaussian Fourier aliases

Squaring coherent Gaussian amplitude sums need not agree with folding squared amplitudes. Can one deterministic phase twist make the two quotient laws identical? For a lattice with an orthogonal integral basis the answer is yes, exactly and at every width. For a nonorthogonal lattice the answer is no at sufficiently large even-grid separation, even if the phase is retuned at each width. The obstruction is a Delaunay triangle, and in rank two it gives the exact optimized exponential rate and a two-case prefactor.

The model is an ideal finite Fourier measurement law, not a preparation or decoding algorithm, a modification of a computational reduction, or a claim about an implementation.

## 1. Exact alias formula

Let \(L\subset\mathbb R^d\) be a full-rank Euclidean lattice, \(R\ge1\) an integer, \(t>0\), and \(e(z)=e^{2\pi i z}\). A phase is an arbitrary \(\theta\) in the dual torus \(\mathbb R^d/L^*\). On \(L/RL\) compare the normalized laws
\[
 Q(y)\ \propto\ \sum_{x\in y+RL}e^{-2t\|x\|^2},
 \qquad
 P_\theta(y)\ \propto\
 \left|\sum_{x\in y+RL}e^{-t\|x\|^2} e\bigl(\langle x,\theta\rangle/R\bigr)\right|^2 .
 \tag{1}
\]
Changing the representative of \(\theta\) modulo \(L^*\) gives each amplitude a constant phase on its residue, so the law is unchanged. The sum for the zero residue is nonzero: by Poisson it is an everywhere positive periodization of a Gaussian, up to a positive constant. Write \(\tau=tR^2/2\).

Expanding the square and pairing the two lifts \(x,x+Rv\) gives the real signed coefficients
\[
 S_g(\theta,\tau)=\sum_{v\in g+2L} e^{-\tau\|v\|^2}e(\langle v,\theta\rangle),
 \qquad g\in L/2L,
\]
and expressible weights before normalization
\[
 \sum_{g\in L/2L} S_g(\theta,\tau)
       \sum_{x\in y+RL} e^{-2t\|x+Rg/2\|^2}.                 \tag{2}
\]
The identity is completion of the square, and the inner sum is unchanged when the lift of \(g\) changes by \(2L\). Signs within a parity coset pair \(v\) with \(-v\); thus imaginary parts cancel. Formula (2) is valid for either parity of \(R\).

If \(R\) is even, the inner sums are translates of the unnormalized \(Q\), centered at the distinct half-shifts \(Rg/2\bmod RL\). Write \(S=\sum_g S_g\) and regard the coefficients as signed masses on this subgroup. The exact relation is
\[
 P_\theta-Q= \frac{1}{S}Q*\sum_{g\ne0}S_g
              \bigl(\delta_{Rg/2}-\delta_0\bigr).             \tag{3}
\]
Here \(\delta_a\) is a point mass; the sign of the shift is immaterial because it has order two. The centered Gaussian Fourier coefficients of \(Q\) are all strictly positive by Poisson summation, so convolution by \(Q\) is injective on this finite group. Hence for even \(R\), equality is equivalent to \(S_g=0\) for every \(g\ne0\). For odd \(R\) this condition is still sufficient by (2), without an assertion of necessity.

## 2. Orthogonal construction and all-dimensional rigidity

Suppose \(b_1,\ldots,b_d\) is an orthogonal integral basis of \(L\). Choose
\[
        \langle b_i,\theta\rangle\equiv \tfrac14\pmod{\tfrac12}
        \qquad(1\le i\le d).
 \tag{4}
\]
In each parity coset the Gaussian sum factors across the basis coordinates. An odd coordinate's one-dimensional factor vanishes by pairing \(k\) and \(-k\), since \(e(k/4)\) has real part zero for odd \(k\). Thus all \(S_g\) except \(S_0\) vanish and (1) agrees exactly for **all** positive \(t\) and **all** \(R\).

Here is the converse and a uniform quantitative statement. If \(L\) is not orthogonal, there exist three strict Voronoi vectors \(v_1,v_2,v_3\) with \(v_3=v_2-v_1\). Let \(M=\max_i\|v_i\|^2\). For all sufficiently large \(\tau\) and even \(R\),
\[
       \inf_\theta d_{\rm TV}(P_\theta,Q)\ge c_L e^{-\tau M}
       \tag{5}
\]
for some positive constant \(c_L\). Thus allowing a fresh optimal phase at each width does not give exactness. For an orthogonal lattice, (4) describes every phase that is exact for all sufficiently large \(\tau\) on even grids: the parity of a single basis vector has exactly the two shortest lifts \(\pm b_i\), so its leading coefficient forces (4) for a fixed phase.

We give the geometry and then the bound. A strict Voronoi vector \(v\) is a neighbor across a facet of the lattice-centered cell. Equivalently, \(\pm v\) are the only shortest vectors in \(v+2L\). For one direction, the latter condition says that at \(v/2\) only \(0,v\) are nearest sites, giving a facet. Conversely a different \(w\in v+2L\) of norm no greater supplies \(a=(v+w)/2,b=(v-w)/2\) in \(L\), \(a+b=v\). On the putative facet the two inequalities for \(a,b\) imply
\[
 \|v\|^2/2\le(\|a\|^2+\|b\|^2)/2
             =(\|v\|^2+\|w\|^2)/4.
\]
If \(\|w\|<\|v\|\) this is impossible; if equal and \(w\ne\pm v\), the two independent equalities force codimension at least two.

By Voronoi–Delaunay duality, the edges of Delaunay polytopes have strict Voronoi vectors as differences. We recall why the absence of triangular Delaunay 2-faces would force orthogonality. A Delaunay 2-face is a convex cyclic polygon with no lattice points other than its vertices in its convex hull: any other such point would lie strictly inside its empty sphere. Its affine plane meets the ambient lattice in a translate of a rank-two lattice. By reducing the vertices modulo twice that plane lattice, it can have at most four vertices, since two of the same parity would have a lattice midpoint. An empty convex lattice quadrilateral is a fundamental parallelogram. Indeed its diagonal splits it into two empty lattice triangles, each of area one-half in lattice units by Pick's formula. In coordinates taking the primitive diagonal from \((0,0)\) to \((1,0)\), the other vertices are \((a,1),(b,-1)\) with integer \(a,b\); convexity forces \(0<(a+b)/2<1\), hence \(a+b=1\). Because it is cyclic, such a parallelogram is a rectangle.

If every Delaunay 2-face were a rectangle, a full-dimensional Delaunay cell would then be a zonotope, by the classical characterization by centrally symmetric 2-faces. For any two nonparallel generating directions, the span of that pair admits a supporting functional vanishing on the span but not on any generator outside it. The resulting two-face has the generator directions in the span as its edge directions. Being a rectangle, it has two perpendicular lines. Thus the generator lines of the full cell are pairwise perpendicular and the cell is an orthogonal box. In dimension two use the whole cell directly for this argument. Let \(L_0\) be the lattice spanned by the edges of the box from a vertex. If \(L_0\) were proper in \(L\), a representative of a nonzero coset in the half-open box would be strictly closer to the center than the vertices, contradicting emptiness. Hence the box edges give an orthogonal integral basis of \(L\). This proves that a nonorthogonal lattice has a triangular 2-face, whose three edge lengths give \(v_1,v_2,v_3\). Their three parity classes are distinct and nonzero, since otherwise one of the strict vectors would lie in \(2L\).

The three phases in a triangle must satisfy, for all real \(x,y\),
\[
        \max\{|\cos x|,|\cos y|,|\cos(y-x)|\}\ \ge\ 1/2.
 \tag{6}
\]
If both of the first two absolute cosines are less than \(1/2\), both angles modulo \(\pi\) lie in \((\pi/3,2\pi/3)\). Their difference modulo \(\pi\) then has absolute cosine at least \(1/2\). For a strict vector \(v_i\), its parity sum has leading term \(2e^{-\tau\|v_i\|^2}\cos(2\pi\langle v_i,\theta\rangle)\), with an exponentially smaller next shell **uniformly** in \(\theta\) (compare at \(\tau\ge1\) with the convergent Gaussian sum). Thus (6) guarantees that one nonzero parity weight has absolute size at least a fixed positive multiple of \(e^{-\tau M}\).

Finally, (3) converts this to TV without a condition on the two rates \(t,R\) separately. Put \(\lambda=\min_{v\ne0}\|v\|\) in the fixed lattice. The balls of radius \(R\lambda/8\) around the half-shifts on \(L/RL\) are disjoint: distinct centers are at least \(R\lambda/2\) apart. The folded \(Q\) lies outside the ball about zero with probability at most
\[
  e^{-t(R\lambda/8)^2}\,
    \frac{\sum_{x\in L}e^{-t\|x\|^2}}{\sum_{x\in L}e^{-2t\|x\|^2}}
 \le 2^{d/2}e^{-t(R\lambda/8)^2},
\]
where the last ratio bound follows by Poisson summation and comparison on the dual lattice. If this probability is \(\epsilon_R\), convolution with \(Q\) on signed half-shift masses has \(\ell^1\) norm bounded between \(1-2\epsilon_R\) and \(1\) times their original \(\ell^1\) norm, by summing the masses in the disjoint balls and using the triangle inequality. Also \(S=1+O(e^{-\tau\lambda^2})\) uniformly. In particular, with an error factor tending to one uniformly in \(\theta\) as \(\tau\to\infty\),
\[
 d_{\rm TV}(P_\theta,Q)
   = (1+o(1))\,
       \max\left\{\sum_{g\ne0}(S_g)_+,\ \sum_{g\ne0}(-S_g)_+\right\}.
 \tag{7}
\]
This gives (5) and will also give sharp constants in the plane.

## 3. Exact optimized planar limit

Take a nonorthogonal rank-two lattice. Choose a Gauss-reduced integral basis \(a,b\) with \(A=\|a\|^2\le B=\|b\|^2\) and \(0<c=\langle a,b\rangle\le A/2\), making the angle acute by a sign change. Such a basis can be obtained by extending a primitive shortest vector and reducing the second vector by integer multiples of the first; if the reduced inner product were zero the lattice would be orthogonal. Put \(C=\|b-a\|^2=A+B-2c\ge B\). Then for even \(R\), along any \(\tau=tR^2/2\to\infty\),
\[
 \boxed{\quad
 \lim e^{\tau C}\inf_{\theta}d_{\rm TV}(P_\theta,Q)
   =\begin{cases}
          2,&C>B,\\
          \sqrt2,&C=B .
     \end{cases}
 \quad}                                                       \tag{8}
\]

First check the parity shells. The three shortest parity pairs are precisely \(\pm a,\pm b,\pm(b-a)\) in their respective classes, each unique up to sign. Indeed
\[
 \|j a+k b\|^2=A(j+ck/A)^2+(B-c^2/A)k^2,\qquad B-c^2/A\ge 3B/4.
\]
In the \(a\) class either \(k=0\), giving the pair, or \(|k|\ge2\), giving length squared at least \(3B\). In the other classes \(|k|\ge3\) cannot minimize, and for \(k=\pm1\) minimizing the first square among even or odd \(j\) respectively gives the other pairs; strictness uses \(c>0\).

Write \(x=2\pi\langle a,\theta\rangle,y=2\pi\langle b,\theta\rangle\). At every width, the parity weights in (7) have uniform leading equivalents \(2e^{-\tau A}\cos x,2e^{-\tau B}\cos y,2e^{-\tau C}\cos(y-x)\), in the sense of exponentially smaller additive remainders at each respective scale.

* **\(C>B\).** Choose \(x=y=\pi/2\). In each of the first two parity classes the cosine vanishes for every lift (the coordinate sum is odd). The third weight has scale \(2e^{-\tau C}\), giving the upper bound. Any sequence of phases with TV \(O(e^{-\tau C})\) must have \(\cos x,\cos y\to0\) by (7) and the two shorter lengths, so \(|\cos(y-x)|\to1\). The third weight gives the matching lower bound.
* **\(A<B=C\).** A sequence achieving TV \(O(e^{-\tau C})\) must have \(\cos x\to0\). The two longest weights then give a normalized lower bound \(\sqrt2-o(1)\) because the maximum of the two absolute cosines of arguments separated by \(\pi/2+o(1)\) is at least \(1/\sqrt2-o(1)\). Choose \(x=\pi/2,y=-\pi/4\) for the upper bound. The parity class of \(a\) contributes only from lifts with nonzero even \(k\) (all others have zero cosine), hence contributes \(o(e^{-\tau C})\) since \(3B>C\). The other two leading weights are opposite, of size \(\sqrt2 e^{-\tau C}\).
* **\(A=B=C\).** Put \(u=\cos x,v=\cos y,w=\cos(y-x)\). The identity \(u^2+v^2+w^2-2uvw=1\) is the vanishing Gram determinant of three unit planar vectors. If all three cosines have the same sign, their total absolute sum is at least one, by this identity and \(|u|,|v|,|w|\le1\). Otherwise call \(p,q\) the two magnitudes of the same sign and \(s\) the third magnitude, allowing zeros. Then \(1\le(p+q)^2+s^2\), since the possible product term is at most \(2pq\). Hence the maximum of total positive and total negative mass of \((u,v,w)\) is at least \(1/\sqrt2\). The choice \(x=\pi/4,y=-\pi/2\) attains it with \((1/\sqrt2,0,-1/\sqrt2)\); multiply by the factor two from the paired shells.

In each case (7) turns this into (8); compactness allows a minimizing sequence and the lower bounds are uniform over the phases in that sequence. There is no optimization claim for odd grids in (8).

## 4. Primary comparisons and scope

- [Regev, *On lattices, learning with errors, random linear codes, and cryptography*, Lemma 3.14](https://cims.nyu.edu/~regev/papers/qcrypto.pdf) and [Peikert–Regev–Stephens-Davidowitz, Lemma 6.7](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) provide the context for the ideal periodized amplitude. They control the untwisted approximation error. The earlier [coherent-Gaussian mesh note](coherent-gaussian-mesh.md) analyzes its parity weights and product limits at zero phase. This note instead optimizes the deterministic twisted ideal law; no step of either reduction is being replaced here.
- [Dutour Sikirić, Madore, Moustrou and Vallentin, *Coloring the Voronoi tessellation of lattices*](https://doi.org/10.1112/jlms.12456) and [Vallentin, Weißbach and Zimmermann, *The chromatic number of 4-dimensional lattices*](https://doi.org/10.1016/j.indag.2024.11.006) supply the Voronoi-graph terminology and lattice Delaunay viewpoint. [Shephard, *Polytopes with centrally symmetric faces*](https://doi.org/10.4153/CJM-1967-109-3) records the classical zonotope characterization. The phases-to-triangle argument and sharp planar TV optimization use those geometric facts, not a new general theorem on lattice graph coloring.

The verifier checks toy orthogonal products, parity-class lengths, phase signs and the planar limiting constants; the analytic bounds, not the numerical tests, supply the all-width and all-lattice claims.
