# An extension-complexity obstruction for the balanced semiprime graph

Write $\operatorname{bit}_B(x)$ for the padded length-$B$ binary expansion, with digit positions indexed from zero at the least significant bit. Let
$$
P_B=\operatorname{conv}\{(\operatorname{bit}_B(p),\operatorname{bit}_B(q),
      \operatorname{bit}_{2B}(pq)):
      2^{B-1}\le p<q<2p,\ q<2^B,\ p,q\text{ prime}\}.
$$
This is a single exact graph polytope for **all** the possible balanced products and their two distinct factors. For all sufficiently large $B$,
$$
\operatorname{xc}(P_B)\ \ge\ (3/2)^{\lfloor\sqrt{B/5}\rfloor}
 =2^{\Omega(\sqrt B)}. \tag{1}
$$
Here extension complexity counts inequalities in an arbitrary real linear extended formulation projecting exactly onto $P_B$; unrestricted affine equalities may be taken free.

This is a barrier to compact exact LP descriptions of that whole bit-vector graph, including formulations with extra variables. It is not a general lower bound for integer factorization, for an input-specific formulation with $pq$ already fixed, for approximate convex models, or for integer programs. The proof does not recover any factors of supplied products.

## Carry-separated multiplication

Let $m=\lfloor\sqrt{B/5}\rfloor$, $C=m^2+3$, $G=B-C$, and $H=G-C-3$. For large $B$ we have $0<H<G$. For arbitrary $x,y\in\{0,1\}^m$, define two length-$C$ cores
$$
a(x)=4\cdot2^{m^2}+\sum_{i=0}^{m-1}x_i2^i,\qquad
b(y)=6\cdot2^{m^2}+\sum_{j=0}^{m-1}y_j2^{mj}.
$$
The remainder terms are below $2^{m^2}$. The cores therefore occupy disjoint ranges, both with $C$ bits. The low $m^2$ bits of their product are precisely the bits $x_i y_j$ at positions $i+mj$: the terms involving one of the two fixed constants are all multiples of $2^{m^2}$, and the variable-variable terms have distinct positions below $m^2$.

Now allow **any** low paddings $0\le r,s<2^H$:
$$
p=2^G a(x)+r,\qquad q=2^G b(y)+s.
$$
Their bits in positions $H,\ldots,G-1$ are zero. These zero positions prevent the padding from changing the readout of the core product. In fact the part of $pq$ apart from $2^{2G}a(x)b(y)$ is
$$
2^G(a(x)s+b(y)r)+rs
<2^{G+C+H+1}+2^{2H}<2^{2G},
$$
by $H=G-C-3$. Thus for every padded pair the product bits at positions $2G+i+mj$ are exactly $x_i y_j$, independent of the padding. Every such pair also satisfies
$$
4\cdot2^{G+m^2}\le p<5\cdot2^{G+m^2},
\qquad 6\cdot2^{G+m^2}\le q<7\cdot2^{G+m^2}.
$$
In particular both are $B$-bit integers and $p<q<2p$.

## Primality can be enforced without affecting the core readout

For each $x$, the integer interval $[2^G a(x),2^G a(x)+2^H)$ contains a prime for all sufficiently large $B$, uniformly in $x$. The same holds for each $y$ and its interval for $q$. Indeed, $H=B-2m^2-9\ge 3B/5-9$, so $2^H-1>2^{0.525 B}$ for all sufficiently large $B$. Apply [Baker, Harman and Pintz, *The difference between consecutive primes, II*, Theorem 1](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf) at the last integer of the interval: its guaranteed backward interval lies inside the chosen padding interval. All the permitted integers are less than $2^B$, as shown above, and the lower endpoint tends to infinity with $B$. No statement about primes with an arbitrary interleaved set of prescribed digits is required.

Consequently every pair of Boolean vectors $(x,y)$ occurs as the chosen cores of at least one prime pair contributing a point of $P_B$. This is an existence argument only.

## Correlation polytope as a projection of a face

Fix the prescribed bits of $p$ and $q$: the zero guard positions, the nonvariable core positions, and the specified leading core constants. Leave the lowest $H$ padding bits unfixed. Each fixed bit is an affine coordinate equal to $0$ or $1$, and all graph points lie in the unit cube. Their simultaneous fixing therefore defines a face $F$ of $P_B$. To see that $F$ contains only convex combinations of graph points obeying all the fixings, sum the nonnegative coordinate slack for every prescribed bit. A convex combination with total slack zero must use only points of slack zero.

Project $F$ to the $2m$ variable core bits $(x,y)$ and the $m^2$ selected product bits $z_{ij}$ at positions $2G+i+mj$. By the carry calculation and prime existence, its image is exactly
$$
Q_m=\operatorname{conv}\{(x,y,z):x,y\in\{0,1\}^m,\ z_{ij}=x_i y_j\}.
$$
On this polytope $x_i+y_i-2z_{ii}\ge0$ is valid: on graph points it equals the bit disagreement in coordinate $i$. The condition
$$
\sum_{i=0}^{m-1}(x_i+y_i-2z_{ii})=0
$$
therefore cuts out a face consisting of convex combinations of graph points with $x=y$. Project this face to $z$. The result is the correlation polytope $\operatorname{COR}(m)=\operatorname{conv}\{xx^{\mathsf T}:x\in\{0,1\}^m\}$.

Extension complexity cannot increase under a linear projection, nor under taking a face (intersect an extension with the pullback of a supporting equality). [Kaibel and Weltge](https://arxiv.org/abs/1307.3543) prove $\operatorname{xc}(\operatorname{COR}(m))\ge(3/2)^m$, so the two face/projection steps give (1).

## What the reduction uses

Separating each bilinear bit into its own product digit would already give a correlation-polytope projection for unrestricted integer multiplication. The extra arithmetic issue here is preserving all Boolean profiles when *both* inputs are constrained to be actual balanced primes. The contiguous padding interval supplies primes independently of the two profiles, and the guard positions place all padding effects below the retained product digits. Both ingredients are needed.

The bit representation and the uniform exact graph are part of the theorem. Projecting away factor bits, approximating the convex hull, or fixing a single product in advance gives different questions not answered by this proof. A [finite exact checker](verify_factor_semiprime_polytope.js) checks the bit arithmetic, carry separation, and diagonal face identities on predetermined toy cores and paddings. It does not factor any input; the all-profile prime existence follows from the cited theorem, not finite checking.
