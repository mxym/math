# Two parallel latitude bands cannot contain 72 or 124 kissing points

Let $C$ be any spherical $60^\circ$ code in $\mathbb R^n$. Choose any polar axis and any two angular latitudes, not assumed opposite. Put
\[
 s=\frac{4001}{8000},\qquad
 \delta=\tfrac12\bigl(\pi/3-\arccos s\bigr)
        \simeq 0.004135139^\circ.
\]
**Theorem.** The union of the two closed latitude bands of half-width $\delta$ contains at most **71** points if $n=6$, and at most **123** if $n=7$. In particular the same bounds apply to any two parallel hyperplane sections of the sphere. They are upper bounds; attainment is not asserted.

Thus for every choice of axis and band centers, a hypothetical 73-point code in six dimensions has at least two points outside the bands, and a hypothetical 127-point code in seven dimensions has at least four. The result applies to arbitrary subsets of arbitrary codes, without any group, lattice, antipodality or root-system assumption. It does not by itself give either unrestricted kissing number.

## Reduction to two prescribed heights

Move each point of the two-band subset along a meridian to an assigned central latitude. This moves each through spherical angle at most $\delta$; at a pole a meridian may be chosen arbitrarily. Triangle inequality shows that every new separation is at least $\pi/3-2\delta=\arccos s>0$, so no points coincide. We need a bound for a code of maximal scalar product $s$ on **two exact latitudes**, uniformly over the two heights. If the two signed heights have the same sign, reflect one labeled layer in the equator. Within-layer scalar products stay the same; between layers they can only decrease. We may therefore take signed heights $h_0$ and $-h_1$, with $h_i\ge0$, and relabel so $h_0\le h_1$.

Use rational parameters $0\le z_i\le1$:
\[
 h(z)=\frac{2z}{1+z^2},\qquad r(z)=\frac{1-z^2}{1+z^2}.
\]
The normalized transverse directions lie on $S^{n-2}$. For their scalar product $u$ the upper thresholds for same-layer and cross-layer pairs are
\[
 b(z)=\frac{s-h(z)^2}{r(z)^2},\qquad
 c(z_0,z_1)=\min\left(1,\frac{s+h(z_0)h(z_1)}{r(z_0)r(z_1)}\right).
\]
The same-layer cutoff decreases with $z$; the cross cutoff increases with either parameter. A cutoff below $-1$ means there are no off-diagonal pairs of that type.

For $z_1\ge9/32$ we use two independent ordinary scalar Delsarte bounds in dimension $n-1$, at cutoffs $s$ and $b(9/32)$. They give at most $46+23=69$ points in dimension six, and at most $83+35=118$ in dimension seven. Their nonnegative polynomial coefficients are included in the data and checked over the whole intervals. A polar layer with $r=0$ has at most one point and satisfies the same bound without division by zero. It remains to treat $0\le z_0\le z_1\le9/32$.

## A positive kernel coupling the two layers

Let $P_k$ denote the normalized spherical Gegenbauer polynomial for $\mathbb R^{n-1}$. For a given pair of heights take real positive semidefinite $2\times2$ matrices $A_0,\ldots,A_{10}$, and set
\[
 F_{ij}(u)=1+\sum_{k=0}^{10}(A_k)_{ij}P_k(u),\qquad i,j\in\{0,1\}.
\]
The initial one is present in **every** matrix entry. In particular the off-diagonal entries of an individual $A_k$ need not be positive. The addition formula makes $P_k$ a positive semidefinite kernel on the transverse sphere. Multiplying by $(A_k)_{ij}$ preserves positivity on the labeled points (Gram tensor products, or the Schur product theorem). This is the classical Delsarte principle applied with two labels; compare the general rotational positive-kernel framework of [Bachoc and Vallentin](https://arxiv.org/abs/math/0610856).

For each pair of radii the certificate has $F_{ii}(1)<N$, where $N=72$ or $124$ respectively, and $F_{ij}(u)\le0$ at **every** allowed off-diagonal scalar product of that type. For $m$ labeled points summing over ordered pairs gives
\[
 m^2\ \le\ \sum_{x,y}F_{\ell(x),\ell(y)}(u_{xy})
 \ \le\ \sum_x F_{\ell(x),\ell(x)}(1)\ <\ Nm .
\]
Thus $m\le N-1$, independently of the populations of the two layers.

## The continuum certificate

The [rational data](kissing-two-latitude-certificates.json) describe a finite cover by closed dyadic squares. A square crossing the diagonal is checked on its whole area. The triangular parameter region is verified by recursive covering, not by sampling. Each corner stores eleven matrices, divided by $10^7$. Inside the patch, interpolate the **matrices themselves** using the four bilinear rectangle weights. Those weights are nonnegative and sum to one, preserving positive semidefiniteness and the diagonal bounds. Neighboring patches need not use the same certificate at shared points.

To certify the off-diagonal signs on a smaller rectangle, bound the admissible $u$ by its worst cutoff using the monotonicity above. At each fixed $u$ every entry polynomial is bilinear in the two radii parameters on the patch. Its maximum on the subrectangle occurs at a corner. It is therefore sufficient to certify the four corner polynomials on the entire univariate interval $[-1,u_{\max}]$. When this sufficient test is inconclusive, bisect and interpolate afresh. Coefficients at a subdivision are kept with a common positive scaling; they are not independently normalized before interpolation.

The [standard-library verifier](verify-kissing-two-latitudes.py) checks exact integer determinants and both diagonal inequalities, verifies that the data cover the whole parameter triangle, and certifies the signs in either of two ways:

| Ambient dimension | Patches | Stored corner records | Bernstein radial nodes | Sturm radial nodes |
|---:|---:|---:|---:|---:|
| 6 | 173 | 234 | 87,929 | 91,845 |
| 7 | 241 | 332 | 63,841 | 66,439 |

The default method constructs the shifted Gegenbauer polynomials by recurrence, converts their restrictions to Bernstein form, and uses integer de Casteljau subdivision. The second method constructs their coefficients from the closed-form Gegenbauer formula, uses an integer signed remainder sequence to count real roots, and splits the two radial parameters in a different order. Neither accepts a floating-point sign. The optimization used to locate witnesses is not needed for replay.

The atlas strings are only zlib-compressed, base64-encoded JSON to keep the worked certificate compact. Decoding either one yields a list of patches (their dyadic endpoints, denominator exponent, and four corner indices) followed by the corner records (eleven symmetric matrices as triples of integers). The two scalar witnesses in each dimension are uncompressed.

**Replay:** put the checker and the JSON in the same directory, then run `python3 verify-kissing-two-latitudes.py` and `python3 verify-kissing-two-latitudes.py --sturm`.
