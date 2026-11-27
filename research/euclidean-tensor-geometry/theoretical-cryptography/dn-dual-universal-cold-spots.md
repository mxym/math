# All-scale Gaussian cold spots of the \(D_n\) and \(D_n^*\) lattices

## The fixed-lattice result

For a lattice \(L\subset\mathbb R^n\), define the inhomogeneous Gaussian sum
\[
F_{\alpha,L}(x)=\sum_{v\in L}e^{-\alpha\|x-v\|^2},\qquad\alpha>0.
\]
A deep hole is a point maximizing \(d(x,L)\). This note proves that, for each \(\alpha>0\), the minimizers of \(F_{\alpha,L}\) are exactly all deep holes for **both**
\[
D_n=\{v\in\mathbb Z^n:\textstyle\sum_i v_i\ \text{even}\},
\qquad
D_n^*=\mathbb Z^n\cup\left(\mathbb Z^n+\tfrac12\mathbf1\right).
\]
These formulas apply also to \(n=1,2\) with the indicated coordinate definitions. The result is the spatial minimization for each fixed lattice, not optimization over lattice shapes or densities.

The minimizing classes in these normalizations are as follows. Set \(P(t)=\sum_{m\in\mathbb Z}e^{-\alpha(m-t)^2}\), \(M(t)=\sum_{m\in\mathbb Z}(-1)^m e^{-\alpha(m-t)^2}\), and \(A=P(0)\), \(B=P(1/2)\), \(C=P(1/4)\). Coordinates for \(D_n^*\) are listed modulo \(\mathbb Z^n\), with half-translation identifying pairs of representatives.

| Lattice | Every minimizing point | Minimum |
|:--|:--|:--|
| \(D_n,\ n<4\) | Integer coordinates of odd total parity | \((A^n-M(0)^n)/2\) |
| \(D_4\) | Integer coordinates of odd total parity, or all coordinates half-integers | \(B^4/2=(A^4-M(0)^4)/2\) |
| \(D_n,\ n>4\) | All coordinates half-integers | \(B^n/2\) |
| \(D_n^*,\ n\) even | \(n/2\) coordinates \(0\), \(n/2\) coordinates \(1/2\) | \(2(AB)^{n/2}\) |
| \(D_n^*,\ n\) odd | One coordinate \(1/4\) or \(3/4\), \((n-1)/2\) coordinates of each of \(0,1/2\) | \(2C(AB)^{(n-1)/2}\) |

This directly addresses the geometric question in Bétermin's [Remark 5.10 of *Minimal Soft Lattice Theta Functions*](https://doi.org/10.1007/s00365-019-09494-x), for the FCC and BCC in dimension three, and also corrects the BCC representative listed there. In the unit-density BCC normalization of that article, the representative is \(2^{1/3}(1/2,1/4,0)=2^{-2/3}(1,1/2,0)\) up to symmetry and translation. The printed point \(2^{-2/3}(1,1,0)\), in the Cartesian coordinates of its displayed BCC basis, is neither a deep hole nor a Gaussian minimizer, at any \(\alpha>0\). See section 4 for the covering radii.

## 1. One-dimensional facts used in both proofs

The function \(P\) is even and of period one. Poisson summation and the [Jacobi triple product](https://dlmf.nist.gov/20.5) give, for \(q=e^{-\pi^2/\alpha}\), the representation
\[
P(t)=a(c)=K\prod_{j\ge1}(1+\beta_j c),\qquad
c=\cos(2\pi t),\qquad
\beta_j=\frac{2q^{2j-1}}{1+q^{4j-2}}\in(0,1),\quad K>0.
\tag{1}
\]
For fixed \(\alpha>0\), \(\sum_j\beta_j<\infty\) and \(1-\beta_1>0\); the product and differentiated logarithms converge uniformly on \([-1,1]\). The product is strictly increasing in \(c\) and strictly convex: differentiating twice gives positive terms \(a(c)\beta_i\beta_j/[(1+\beta_i c)(1+\beta_j c)]\) from distinct factor pairs. Consequently \(P\) is strictly decreasing in \(t\) on \([0,1/2]\), and \(A+B>2C>0\).

The sum \(M\) is even and changes sign under a unit translation. On \([0,1/2]\),
\[
0\le r(t)=\frac{M(t)}{P(t)}<1,\qquad r(0)>0,\quad r(1/2)=0,
\]
and \(r\) is strictly decreasing. In fact, if \(E(t)=\sum_{m\in2\mathbb Z}e^{-\alpha(m-t)^2}\), then \(P(t)=E(t)+E(1-t)\) and \(M(t)=E(t)-E(1-t)\). The period-two sum \(E\) strictly decreases on \([0,1]\), by (1) applied with parameter \(4\alpha\) and argument \(t/2\). Thus \(E(t)\) decreases and \(E(1-t)\) increases on \([0,1/2]\), and the stated assertions follow.

## 2. The parity lattice: a \(D_4\) identity and a power comparison

The parity projector gives the direct formula
\[
F_{\alpha,D_n}(x)=\tfrac12\left(\prod_{i=1}^n P(x_i)+\prod_{i=1}^n M(x_i)\right).
\tag{2}
\]
Write \(t_i\in[0,1/2]\) for the distance from \(x_i\) to the nearest integer. Set \(a_i=P(t_i)\), \(b_i=M(t_i)\). Then \(P(x_i)=a_i\) and \(|M(x_i)|=b_i\), so (2) is bounded below by \((\prod a_i-\prod b_i)/2\). Hölder's inequality, applied to the two nonnegative entries \(b_i\) and \((a_i^n-b_i^n)^{1/n}\) in each factor, gives
\[
\prod a_i-\prod b_i
\ \ge\ \prod_{i=1}^n (a_i^n-b_i^n)^{1/n}.
\tag{3}
\]
For \(n>1\), equality is possible only when the ratios \(b_i/a_i\) are all equal: the two-entry vectors of \(n\)-th powers must be proportional, and their second entries are positive. At \(n=1\) (3) is an identity.

To minimize each scalar factor in (3), use the orthogonal half-Hadamard matrix
\[
H=\tfrac12
\begin{pmatrix}
1&1&1&1\\ 1&1&-1&-1\\ 1&-1&1&-1\\ 1&-1&-1&1
\end{pmatrix}.
\]
It preserves \(D_4\): the four row sums against any \(v\in D_4\) are even before division by two, the resulting coordinate total is \(2v_1\), and \(H^2=I\). In particular
\[
H(1+t,t,t,t)=(1/2+2t,1/2,1/2,1/2).
\]
The product of \(M\)'s in (2) changes sign on the first input, and vanishes on the second. Equating both values proves
\[
P(t)^4-M(t)^4=P(1/2+2t) B^3.
\tag{4}
\]
Equation (1) shows that \((P(t)^4-M(t)^4)^{1/4}\) has minimum \(B\) at exactly \(t=0,1/2\) on the reduced interval.

For the other powers, set
\[
\psi_n(r)=\frac{(1-r^n)^{1/n}}{(1-r^4)^{1/4}},\qquad
\frac{d}{dr}\log\psi_n(r)
=\frac{r^3-r^{n-1}}{(1-r^n)(1-r^4)}\quad(0<r<1).
\tag{5}
\]
The scalar factor \((P(t)^n-M(t)^n)^{1/n}\) is the fourth-power factor from (4) times \(\psi_n(r(t))\). For \(n<4\), \(\psi_n\) is strictly decreasing in \(r\), so its minimum in \(t\) is uniquely \(t=0\). This point is also one of the minima of the fourth-power factor, proving it is the unique scalar minimum. For \(n>4\), the strict increase of \(\psi_n\) in \(r\) proves a unique scalar minimum at \(t=1/2\) by the same argument. For \(n=4\) the scalar minima are the two endpoints, but equality in (3) requires using just one type of endpoint. In the all-integer case one must take the negative product in (2), i.e. odd coordinate parity. In the all-half-integer case the product vanishes and no such restriction remains. These possibilities attain all the claimed values, and exclude every other point by the strictness just proved.

## 3. The body-centered lattice: strict log-concavity reduces the problem to one coordinate

For \(D_n^*\), the primal decomposition as two translated cubic lattices gives
\[
F_{\alpha,D_n^*}(x)=\prod_{i=1}^n a(c_i)+\prod_{i=1}^n a(-c_i),
\qquad c_i=\cos(2\pi x_i)\in[-1,1],
\tag{6}
\]
where \(a\) is the function in (1). Introduce the coordinates \(u(c)=\log(a(c)/a(-c))\) and \(v(c)=\log(a(c)a(-c))\). The first is strictly increasing with range \([-U,U]\), \(U=\log(A/B)>0\). The essential one-dimensional curvature is that \(v\) is **strictly concave as a function of \(u\)**. By differentiating (1),
\[
\frac{dv}{du}
=-c\,\frac{\sum_j \beta_j^2/(1-\beta_j^2c^2)}
{\sum_j \beta_j/(1-\beta_j^2c^2)}=-c\,\overline{\beta}(c).
\tag{7}
\]
Here \(\overline{\beta}(c)>0\) is the weighted mean of the \(\beta_j\) with weights \(\beta_j/(1-\beta_j^2c^2)\). The mean is an even function, nondecreasing in \(c\) for \(c\ge0\). One proof is to differentiate the weighted expectation: its derivative is the covariance under the normalized weights between \(\beta_j\) and \(2c\beta_j^2/(1-\beta_j^2c^2)\), which is nonnegative because both are increasing functions of \(\beta_j\) when \(c\ge0\). The covariance sign follows by expanding the expectation of pairwise differences over two independent samples of the weights. Thus \(c\,\overline{\beta}(c)\) is strictly increasing on the entire interval. Since \(u\) strictly increases with \(c\), (7) proves strict concavity.

Taking logs in (6) gives
\[
\log F_{\alpha,D_n^*}(x)
=\log2+\tfrac12\sum_i v(c_i)+\log\cosh\left(\tfrac12\sum_i u(c_i)\right).
\]
At fixed \(\sum_i u(c_i)\), if two coordinates were interior, one could vary them by opposite small increments of \(u\). The resulting strictly concave function on that segment cannot be minimized at its interior point. Every global minimum therefore has **at most one** \(c_i\) in the open interval.

Fix the other \(n-1\) endpoint values, with \(j\) plus endpoints and \(l\) minus endpoints. The remaining profile is
\[
A^jB^l a(c)+B^jA^l a(-c).
\]
It is strictly convex. If \(j=l\), its unique minimizer is \(c=0\). If \(j>l\), its derivative at \(c=-1\) is positive: by differentiating the product in (1),
\[
\frac{a'(1)}{a'(-1)}
=\frac{A}{B}\,
\frac{\sum_m \beta_m/(1+\beta_m)}{\sum_m \beta_m/(1-\beta_m)}
<\frac{A}{B}\le (A/B)^{j-l}.
\]
The unique minimum of the profile is therefore the opposite endpoint \(c=-1\); if \(j<l\) use reflection. Among all-endpoint points the expression \(\prod a(c_i)+\prod a(-c_i)\) is minimized when the coordinate counts are as balanced as possible, because after factoring \((AB)^{n/2}\) it is twice a hyperbolic cosine of the count difference times \(\tfrac12\log(A/B)\).

When \(n\) is even, no \(j=l\) is possible among the other \(n-1\) coordinates, so only balanced endpoints can minimize. When \(n\) is odd, the best all-endpoint value is \((AB)^{(n-1)/2}(A+B)\), strictly larger than the balanced-others midpoint value \(2(AB)^{(n-1)/2}C\). The pattern of \(c\)'s is exactly the one in the table: \(c=0\) means \(x_i=1/4\) or \(3/4\) modulo one. This proves strictness off the claimed patterns.

## 4. Identification with all geometric deep holes

The geometric classification can be derived without the Gaussian analysis.

* For \(D_n\), choose nearest integers in each coordinate and let \(t_i\in[0,1/2]\) be the absolute coordinate errors. If the resulting integer point has even parity, the squared distance to \(D_n\) is \(\sum_i t_i^2\). If it has odd parity and \(t_{\max}=\max t_i\), it is \(\sum_i t_i^2+1-2t_{\max}\): changing parity requires changing an odd number of rounded integers, and the cheapest single-coordinate parity change costs \(1-2t_{\max}\). Indeed every altered rounded integer costs at least the corresponding \(1-2t_i\ge0\), and the nearest other integer realizes it. Ties at \(1/2\) are harmless. In the odd case this is bounded by \(nt_{\max}^2+1-2t_{\max}\), strictly convex in \(t_{\max}\); the maximum over the interval is the larger of \(1,n/4\), with only endpoint equality. The even case is bounded by \(n/4\). The endpoints give exactly the types in the table, so the squared covering radius is \(\max(1,n/4)\).
* For \(D_n^*\), reduce by integer translations and coordinate reflections to \(t_i\in[0,1/2]\). Squared distance is the smaller of \(\sum t_i^2\) and \(\sum(1/2-t_i)^2\). Their difference equals \(\sum t_i-n/4\). By the simultaneous replacement \(t_i\mapsto1/2-t_i\), it is enough that \(\sum t_i\le n/4\), when the first sum is the smaller. If the sum is strictly below \(n/4\), some \(t_i<1/2\) can be increased with the total still at most \(n/4\), increasing the first sum. At equality of totals, maximizing \(\sum t_i^2\) forces at most one interior coordinate, by strict convexity along a two-coordinate transfer at fixed sum. The total fixes the balanced patterns in the table. The squared covering radius is \(n/8\) for even \(n\) and \((2n-1)/16\) for odd \(n\).

Thus all geometric holes and all Gaussian minima coincide. In particular the BCC representative \((1/2,1/2,0)\) has squared distance \(1/4\) in our unscaled coordinates, whereas \((1/2,1/4,0)\) has squared distance \(5/16\). At all scales their Gaussian values are respectively \(AB(A+B)\) and \(2ABC\), strictly ordered by (1).

## 5. Consequences and a limit of the cubic hypothesis

The same minimizing sets apply to any nonzero positive mixture of Gaussian potentials on \((0,\infty)\), provided the resulting lattice sums are finite at all shifts under comparison. Indeed integrate the strict pointwise inequality away from the common minimizing set; Tonelli applies to the positive summands. This uses only spatial minimization, and in particular makes no universal-optimality claim over variable lattices.

The curvature argument in section 3 also yields a reduction for a body-centered box with unequal side lengths \(s_i\): replacing \(\alpha\) by \(\alpha s_i^2\) in coordinate \(i\) only changes its \(u_i\) interval and its strictly concave function \(v_i(u_i)\). Thus still at most one cosine coordinate is interior at a minimum, and optimizing each remaining strictly convex scalar profile gives a finite reduction. Cubic symmetry is used in the subsequent balancing argument.

The deep-hole conclusion itself does not extend to all unequal boxes. For example, take \(L=\operatorname{diag}(2,1)D_2^*\). In coordinates \(x=(2t,u)\), reduce to \(0\le t,u\le1/2\). For fixed \(u\), the maximum of the smaller of \(4t^2+u^2\) and \(4(1/2-t)^2+(1/2-u)^2\) occurs where they coincide: \(4t+u=5/4\), since the first increases and the second decreases strictly. The coincident value is strictly convex in \(u\), so reaches its maximum at \(u=0\) or \(1/2\), giving reduced deep holes \(t=5/16\) or \(3/16\), respectively. But the dual lattice is \(\{(m_1/2,m_2):m_1+m_2\text{ even}\}\), whose unique shortest pair is \(\pm(1,0)\), with next squared norm \(5/4\). For \(\alpha\to0^+\), normalize the Gaussian sum by its constant Fourier term. The leading nonconstant term is \(2e^{-\pi^2/\alpha}\cos(4\pi t)\), with uniform error \(O(e^{-5\pi^2/(4\alpha)})\) by the convergent dual theta sum. It is strictly lower at \(t=1/4\) than at either deep-hole value by a fixed positive fraction of \(e^{-\pi^2/\alpha}\). For sufficiently broad Gaussians these geometric deep holes are therefore not cold spots, consistent with, but not implied by, the reduction.

## Prior work and reproducibility

Bétermin's Remark 5.10 poses the fixed-lattice FCC/BCC question described above. Bachoc, Moustrou, Vallentin, and Zimmermann's [*Polarization of lattices: Stable cold spots and spherical designs*](https://doi.org/10.1017/fms.2026.10169) proves the cold spot statement for root lattices when \(\alpha\) is sufficiently large, and uses the standard \(D_4\) Hadamard symmetry. Here that symmetry is used to produce the all-scale scalar identity (4); the dual-family argument (7) is different. The [November 2026 Palomar record](https://open-research-index.vercel.app/r/palomar/PALOMAR-2026-11-19-000011) on universal cold spots lists other lattices and \(D_n^+\), not the sequences \(D_n\) and \(D_n^*\) in this note; see also its [pinned primary theorem statement](https://github.com/caiusdfolkerts/research/blob/9fcbca1143471e6e25c337def9897b58377e0b4c/cold_spots/Challenge.lean). This comparison is not a claim of exhaustive priority.

Run **node verify-dn-dual-universal-cold-spots.js** for exact rational-shift squared-distance shell identities, covering patterns, and numerical regression of Gaussian sums and the BCC curvature; it uses only built-in assertions. The proof for all positive widths is analytic and does not rely on grid sampling.
