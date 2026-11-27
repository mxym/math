# Detecting the exceptional kissing codes by one harmonic moment

Take **any** $N=72$ unit vectors in $\mathbb R^6$ or $N=126$ in $\mathbb R^7$, with pairwise inner products at most $1/2$. No labeling, symmetry, or distinguished subset is needed. Let $P_7$ be the degree-seven zonal polynomial in the ambient dimension, normalized by $P_7(1)=1$, and put $M_7=N^{-2}\sum_{ij}P_7(x_i\cdot x_j)$.

**Gap theorem.** If
$$
 M_7\le\frac{7}{8564244480}\quad(d=6),\qquad
 M_7\le\frac{221}{4092566962176}\quad(d=7),
$$
then the code is **exactly isometric** to the $E_6$ or $E_7$ root configuration, respectively. Every other code of that size has moment strictly above the threshold, not merely nonzero. The normalized thresholds are approximately $8.17\cdot10^{-10}$ and $5.40\cdot10^{-11}$, respectively; we do not assert they are optimal.

There is also a labeled error bound for approximate data below, and we compute the entire exact spectrum of the tangential contact operator. [Cohn, Jiao, Kumar and Torquato](https://msp.org/gt/2011/15-4/gt-v15-n4-p11-p.pdf) already proved infinitesimal jamming of these codes; jamming itself is not new. [The single-index bound](KissingSingleHarmonicObstructions.md) characterized the zero moment. Here we give an explicit **unframed** one-moment recognition radius and **quantitative** local conditioning. These results do not determine the unrestricted kissing number in either dimension.

## 1. One moment bounds global rounding error

Put $S=\{-1,-1/2,0,1/2\}$. Use the polynomial
$$
 g(t)=t^2(2t-1)(2t+1)^2(1+t)(3-2t)/12 .
$$
On the entire interval $[-1,1/2]$ one has the sharp scalar estimate
$$
                       -g(t)\ \ge\ (21/256)\operatorname{dist}(t,S)^2. \tag{1}
$$
Indeed split the interval at the four roots and their adjacent midpoints. On each of the six resulting segments the nearest root $z$ is fixed; every Bernstein coefficient of $-g(t)-(21/256)(t-z)^2$ is nonnegative. The [rational checker](verify-kissing-harmonic-recognition.py) verifies all six instances directly. At $t=-1/4$ there is equality with nonzero distance.

Write $b=5/32$ or $128/663$, respectively. The [degree-seven calculation](KissingSingleHarmonicObstructions.md#1-a-closed-formula-at-degree-seven) gives constant coefficient $g(1)/N$ and nonnegative other coefficients, except the coefficient $-b$ at index seven. The spherical addition formula therefore implies
$$
                 \sum_{i\ne j}-g(x_i\cdot x_j)\le bN^2 M_7 .
$$
Round the Gram matrix $G$ to $G_0$ by preserving the unit diagonal and symmetrically choosing nearest values in $S$ off the diagonal. Then its **entire** Frobenius rounding error is bounded by
$$
               D^2=\|G-G_0\|_F^2 \le (256/21)bN^2 M_7 . \tag{2}
$$
The thresholds in the theorem make $D\le1/h$, with $h=352$ or $704$. The next step makes no prior assumption that a rounded Gram matrix is realizable.

## 2. Quantization preserves dimension and positivity

If $D=0$ the rounding step is immediate. Otherwise, we claim that $G_0$ is itself positive semidefinite of rank at most $d$. For a square $r$-by-$r$ mixed submatrix of $G$, the nuclear norm is at most $r$: write it as $X_I^tX_J$ for unit-column matrices and apply the Frobenius product bound. The corresponding rounded submatrix has nuclear norm at most $r+\sqrt rD$.

Consider first a mixed minor of order $r=d+1$. The original submatrix was singular, so the rounded one has a singular value at most $D$. Its absolute determinant is therefore at most
$$
         D\left(\frac{r+\sqrt rD}{r-1}\right)^{r-1}
          \le D\exp(1+\sqrt rD)<(11/4)D.
$$
Every such determinant is an integer multiple of $2^{-r}$, and $(11/4)/h=2^{-(d+1)}$. It must vanish. Thus the rank is at most $d$. For a principal minor of order $2\le r\le d$, if its determinant were negative there would be a negative eigenvalue. Its magnitude is at most $D$, since the original principal submatrix is positive semidefinite. The same determinant estimate then contradicts the denominator $2^r$. The diagonal is positive, and all larger minors vanish. The principal-minor criterion proves the claim. The check $\exp(1+3/352)<11/4$ suffices in both dimensions.

The rounded matrix now represents $N$ genuine unit vectors, all distinct, with products in $S$. Adding their negatives still gives a kissing code. The [classical antipodal bound and uniqueness](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) force the rounded configuration to be exactly $E_d$ up to orthogonal labeling. It remains important to eliminate small actual deformations: discrete rounding of $G_0$ did not prove $G=G_0$.

## 3. The exact tangential spectrum

Let $b_i$ be the unit root vectors, $i\sim j$ mean $b_i\cdot b_j=1/2$, and $l$ be their common contact degree (20 or 32). On the space of tangent motions $w_i\perp b_i$, $w_i\in\mathbb R^d$, define
$$
       (A w)_{\{i,j\}}=b_i\cdot w_j+b_j\cdot w_i\quad(i\sim j).
$$
Each unordered edge occurs exactly once. The eigenvalues of $A^tA$, with multiplicities as superscripts, are
$$
\begin{array}{c|l}
E_6&0^{15},\, (3/2)^{70},\,2^{81},\,3^{60},\,(9/2)^{114},\,6^{20}\\
E_7&0^{21},\,2^{112},\,3^{210},\,4^{189},\,6^{147},\,(13/2)^{56},\,8^{21}.
\end{array}
$$
In particular the kernel consists precisely of the infinitesimal rotations (which already have the stated nullity). Denote the least positive eigenvalue by $\kappa$.

Here are details of the fully integer verification. Use the $E_8$ vectors $r_i$ of length $\sqrt8$: the signed permutations of $(2,2,0,\ldots,0)$ and the all-$\pm1$ vectors with an even number of minus signs. Impose coordinates $r_7+r_8=0$ for $E_7$, and also $r_6+r_8=0$ for $E_6$; set $b_i=r_i/\sqrt8$. For each edge, an integer row with blocks $2r_j-r_i,\,2r_i-r_j$ at $i,j$ is $\sqrt{32}$ times its tangential contact row, extended by zero on radial and out-of-span directions. Its Gram operator $T$ is thus $32 A^t A$ on the tangent subspace. The checker shows that the product of $(T-\lambda I)$ over the proposed **distinct** scaled eigenvalues (including zero) annihilates the eight coordinate vectors at one chosen site. It verifies site transitivity by traversing the root reflections, which are orthogonal symmetries intertwining $T$; thus that product annihilates the whole space. No other eigenvalues are possible. For their multiplicities, the trace of $T^j$ is $N$ times the sum of the eight diagonal entries at the site for every $j$. Exact trace checks for $j$ from zero through at least the number of distinct eigenvalues minus one determine all multiplicities by a Vandermonde system. Removing $N(8-d+1)$ invisible directions gives the table. The same verifier checks
$$
       \sum_i b_i b_i^t=(N/d)I\ \text{on the root span},\qquad
       \sum_{j\sim i} b_j=(l/2)b_i.
$$

## 4. Quantitative local recognition, including perturbed contacts

More generally suppose that $G_0=B^tB$ is the **labeled** root Gram matrix, and $G=X^tX$ is any other unit-column Gram matrix in the same ambient dimension with $D=\|G-G_0\|_F\le1/25$. Permit a contact excess $\delta=\max(0,\max_{i\sim j}(x_i\cdot x_j-1/2))$. Then
$$
       U=\min_{Q\in O(d)}\|X-QB\|_F \ \le\ \frac{5|E|}{2\sqrt\kappa}\,\delta ,
$$
where $|E|=720$ or $2016$. In particular for an actual kissing code $\delta=0$ and the configuration is exactly the root code. This applies after the label recovery in §2 since $1/h<1/25$.

To prove it, set $s=N/d$, $P=B^tB/s$, an orthogonal projector, and $F=XB^t/s$. We have $XP=FB$ and $\|F^tF-I\|_F\le D/s$. A polar orthogonal factor of $F$ thus differs from $F$ by at most $D/s$ in Frobenius norm (apply $|\sigma-1|\le|\sigma^2-1|$ to each singular value). Also $\sigma_{\min}(X)\ge\sqrt{s-D}$ from the spectrum of $G_0$ and the perturbation bound; hence $\|X(I-P)\|_F\le D/\sqrt{s-D}$ as $X^tX(I-P)=(G-G_0)(I-P)$. The two row subspaces are orthogonal, giving
$$
            U^2\le D^2(1/s+1/(s-D)) <\kappa/(9l^2),\qquad U^2<1/100
$$
at the stated radii (use $\le$ in the initial bound when $D=0$).

Align optimally and write $x_i=b_i+u_i$, so $\sum\|u_i\|^2=U^2$ and $b_i\cdot u_i=-\|u_i\|^2/2$. The tangent parts $w_i=u_i+(\|u_i\|^2/2)b_i$ are orthogonal collectively to all rotations by stationarity of the optimal alignment. Thus
$$
         \|Aw\|_2\ge\sqrt\kappa\,U\sqrt{1-U^2/4}.
$$
The sum over all entries of $Aw$ is zero by the contact balance above. Each entry is at most $\delta-u_i\cdot u_j+(\|u_i\|^2+\|u_j\|^2)/4$, hence its positive part is at most $\delta+3(\|u_i\|^2+\|u_j\|^2)/4$. For any zero-sum vector its norm is at most $\sqrt2$ times its total positive part. Therefore
$$
     \sqrt\kappa\,U\sqrt{1-U^2/4}
        \le\sqrt2\bigl(|E|\delta+3lU^2/4\bigr).
$$
Substituting $U<\sqrt\kappa/(3l)$ and $U^2<1/100$ yields the asserted Lipschitz bound. This concludes both the noisy labeled estimate and the one-moment gap theorem.

**Replay:** `python3 verify-kissing-harmonic-recognition.py`. The checker uses only the Python standard library. The spectra are certified exactly, not read off a floating-point eigensolver.
