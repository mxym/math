# A quadratic-overlap refinement of ternary Walsh–Hadamard rigidity

Let \(N=2^n\), \(G=\mathbb F_2^n\), and \(H[x,y]=(-1)^{x\cdot y}\).
For a matrix over \(\mathbb F_3\), rank-r rigidity is the minimum
number of entries to change to obtain rank at most r over that
field. Edits here are arbitrary, including changes to zero.

**Theorem.** For every integer \(n\ge100000\),
\[
 R^{\mathbb F_3}_{H}\!\left(\left\lfloor\frac{n^2}{80}\right\rfloor\right)
     > \frac{667}{5000}N^2 = 0.1334\,N^2 .
\]
Asymptotically at the same rank, the argument proves every fixed
edit fraction below
\[
 \delta_*=\frac{a-2^{(h_*-1)/2}}{b}
        \simeq 0.13343291539,\qquad
 a=\frac{\sqrt6+\sqrt2}{4},\quad
 b=\frac{\sqrt6+3\sqrt2}{4},\quad
 h_*=\frac{8\kappa}{1+6\kappa},\quad \kappa=\frac{\log_2 3}{80}.
\tag{1}
\]

[Alman, arXiv:2608.06592](https://arxiv.org/html/2608.06592)
gives the signed-probe/Bessel framework and a 1% lower bound
at this target rank. [Maksov, Zenodo 24571049](https://doi.org/10.5281/zenodo.24571049)
introduces the asymmetric \(3\pi/4\) target phase; its
[author abstract](https://aixiv.online/abs/2611.03141) reports
13% and a trade-off reaching about 13.2632% asymptotically.
Here we use that same phase. The new estimate treats the
overlap on the intersection as a \(\mathbb Z/4\)-valued
quadratic Gauss sum and uses an additional random Gram rank
constraint. This improves the edit fraction, not the
\(\Theta((\log N)^2)\) rank scale, and does not prove either
Valiant or Razborov rigidity. We compare to the earlier
reported numerical result, not to a comprehensive priority
claim about possible overlap methods.

## 1. Probes and a surviving signal

Fix even \(k\le n/3\). A probe \(\alpha\) consists of a uniform
ordered independent k-tuple \(y_j\) in G and independent uniform
signs \(\varepsilon_j\). Form
\(a_\alpha=\sum_j\varepsilon_j e_{y_j}\) over \(\mathbb F_3\).
Suppose a rank-r matrix L over \(\mathbb F_3\) differs from H
at a fraction at most \(\delta\) of entries. Use the unit vectors
\[
 \begin{split}
 p_\alpha(x)&=N^{-1/2}
      \exp\!\left(\frac{3\pi i}{4}
                    \sum_{j=1}^k\varepsilon_j H[x,y_j]\right),\\
 q_\alpha(x)&=N^{-1/2}\omega^{(La_\alpha)_x},\qquad
 \omega=e^{2\pi i/3}.
 \end{split}
\tag{2}
\]
The first sum in (2) is an integer sum, not a mod-three sum.
The low-rank encoding \(q_\alpha\) takes at most \(3^r\) values.

Initially draw the y's independently with replacement. For a
fixed x, averaging its contribution to \(\langle q_\alpha,p_\alpha\rangle\)
over the independent signs gives the product of k real
one-coordinate factors. The per-column factor is
\(\cos(3\pi H[x,y]/4-(2\pi/3)L[x,y])\), interpreting the two
possible nonzero mod-three values as \(1,-1\).
For an unchanged entry it is \(a=\cos(\pi/12)\).
For an edited entry its minimum is \(-1/\sqrt2\), reached at
a change to zero; an edit to the opposite sign gives
\(\cos(17\pi/12)>-1/\sqrt2\). With row edit fraction
\(\delta_x\), the average factor within that row is at least
\(a-b\delta_x\), where \(b=a+1/\sqrt2\).
The mean correlation on the with-replacement distribution is
the average of the k-th powers of these real row means.
By the convexity of the even power and Jensen, it is at least
\(\rho^k\), where \(\rho=a-b\delta>0\) in the regime used below.

The probability of drawing a dependent tuple is at most
\(\sum_{j=0}^{k-1}2^{j-n}<2^{k-n}\). As inner products have
absolute value at most one, conditioning on independence
gives
\[
 \operatorname{Re}\mathbb E_\alpha\langle q_\alpha,p_\alpha\rangle
      \ge \rho^k-2^{k-n} \ge \rho^k/2
\tag{3}
\]
when \(\rho\ge 2^{-1/2}\), \(k\le n/3\), and \(n\ge2\).
The second inequality follows from \(2^{k-n}/\rho^k
 \le2^{3k/2-n}\le2^{-n/2}\).

We use the following form of Alman's small-output bound:
for any positive integer s,
\[
 \big|\mathbb E\langle q_\alpha,p_\alpha\rangle\big|^{2s}
 \le 3^r\,
        \mathbb E_{\alpha,\beta}|\langle p_\alpha,p_\beta\rangle|^s.
\tag{4}
\]
For completeness take s-th tensor powers after using Jensen,
group the probes by their common \(q_\alpha\), and multiply
the \(p_\alpha^{\otimes s}\) within each group by scalar unit
phases making their inner products with that group's
\(q^{\otimes s}\) nonnegative. Cauchy–Schwarz in each group
bounds its sum by the norm of its tensor sum. A second
Cauchy–Schwarz over at most \(3^r\) groups and expansion of
the summed squared norms give (4), after bounding the
within-group overlaps by the sum of all absolute overlaps.

## 2. Exact conditional overlap by a quadratic form

The Fourier expansion of \(p_\alpha\) in the normalized
Walsh basis is flat in absolute value on its k-dimensional
span U, and zero off U. Indeed
\(e^{3\pi i\varepsilon H/4}=(-1/\sqrt2)(1-i\varepsilon H)\).
If \(u_\alpha(z)\in\mathbb F_2^k\) is the coordinate vector
of \(z\in U\) in the ordered basis of the probe, then the
coefficient at z is
\[
 (-1)^k 2^{-k/2}(-i)^{|u_\alpha(z)|}
                  \prod_j\varepsilon_j^{u_\alpha(z)_j}.
\]
Let V be the span of \(\beta\), \(I=U\cap V\), and \(d=\dim I\).
Thus the overlap is
\[
 2^{-k}\sum_{z\in I} i^{Q(z)}(-1)^{\ell(z)},\qquad
 Q(z)=|u_\alpha(z)|-|u_\beta(z)|\pmod4,
\tag{5}
\]
where, conditional on the two ordered bases and the first
set of signs, \(\ell\) is a uniform linear functional on I.
The signs of the second probe are independent and restriction
from \(\mathbb F_2^k\) to the embedded I is surjective on
linear functionals.

The polarization of Q is
\(Q(x+y)-Q(x)-Q(y)=2B(x,y)\bmod4\), with
\[
 B(x,y)=u_\alpha(x)\cdot u_\alpha(y)
             +u_\beta(x)\cdot u_\beta(y)
 \quad\text{over }\mathbb F_2.
\]
If \(w=\operatorname{rank}B\), its radical has dimension
\(d-w\). Squaring the Gauss sum in (5) and changing variables
shows its squared modulus (before the factor \(2^{-2k}\))
equals
\[
     2^d\sum_{z\in\operatorname{rad}B} i^{Q(z)}(-1)^{\ell(z)}.
\]
On the radical, Q is even and \(Q/2\) is linear: set \(x=y\)
in polarization for evenness, then use additivity there.
Hence this square is \(2^{2d-w}\) if
\(\ell|_{\operatorname{rad}B}=Q/2\), and zero otherwise.
The conditional probability of the nonzero case is
\(2^{-(d-w)}\). Therefore the conditional s-th moment over
the second set of signs is exactly
\[
 2^{-ks+(d-w/2)s-(d-w)} .
\tag{6}
\]
This is the additional quadratic overlap information, beyond
the flat-support bound \(2^{d-k}\).

## 3. Counting low-rank Gram differences

Fix the first ordered basis, and condition on the second
subspace V, not its ordered basis. For the fixed subspace
intersection I choose any basis. The map \(u_\beta|_I\)
is a uniform injective map \(I\to\mathbb F_2^k\), since the
second ordered basis is uniform and the general linear
group acts transitively on injective maps.

For any prescribed symmetric d-square Gram matrix, its
probability for such an injection is at most
\(4\cdot2^{-d(d-1)/2}\). In fact, at the step after choosing
j independent columns, the prescribed j off-diagonal
inner products of the next column are j independent
linear constraints. There are at most \(2^{k-j}\)
acceptable candidates among \(2^k-2^j\) choices.
Ignoring diagonals and multiplying yields the bound, using
\(\prod_{i\ge1}(1-2^{-i})\ge1/4\). This product bound follows
from the first factor \(1/2\) and
\(\prod_{i\ge2}(1-2^{-i})\ge1-\sum_{i\ge2}2^{-i}=1/2\).

The number of symmetric d-square binary matrices of rank w
is at most \(4\cdot2^{dw-w(w-1)/2}\). Choose their image
space in at most \(4\cdot2^{w(d-w)}\) ways by the Gaussian
binomial formula. For a fixed full-column-rank basis matrix
A of that space, a symmetric matrix with image there has
form \(ACA^{\mathsf T}\) with C symmetric of size w.
To see this, if D is any left inverse of A then the
matrix equals \(A(D K D^{\mathsf T})A^{\mathsf T}\), using
both its image and its row space. This gives at most
\(2^{w(w+1)/2}\) choices. Translation by the fixed first
Gram matrix makes the same bound applicable to B.

Combining these two count bounds with (6), for \(s\ge2k+2\)
the factor depending on w in the resulting moment sum
is at most one: its exponent is
\(w(d+1-s/2)-w(w-1)/2\le0\).
Thus at a fixed intersection dimension d the conditional
moment is at most
\[
   16(d+1)\,2^{-ks+ds-d-d(d-1)/2}.
\]
Finally, for uniform k-space V and fixed U, the probability
that \(\dim(U\cap V)\ge d\) is at most
\(16\cdot2^{-d(n-2k+d)}\):
union bound over d-spaces in U, and the chance a fixed
one is contained in V is
\(\prod_{j=0}^{d-1}(2^k-2^j)/(2^n-2^j)\).
The Gaussian binomial and product bounds supply the two
factors at most four. Summing over d, and maximizing the
resulting concave quadratic over all real \(d\ge0\), gives
\[
 \mathbb E_{\alpha,\beta}|\langle p_\alpha,p_\beta\rangle|^s
 \le 256(k+1)^2\,
      2^{-ks+(s-n+2k-1/2)_+^2/6}.
\tag{7}
\]
The quadratic penalty before maximization is \(3d^2/2\):
one \(d^2\) from intersection probability and the additional
\(d^2/2\) from the Gram difference. This step does not
assume the two restricted bases or Gram matrices agree.

## 4. The edit bound

Write \(h=1+2\log_2\rho\). From (3), (4), (7),
every such approximation must satisfy
\[
 r\log_2 3\;\ge\;
 k s h-\frac{(s-n+2k-1/2)_+^2}{6}
       -2s-8-2\log_2(k+1).
\tag{8}
\]
For the explicit theorem take \(k=2\lfloor 7n/50\rfloor\),
\(s=2k+2\), and \(\delta=667/5000\).
We have \(h>2837/20000=0.14185\) and
\(\log_2 3<317/200=1.585\). Both inequalities can be
checked entirely with integers: lower-bound the square
roots in \(\rho\) by \(24494897/10^7\) and \(14142135/10^7\),
respectively, obtaining \(\rho>37137/50000\), then raise
\(2(37137/50000)^2\) to power 20000 and compare to \(2^{2837}\).
For the second use \(3^{200}<2^{317}\).
Also \(7n/25-2\le k\le7n/25\) and
\(8+2\log_2(k+1)\le n\) in the stated range.
Using \(ks\ge2(7n/25-2)^2\) and
\((s-n+2k-1/2)_+\le 3n/25+3/2\), the right side of
(8) exceeds \((n^2/80)\log_2 3\) by at least
\[
  \frac{1479}{50000000}n^2
      -\frac{312218}{125000}n-\frac{35}{8}.
\]
This is positive at \(n=100000\) and strictly increasing
thereafter. The contradiction proves the finite assertion.

For the asymptotic statement, let \(k/n\to\alpha\), with
even k and \(s=2k+2\). For h in the range \(0<h\le1/3\)
choose \(\alpha=1/(4-3h)\in[1/4,1/3]\).
After dividing (8) by \(n^2\) its right hand side tends to
\(2\alpha^2h-(4\alpha-1)^2/6=h/(8-6h)\).
This exceeds \(\log_2 3/80\) exactly when \(h>h_*\)
in (1). The parameter range contains a neighborhood of
this threshold, and monotonicity in the allowed edit
fraction handles all smaller fractions. This establishes
(1) without claiming a bound at the exact endpoint.

The optional exact replay
~~~sh
python3 verify_factor_walsh_hadamard_quadratic_overlap.py
~~~
verifies the finite integer constants, checks the injection
Gram point bound in small dimensions, and directly evaluates
the Gaussian integer sums in (5) on checked small examples.
The general result is by the displayed proof, not a
numerical rank search.
