# Sharp binary-quartic rigidity and the optimal order of tensor error bounds

Research note, 7 October 2026. Complete written proofs with a partial Lean
formalization of the scalar quartic certificate. Literature comparison is
preliminary; no priority assertion is made.

## 1. Statements and conventions

Let $T$ be a real fully symmetric order-$p$ tensor on $\mathbb R^2$, with
$p\geq3$. Write $t_k$ for an entry having exactly $k$ indices equal to 2.
Our tensor norm and associated polynomial are
\[
 \|T\|_F^2=\sum_{k=0}^p\binom pk t_k^2,
 \qquad f_T(x,y)=\sum_{k=0}^p\binom pk t_k x^{p-k}y^k.
\]
The orthogonally decomposable class is
\[
 \mathcal D_{2,p}=\{a u^{\otimes p}+b v^{\otimes p}:
        (u,v)\text{ an orthonormal basis},\ a,b\in\mathbb R\}.
\]
Zero, repeated and negative weights are allowed. For every **ordered** index
tuple $\alpha\in\{1,2\}^{p-2}$, let
$(X_\alpha)_{ij}=T_{\alpha,i,j}$, and set
\[
 R_p(T)^2=\sum_{\alpha,\beta\in\{1,2\}^{p-2}}
                       \|[X_\alpha,X_\beta]\|_F^2.
\]
Thus $R_p$ has degree two in $T$; it is already a square root of a sum of
squared commutator norms. This convention matters for all constants below.
Let $d_p(T)=\operatorname{dist}_F(T,\mathcal D_{2,p})$.

**Theorem 1 (binary all-orders bound).** For every $p\geq3$,
\[
 d_p(T)\leq\frac{\sqrt p}{2}\sqrt{R_p(T)}.
\]
In particular, $R_p(T)=0$ if and only if $T\in\mathcal D_{2,p}$.

**Theorem 2 (sharp quartic bound and equality).** For $p=4$,
\[
 d_4(T)\leq\frac{3^{1/4}}{\sqrt2}\sqrt{R_4(T)}.
\]
The constant is best possible. For $R_4(T)>0$, equality holds exactly for
nonzero real scalar multiples and orthogonal coordinate transforms of the
tensor $T_*$ with coefficients
\[
 (t_0,t_1,t_2,t_3,t_4)=(4,\sqrt3,0,\sqrt3,4).
\]
For $R_4(T)=0$, both sides vanish.

**Theorem 3 (order growth in fixed dimension).** For every $p\geq5$, the
tensor $S_p$ with
\[
 t_0=t_p=1,\quad t_1=t_{p-1}=p^{-1/2},\quad
 t_k=0\quad(2\leq k\leq p-2)
\]
satisfies
\[
 \|S_p\|_F^2=4,\qquad d_p(S_p)^2=2,\qquad
 R_p(S_p)=\frac{4\sqrt{2(p-1)}}p.
\]
Consequently, if $C_p$ is the best constant in a binary estimate
$d_p(T)\leq C_p\sqrt{R_p(T)}$, then
\[
 \frac{\sqrt p}{\sqrt2\,[2(p-1)]^{1/4}}
       \leq C_p\leq\frac{\sqrt p}{2}\qquad(p\geq5).
\]
There is no constant uniform in tensor order, even in dimension two.

**Theorem 4 (matching upper growth).** For every $p\geq3$,
\[
 C_p\leq\min\{\sqrt p/2,\ (3p/4)^{1/4}\}.
\]
In particular $C_p=\Theta(p^{1/4})$ as $p\to\infty$. An improved explicit
bound is available: define
\[
 c_p=\begin{cases}(p-1)/(p-2),&p\text{ even},\\
                 p/(p-1),&p\text{ odd}.
       \end{cases}
\]
For $p\geq9$,
\[
 C_p^2\leq\frac{p}{4\sqrt{p/(4c_p)-1}}.
\]
Thus the normalized constants satisfy
\[
 2^{-3/4}\leq\liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
 \leq\limsup_{p\to\infty}\frac{C_p}{p^{1/4}}\leq2^{-1/2}.
\]
The leading constant, and whether the normalized constants converge,
remain undetermined.

These statements are independent of entropy inequalities or any claimed
resolution in the OpenAI collection. They refine our earlier all-dimensional
tensor note, whose substantially larger dimension-dependent constants remain
valid. The earlier exact cubic constant is $\sqrt3/2$; Theorem 2 concerns the
next order, with a different equality configuration.

## 2. Distance and a two-dimensional Gram matrix

**Lemma 4 (projection formula).**
\[
 d_p(T)^2=\|T\|_F^2-
       \max_{(u,v)\text{ orthonormal}}
                      \big(f_T(u)^2+f_T(v)^2\big).
\]
For a fixed basis, the best weights are $a=f_T(u)$, $b=f_T(v)$.

**Proof.** The tensors $u^{\otimes p}$ and $v^{\otimes p}$ are orthonormal
in the Frobenius inner product. Minimize the two separate quadratic expressions
in $a,b$. A maximizing basis exists by compactness of $O(2)$ and continuity.
This also proves existence of a nearest element of $\mathcal D_{2,p}$.

Let $w_k=\binom{p-2}k$, $0\leq k\leq p-2$, and define
\[
 z_k=\begin{pmatrix}t_k-t_{k+2}\\2t_{k+1}\end{pmatrix},\qquad
 G(T)=\sum_{k=0}^{p-2}w_k z_k z_k^\top.
\]

**Lemma 5 (exact residual identity and change of basis).**
\[
 R_p(T)^2=\det G(T).
\]
Under orthogonal coordinate changes, $G$ is conjugated by an orthogonal
two-dimensional matrix. Every rotation of this trace-free coordinate plane
can be obtained by a rotation of the underlying tensor coordinates.

**Proof.** A contraction with $k$ indices equal to 2 is
\[
 X_k=\begin{pmatrix}t_k&t_{k+1}\\t_{k+1}&t_{k+2}\end{pmatrix}
\]
and appears $w_k$ times. The commutator $[X_k,X_l]$ has off-diagonal
entries $c_{kl},-c_{kl}$, where
\[
 c_{kl}=(t_k-t_{k+2})t_{l+1}-(t_l-t_{l+2})t_{k+1}
        =\tfrac12\det(z_k,z_l).
\]
Expanding the $2\times2$ determinant gives
\[
 \det G=\tfrac12\sum_{k,l}w_kw_l\det(z_k,z_l)^2
        =2\sum_{k,l}w_kw_l c_{kl}^2=R_p(T)^2.
\]
For the basis-change assertion, first index the contraction family by all
ordered tuples. A rotation $Q$ acts on its label space by the orthogonal
matrix $Q^{\otimes(p-2)}$, and on each matrix by conjugation with $Q$.
The first operation leaves the sum of the trace-free outer products
unchanged. On a matrix $X$, the vector $(X_{11}-X_{22},2X_{12})$ transforms
orthogonally under conjugation. A coordinate rotation through $\theta$
rotates this vector through $2\theta$, up to the harmless sign convention
for whether the new basis is active or passive. Therefore every plane
rotation is available. This proves the assertions, including reflections.

**Proof of Theorem 1.** Choose tensor coordinates making
$G_{22}=\lambda_{\min}(G)$ and $G_{12}=0$. Use the approximation retaining
only $t_0,t_p$ in this basis. Its squared error is
\[
 E=\sum_{k=1}^{p-1}\binom pk t_k^2
 \leq p\sum_{k=1}^{p-1}\binom{p-2}{k-1}t_k^2
 =\tfrac p4 G_{22}.
\]
Indeed,
$\binom pk/\binom{p-2}{k-1}=p(p-1)/(k(p-k))\leq p$.
As $G$ is positive semidefinite,
$G_{22}=\lambda_{\min}\leq\sqrt{\det G}=R_p(T)$.
Lemma 4 gives $d_p^2\leq E$, proving the bound. If $R_p=0$, the same
argument gives an exact decomposition. Conversely, every tensor in
$\mathcal D_{2,p}$ has diagonal contractions in its decomposing basis,
so its residual vanishes.

## 3. The sharp quartic constant

We prove $4d_4(T)^4\leq3R_4(T)^2$. The zero tensor is immediate. For a
nonzero tensor, choose a maximizing basis in Lemma 4, and write
\[
 L=t_0+t_4,\quad D=t_0-t_4,\quad h=t_1+t_3,\quad j=t_1-t_3,
 \quad t=t_2,\quad N=L^2+D^2.
\]
Here $N>0$: a nonzero homogeneous polynomial is nonzero at some point of
the unit circle, and hence the maximum projection energy is positive.
The squared distance in this basis is
\[
 E=d_4(T)^2=2(h^2+j^2)+6t^2.
\]

### 3.1 An exact criterion for a maximizing basis

On the circle, write
\[
 f_T(\cos\theta,\sin\theta)=
 a\cos4\theta+b\sin4\theta+c\cos2\theta+d\sin2\theta+e,
\]
where direct expansion gives
\[
 a=(L-6t)/8,\quad b=j/2,\quad c=D/2,\quad d=h,
 \quad e=3(L+2t)/8.
\]
The projection energy for a rotated orthonormal basis is
\[
 2(e+a\cos4\theta+b\sin4\theta)^2+
 c^2+d^2+(c^2-d^2)\cos4\theta+2cd\sin4\theta.
\]
Apart from its constant part, this is
\[
 q(z)=2(a z_1+b z_2)^2+\ell_1z_1+\ell_2z_2,
 \quad z_1^2+z_2^2=1,
\]
where $\ell_1=4ea+c^2-d^2$, $\ell_2=4eb+2cd$.
Stationarity at our chosen basis $z=(1,0)$ says
$\ell_2=-4ab$, equivalently
\[
 Lj+Dh=0.
\]
Moreover, using $z_2^2=1-z_1^2$, we have the identity
\[
 q(1,0)-q(z)=(1-z_1)
 [\ell_1+2(a^2-b^2)(1+z_1)+4abz_2].
\]
The minimum of the bracket on the unit circle is
$\ell_1+2(a^2-b^2)-2(a^2+b^2)=\ell_1-4b^2$.
Consequently, subject to stationarity, $(1,0)$ is a global maximizing
point if and only if $\ell_1\geq4b^2$. Necessity follows also when the
minimum is at $(1,0)$: a negative value there remains negative at nearby
points, for which $1-z_1>0$.

Because $N>0$, stationarity lets us write
\[
 h=sL,\qquad j=-sD
\]
for some real $s$. Put
\[
 u=L/\sqrt N,\quad \tau=t/\sqrt N,\quad \sigma=s^2,
 \qquad v=u+6\tau,\quad k=(4-v^2)/16.
\]
Then the global maximizing condition is exactly
\[
 |u|\leq1,\qquad |v|\leq2,\qquad0\leq\sigma\leq k.
\]
To check the last assertion without division ambiguities, calculate
\[
 16(\ell_1-4b^2)=4N-(L+6t)^2-16s^2N.
\]

### 3.2 A complete nonnegative polynomial certificate

The Gram entries of Lemma 5 in this basis are
\[
 G_{11}=\tfrac12(L-2t)^2+\tfrac12D^2+2j^2,
 \quad G_{22}=2(h^2+j^2)+8t^2,\quad G_{12}=2tj.
\]
Thus
\[
 \frac{R_4^2}{N^2}=
 (\tfrac12-2u\tau+2\tau^2+2\sigma(1-u^2))(2\sigma+8\tau^2)
       -4\tau^2\sigma(1-u^2),\qquad
 \frac E N=2\sigma+6\tau^2.
\]
Let $P=(3R_4^2-4E^2)/N^2$. Expansion yields
\[
 \begin{split}
 P={}&3\sigma+12\tau^2-12u\tau\sigma-48u\tau^3\\
 &-(48+36u^2)\tau^2\sigma-(4+12u^2)\sigma^2-96\tau^4,
 \qquad \tau=(v-u)/6.
 \end{split}
\]
For fixed $u,v$ this is a strictly concave quadratic in $\sigma$.
Its endpoint values have the following exact factorizations:
\[
 P(u,v,0)=12\tau^2
       [\tfrac49(u-v/4)^2+1-v^2/4],
\]

\[
 \begin{split}
 1728P(u,v,k)={}&16(4u-v)^2(u-v)^2\\
 &+27(1-u^2)(4-v^2)Q(u,v),
 \end{split}
\]
where
\[
 Q(u,v)=4u^2-8uv+v^2+8=(2u-v)^2+4(2-uv)\geq0.
\]
The last inequality follows from $|u|\leq1$, $|v|\leq2$.
Both endpoints are nonnegative. For completeness, the following
division-free interpolation identity is a direct polynomial check:
\[
 \begin{split}
 kP(u,v,\sigma)={}&(k-\sigma)P(u,v,0)+\sigma P(u,v,k)\\
 &+(4+12u^2)k\sigma(k-\sigma).
 \end{split}
\]
If $k=0$, necessarily $\sigma=0$. If $k>0$, every term on the right is
nonnegative. Hence $P\geq0$, proving the claimed quartic inequality.
These identities, the nonnegativity implication for **all real** $u,v,\sigma$
in the displayed domain, and the link to the residual expression are
checked in `formal/QuarticCertificate.lean` without unproved placeholders.

### 3.3 All equality cases

Suppose $R_4>0$ and $P=0$. If $k>0$ and $0<\sigma<k$, the last term of
the interpolation identity is positive, which is impossible. Thus an
endpoint must occur.

At $\sigma=0$, either $\tau=0$, yielding an odeco tensor and $R_4=0$, or
\[
 v=\pm2,\qquad u=v/4,\qquad\tau=v/8.
\]
At $\sigma=k>0$, we have $|v|<2$, so $Q>0$. The second endpoint formula
forces $|u|=1$. Its first term then forces $v=u$, since $v=4u$ is outside
the domain. Therefore
\[
 u=\pm1,\qquad\tau=0,\qquad\sigma=3/16.
\]
The latter configuration has $D=t_2=0$ and
\[
 t_0=t_4=\lambda,\qquad
 t_1=t_3=\pm\tfrac{\sqrt3}{4}\lambda,
 \qquad\lambda\ne0.
\]
Reflection of one coordinate changes the sign of $t_1,t_3$, so these are
exactly the scalar multiples of $T_*$ up to orthogonal changes.

In the first nonzero-residual configuration $h=j=0$, and, after an overall
sign and possible interchange of the axes, the coefficients are
\[
 \tfrac{\sqrt N}{4}(1+\sqrt3),\quad0,\quad
 \tfrac{\sqrt N}{4},\quad0,\quad
 \tfrac{\sqrt N}{4}(1-\sqrt3).
\]
Rotating $T_*$ by $\pi/4$ gives
$(2+2\sqrt3,0,2,0,2-2\sqrt3)$; scaling by $\sqrt N/8$ gives precisely
this configuration. Thus it belongs to the same orbit.

Finally, $T_*$ has $\|T_*\|_F^2=56$, $G=\operatorname{diag}(32,24)$,
and projection maximum $32$. The maximizing criterion above certifies
that the standard axes attain this maximum: $a=1,b=c=0,d=2\sqrt3,e=3$
give $\ell_1=0=4b^2$. Hence
\[
 d_4(T_*)^2=24,\qquad R_4(T_*)^2=768,
 \qquad \frac{d_4(T_*)^2}{R_4(T_*)}=\frac{\sqrt3}{2}.
\]
This proves sharpness, as well as sufficiency of every listed equality
case, by homogeneity and orthogonal invariance. The zero-residual equality
cases were already classified by Theorem 1.

## 4. An infinite family forcing order growth

**Proof of Theorem 3.** The norm formula immediately gives
$\|S_p\|_F^2=2+2p/p=4$. Since $p\geq5$, the four specified entries do
not overlap. Direct substitution in Lemma 5 gives
\[
 G(S_p)=\operatorname{diag}\big(4(p-1)/p,\ 8/p\big),
\]
so the claimed residual follows.

It remains to prove the maximum projection energy is exactly 2, rather
than infer this from numerical maximization. Write $x^2+y^2=1$,
$a=x^2$, $b=y^2$, so $a+b=1$, and set
\[
 B=a^p+b^p+p(ab^{p-1}+ba^{p-1}).
\]
For odd $p\geq5$, expanding
$f_{S_p}(x,y)^2+f_{S_p}(-y,x)^2$ gives
\[
 2B+4\sqrt p\,(ab)^{(p-1)/2}.
\]
The binomial expansion of $(a+b)^p=1$ contains the four terms in $B$.
The two central terms, which are not among those four, sum to
\[
 \binom p{(p-1)/2}(ab)^{(p-1)/2}(a+b)
     =\binom p{(p-1)/2}(ab)^{(p-1)/2}.
\]
All remaining terms are nonnegative. Thus
\[
 B\leq1-\binom p{(p-1)/2}(ab)^{(p-1)/2}.
\]
The central coefficient is at least $p$, and $p\geq2\sqrt p$ for
$p\geq5$, proving that the projection energy is at most 2.

For even $p\geq6$, the corresponding exact expansion is
\[
 2B+4(p+1)(ab)^{p/2}.
\]
The omitted central binomial term gives
$B\leq1-\binom p{p/2}(ab)^{p/2}$. Here
\[
 \binom p{p/2}\geq\binom p2=p(p-1)/2\geq2(p+1)
       \qquad(p\geq6),
\]
again proving the required upper bound. The coefficient comparisons used
in both cases follow from the successive ratio
$\binom p{k+1}/\binom pk=(p-k)/(k+1)$ up to the middle. The final
even-case comparison is $(p^2-5p-4)/2\geq0$, true at $p=6$ and increasing
thereafter.

These formulas hold for all signs of $x,y$: the cross powers are
$(xy)^{p-1}$ in the odd case and $(xy)^p$ in the even case, both even
powers. Every orthonormal basis is covered, since changing the sign of
a basis vector does not change its squared evaluation. The standard axes
have projection energy 2. Lemma 4 therefore gives $d_p(S_p)^2=4-2=2$.
Taking its ratio to the residual proves the asserted lower bound for
$C_p$ and its $p^{1/4}$ asymptotic order.

## 5. Matching upper growth by trace contraction

Define the symmetric order-$(p-2)$ tensor
$(\operatorname{Tr}T)_\alpha=T_{\alpha,1,1}+T_{\alpha,2,2}$.
The binomial identity
$\binom pk=\binom{p-2}k+2\binom{p-2}{k-1}+\binom{p-2}{k-2}$,
with out-of-range coefficients zero, gives
\[
 \operatorname{tr}G(T)=2\|T\|_F^2-\|\operatorname{Tr}T\|_F^2.
\]
This can also be read entry by entry from
$(a-c)^2+4b^2=2(a^2+2b^2+c^2)-(a+c)^2$.

For a symmetric binary cubic with coefficients $(a,b,c,d)$,
\[
 \begin{split}
 4(a^2+3b^2+3c^2+d^2)-3[(a+c)^2+(b+d)^2]
       =(a-3c)^2+(d-3b)^2\geq0.
 \end{split}
\]
Fix any ordered $(p-3)$-tuple and apply this bound to the remaining
three indices of $T$. Summing over all such tuples proves, for every
$p\geq3$,
\[
 \|\operatorname{Tr}T\|_F^2\leq\tfrac43\|T\|_F^2,
 \qquad \|T\|_F^2\leq\tfrac32\operatorname{tr}G(T).
\]
The sum on the left is exactly the norm of the trace tensor, because
its remaining one index together with the fixed tuple ranges over all
ordered $(p-2)$-tuples; no multiplicities are discarded.

Let $A=\lambda_{\max}(G)$ and $B=\lambda_{\min}(G)$. In the basis used
in Theorem 1 the squared distance $E=d_p(T)^2$ satisfies both
\[
 E\leq\tfrac p4 B,\qquad E\leq\|T\|_F^2\leq\tfrac32(A+B).
\]
Since $A\geq B\geq0$, multiplying these two nonnegative bounds yields
\[
 E^2\leq\tfrac{3p}{8}B(A+B)\leq\tfrac{3p}{4}AB
       =\tfrac{3p}{4}R_p(T)^2.
\]
This proves the first assertion of Theorem 4. The scalar multiplication
step, cubic trace bound and entrywise trace identity are also Lean-checked.
Together with Theorem 3, this determines the optimal growth order.

### 5.1 A sharper trace norm and explicit constant

We supply a complete derivation of the sharper trace estimate
\[
 \|\operatorname{Tr}T\|_F^2\leq
 \sigma_p\|T\|_F^2,\qquad
 \sigma_p=\frac{4\lfloor p^2/4\rfloor}{p(p-1)}.
\]
Complexify the tensor space with its Hermitian Frobenius inner product.
The vectors $e_+=(e_1+i e_2)/\sqrt2$ and
$e_-=(e_1-i e_2)/\sqrt2$ are Hermitian orthonormal. Their bilinear
Euclidean contractions, which define the complex extension of the real
trace, satisfy
\[
 e_+\cdot e_+=e_-\cdot e_-=0,\qquad e_+\cdot e_-=1.
\]
Let $F_{p,r}$ be the average over all distinct permutations of the tensor
with $r$ copies of $e_+$ and $p-r$ copies of $e_-$.
Its $\binom pr$ summands are Hermitian orthonormal, so
$\|F_{p,r}\|_F^2=1/\binom pr$, and different $r$ give orthogonal tensors.
Tracing the first two slots keeps precisely the permutations where one
slot is $e_+$ and the other $e_-$. Their proportion is
$2r(p-r)/(p(p-1))$. The remaining slots have the uniform symmetrization,
so
\[
 \operatorname{Tr}F_{p,r}=
   \frac{2r(p-r)}{p(p-1)}F_{p-2,r-1}
       \quad(1\leq r\leq p-1),
\]
with zero output for $r=0,p$. On the normalized orthonormal basis
$\sqrt{\binom pr}F_{p,r}$, the squared nonzero singular values are
\[
 \left(\frac{2r(p-r)}{p(p-1)}\right)^2
 \frac{\binom pr}{\binom{p-2}{r-1}}
       =\frac{4r(p-r)}{p(p-1)}.
\]
Distinct input indices map to distinct orthogonal output indices. Thus
the largest squared singular value is $\sigma_p$, proving the estimate
for all complex tensors and hence all real tensors. The norm is attained
over the real space as well: for even $p$, $F_{p,p/2}$ is real; for odd
$p$, take the real sum of the two conjugate middle basis vectors, whose
singular values agree. This attainment is not needed for the upper bound.

It follows that
$\|T\|_F^2\leq c_p(A+B)$ with $c_p=(2-\sigma_p)^{-1}$ as stated.
If $B=0$, the distance is zero by Theorem 1. Otherwise write
$x=\sqrt{A/B}\geq1$. The two distance bounds now give
\[
 \frac{d_p(T)^2}{R_p(T)}\leq
    \min\{p/(4x),\ c_p(x+1/x)\}.
\]
For $p\geq9$, we have $p\geq8c_p$ (check $p=9$ directly and use
$c_p\leq9/8$ for $p\geq10$). The decreasing and increasing functions
cross at $x_*=\sqrt{p/(4c_p)-1}\geq1$. For $x\leq x_*$ use the second
bound, and for $x\geq x_*$ use the first. Their common value at the
crossing is $p/(4x_*)$, proving the sharper assertion of Theorem 4.
Since $c_p\to1$, its asymptotic upper constant is $2^{-1/2}$.

## 6. Verification, dependence and open questions

The proofs above do not depend on finite sampling. The standard-library
exact checker independently expands the polynomial certificate, computes
the sharp quartic tensor in $\mathbb Q(\sqrt3)$ using the complete ordered
contraction convention, checks rational orthogonal transformations, and
replays the order-growth identities and binomial comparisons at specified
finite orders. The finite order replay is a diagnostic for formulas; the
infinite family is proved in Section 4. Optimized Python execution also
passes, since validation does not use removable `assert` statements.

Lean formalizes the nine scalar results listed in the formal directory,
including the domain-wide inequality used in Section 3.2. It does not
formalize the tensor definitions, angular reduction, equality classification
or the infinite binomial argument. Its exported axioms are recorded;
`sorryAx` and new postulated axioms are absent. This is model-conducted
verification, not external human peer review or whole-paper formalization.

The original qualitative odeco characterization is part of the established
tensor literature; we do not claim it as a first discovery. The relevant
comparison includes Boralevi--Draisma--Horobet--Robeva, *Orthogonal and
unitary tensor decomposition from an algebraic perspective*, Israel
Journal of Mathematics 222 (2017), 223--260, DOI
[10.1007/s11856-017-1588-6](https://doi.org/10.1007/s11856-017-1588-6).
Our [preliminary benchmark comparison](../../research/novelty-assessment/2026-10-07-binary-odeco-benchmarks.md)
records exactly which sources were inspected; it does not establish priority.

Two principal quantitative gaps remain. First, what is the sharp
asymptotic leading constant in $C_p=\Theta(p^{1/4})$, and can all-order
extremizers be classified? Second, in higher dimension can
the earlier polynomial-dimensional upper bound be reduced toward the
known $m^{1/4}$ direct-sum obstruction while retaining the complete
commutator residual and arbitrary weights? Both require further theorems.
