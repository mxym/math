# One-sided classicality rules out a qubit–qutrit CQC violation

**Theorem.** Let $A$ have dimension two and $B$ dimension three. Choose any ordered mutually unbiased pair $X_A,Z_A$ and any ordered mutually unbiased pair $X_B,Z_B$. If $\rho_{AB}$ is classical on at least one subsystem, then
$$
I(X_A:X_B)+I(Z_A:Z_B)\le I(A:B)_\rho.
$$
Classical on $B$ means $\rho_{AB}=\sum_i p_i\rho_i^A\otimes|i\rangle\langle i|_B$ for **some** orthonormal basis, not necessarily one of the measured bases; classical on $A$ is defined by reversing the roles. This is the usual zero one-sided discord criterion. Conditionals may be mixed and probabilities arbitrary. If the qubit is classical, Bob may in fact have any finite dimension and make arbitrary measurements in the two settings.

### 1. The classical qubit

Let $K$ be its binary classical label. For setting $M$, the channel $K\to A_M$ is binary symmetric with signed slope $m_M$, the dot product of the Bloch axes of the record and measurement. If $Y-K-A_M$ is a Markov chain, then
$$
I(Y:A_M)\le m_M^2 I(Y:K).
$$
Indeed, both sides involve Jensen gaps for entropy as a function of the probability $u$ of the first input. The output probability is $u'=(1-m_M)/2+m_Mu$. The ratio of the negative second derivative of $h_2(u')$ to that of $h_2(u)$ is $m_M^2u(1-u)/[u'(1-u')]\le m_M^2$, since $u'(1-u')\ge u(1-u)$. Hence $m_M^2h_2(u)-h_2(u')$ is concave; use continuity at endpoints. Apply this with $Y=B_M$. By the Holevo bound $I(B_M:K)\le\chi(K:B)=I(A:B)_\rho$. The two qubit measurement axes are orthogonal, so $m_Z^2+m_X^2\le1$ and summing suffices.

### 2. A qubit information-exclusion polygon

For any finite qubit ensemble with label $K$ write $J_X=I(K:A_X)$, $J_Z=I(K:A_Z)$ and $\chi=I(K:A)$. The following polygon strengthens the weight $(1,1/2)$ and its swap from [Wang–Wang–Chen, Eq. (2)](https://arxiv.org/html/2608.04916v1):
$$
sJ_X+tJ_Z\le\chi
\quad\text{for }(s,t)\text{ in the downward convex hull of }
(1,3/4),\ (13/14,13/14),\ (3/4,1).
$$
Here the downward hull means the convex hull together with all coordinatewise smaller **nonnegative** weight pairs. The weights are sufficient; no optimality is asserted.

Use mutually orthogonal qubit axes $x,z$. Write $v=(x,y,z)$ for the Bloch vector, $r=|v|$, $T=r^2$, $X=x^2$, $Y=y^2$, $Z=z^2$, and $h(u)=h_2((1+u)/2)$ with natural logarithms. The Holevo information is the Jensen gap of $h(r)$ and the measured informations are the Jensen gaps of $h(x), h(z)$. Thus it suffices to prove concavity of $h(r)-s h(x)-t h(z)$ on the ball.

At $0<r<1$ put $H=\operatorname{atanh}(r)/r$, $K_0=1/H$ and $\delta=(1-K_0)/T$. Since $1<H<1/(1-T)$ we have $0<\delta<1$. The **negative Hessian** $D=-\nabla^2_v h(|v|)$ has eigenvalue $1/(1-T)$ along $v$ and $H$ on its orthogonal complement, so
$$
D^{-1}=K_0 I-(1-\delta)vv^{\mathsf T}.
$$
For $s,t>0$, put $E=[e_x\ e_z]$, $L=\operatorname{diag}(s/(1-X),t/(1-Z))$. The desired negative Hessian is $D-ELE^{\mathsf T}$. By the Schur complement this is positive semidefinite iff $L^{-1}-E^{\mathsf T}D^{-1}E$ is. With $a=1/s-1$, $b=1/t-1$ the latter matrix is
$$
\begin{pmatrix}
a(1-X)+\delta(T-X)&(1-\delta)xz\\
(1-\delta)xz& b(1-Z)+\delta(T-Z)
\end{pmatrix}.
$$
Both diagonal entries are nonnegative at each of the three candidate vertices. At fixed $T,Z$, increasing $X$ to $T-Z$ lowers the first diagonal, does not change the second, and increases the absolute value of the off-diagonal. Thus it suffices to check the determinant when $Y=0$.

**Vertex $(1,3/4)$.** Now $a=0,b=1/3$ and the determinant is
$$
Z\{\delta b(1-Z)+(2\delta-1)X\}.
$$
If $2\delta\ge1$, this is nonnegative. Otherwise $X=T-Z\le T(1-Z)$, so it suffices that $\delta(1+6T)\ge3T$, or equivalently
$$
H(T)(1+6T-3T^2)\ge1+6T,\qquad
H(T)=\frac{\operatorname{atanh}\sqrt T}{\sqrt T}=\sum_{j\ge0}\frac{T^j}{2j+1}.
$$
The swapped vertex follows by symmetry.

**Vertex $(13/14,13/14)$.** Here $a=b=1/13$ and the determinant becomes
$$
a^2(1-T)+a\delta T(1-T)+(a^2+2a\delta+2\delta-1)XZ.
$$
At fixed $T$ it is affine in $XZ\in[0,T^2/4]$. Its value at zero is nonnegative. At $X=Z=T/2$ the subtraction in the $x,z$ plane is scalar $s/(1-T/2)$; the eigenvalues of $D$ there are $H(T)$ and $1/(1-T)\ge H(T)$. The unmeasured $y$ direction retains eigenvalue $H(T)$. It suffices therefore that
$$
(1-T/2)H(T)\ge13/14.
$$

**Exact scalar checks.** Put $H_n(T)=\sum_{j=0}^nT^j/(2j+1)$. The multipliers of $H$ in both tests are positive on $[0,1]$, so the partial sums are lower bounds for $T<1$. Define the polynomials
$$
P(T)=\big[H_4(T)(1+6T-3T^2)-1-6T\big]/T,\quad
Q(T)=H_7(T)(1-T/2)-13/14 .
$$
The numerator in $P$ has zero constant term. On each interval $[i/4,(i+1)/4]$, for $i=0,1,2,3$, express the polynomial in the Bernstein basis of that interval. The least coefficients are, in that order:
* $P$: $51971/322560,\ 701/10080,\ 67/1152,\ 8363/107520$;
* $Q$: $193143913/5904138240,\ 45761/7687680,\ 1951291/1291530240,\ 1342581/131203072$.

Every basis polynomial is nonnegative and the basis sums to one; hence $P,Q>0$ throughout. The [primary check](verify.py) computes these rational numbers. An [independent Sturm computation](check_independent.py) counts zero roots of either polynomial on the same interval. The Hessian extends at $r=0$ by continuity; continuity of the entropy extends concavity to the closed ball. Linearity in $(s,t)$ and nonnegativity of mutual information finish the polygon result.

### 3. The classical qutrit

Let $K=i$ be Bob’s classical label and $T_M(i,j)=|\langle i|m_j\rangle|^2$ the stochastic readout matrix for setting $M$. Let $d_M$ be the maximal total variation distance between two rows of $T_M$. Then
$$
I(A_M:B_M)\le d_M I(A_M:K).
$$
For completeness, for any classical channel $T$ with row diameter $d$ and $\gamma\ge1$ set $E_\gamma(P,Q)=\sum_j[P_j-\gamma Q_j]_+$. The positive and negative parts of $P-\gamma Q$ have masses $w$ and $w+\gamma-1$. If $w=0$ contraction is immediate. Otherwise after applying $T$ the signed vector is $wU-(w+\gamma-1)V$ for convex mixtures of channel rows $U,V$, with total variation at most $d$. Its positive mass is at most $w\operatorname{TV}(U,V)\le wd$. Integrating both directions gives the same contraction for KL divergence since
$$
D(P\|Q)=\int_1^\infty\left[\frac{E_\gamma(P,Q)}{\gamma}+\frac{E_\gamma(Q,P)}{\gamma^2}\right]d\gamma.
$$
Scalar integration yields $p\log(p/q)-p+q$, with zeros by limits. Averaging the conditional KL inequalities for the channel $K\to B_M$ given each outcome of $A_M$ proves the claim.

On **three** outcomes, TV of two probability vectors is the largest absolute coordinate difference: every nonempty proper subset is either a singleton or its complement. Thus choose a maximizing column in each setting, with rays $x,z$, and respective row indices $i,j$ for the largest probability in each column. Then $d_X\le|\langle i|x\rangle|^2$, $d_Z\le|\langle j|z\rangle|^2$, and $|\langle x|z\rangle|^2=1/3$. Use $P_v=|v\rangle\langle v|$, $\alpha=5/2,\beta=1$.

* If $i=j$, then $\alpha d_X+\beta d_Z\le\lambda_{\max}(\alpha P_x+\beta P_z)=(\alpha+\beta+\sqrt{(\alpha-\beta)^2+4\alpha\beta/3})/2$.
* Otherwise $P_j\le I-P_i$ gives $\alpha d_X+\beta d_Z\le\beta+\lambda_{\max}(\alpha P_x-\beta P_z)=(\alpha+\beta+\sqrt{(\alpha+\beta)^2-4\alpha\beta/3})/2$.

These formulas follow by taking trace and determinant on the span of the two rays. The second bound is larger, since $1/3<1/2$; its radicand is $107/12<9$. Hence $(5/2)d_X+d_Z\le13/4$; likewise $d_X+(5/2)d_Z\le13/4$. Together with $0\le d_X,d_Z\le1$, these inequalities give exactly the polygon of §2: the intersection of the sloped faces is $(13/14,13/14)$ and their side endpoints are $(1,3/4)$ and $(3/4,1)$. Consequently
$$
I(X_A:X_B)+I(Z_A:Z_B)\le d_XJ_X+d_ZJ_Z\le\chi(K:A)=I(A:B)_\rho,
$$
as required. This does not address states with discord on both sides. See the [scope, prior work and verification notes](README.md).
