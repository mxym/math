# When a canonical discrete Gaussian survives a normalized field trace

Field trace is an orthogonal projection after scaling, so it preserves the Gaussian form for a continuous spherical law. It need not do so for a discrete one, even if the target law is allowed any mean and positive-definite covariance. This note gives the exact splitting criterion, an ideal-valuation test, a full classification along nested cyclotomic conductors, and one explicit first-order total-variation discrepancy.

These are standalone distributions on unwrapped lattices. No public samples, secret, modulus, ring-switching algorithm, or hardness claim is involved.

## Exact criterion for orthogonal projection

Let $E=U\perp W$ be a Euclidean space, let $\Lambda\subset E$ be a full lattice, and suppose that orthogonal projection $\pi$ onto $W$ has discrete image $\Gamma=\pi\Lambda$. Set $D=\Lambda\cap U$, a full lattice of $U$ by the rank of the projection exact sequence. Let $G_s$ be the spherical discrete Gaussian of mass proportional to $\exp(-\pi\|x\|^2/s^2)$ on $\Lambda$, for any $s>0$. For $y\in\Gamma$, write $c_y\in U/D$ for the other component of any lift of $y$ to $\Lambda$. Then

$$
\Pr[\pi G_s=y]\ \propto\ \exp(-\pi\|y\|^2/s^2)\,\rho_s(D+c_y),
\quad
\rho_s(D+c)=\sum_{x\in D+c}e^{-\pi\|x\|^2/s^2}.
\tag{1}
$$

This follows by summing the spherical density over the fiber and using orthogonality. The law in (1) is any single positive-definite discrete Gaussian on $\Gamma$ if and only if

$$
\Lambda=D\perp(\Lambda\cap W),\quad\text{equivalently }\pi\Lambda=\Lambda\cap W .
\tag{2}
$$

Indeed, the factor $\rho_s(D+c)$ is positive, continuous and bounded above and away from zero on the compact torus $U/D$. Thus its logarithm is bounded on $\Gamma$. In comparing (1) to another Gaussian, that logarithm would equal a quadratic polynomial on $\Gamma$. Evaluating the polynomial along all integral multiples of each lattice vector (and using polarization) forces its quadratic and linear parts to vanish. So the candidate has the original width and center zero, and the fiber factor would be constant. Poisson summation gives

$$
\frac{\det D}{s^{\dim U}}\rho_s(D+c)
  =\sum_{\xi\in D^*}e^{-\pi s^2\|\xi\|^2}\cos(2\pi\langle\xi,c\rangle).
\tag{3}
$$

All Fourier weights are positive; the factor is maximized at $c=0$ and equality requires $\langle\xi,c\rangle\in\mathbb Z$ for every $\xi\in D^*$, equivalently $c=0\bmod D$. Since the $y=0$ fiber has this maximal value, constancy is equivalent to every fiber having $c_y=0$. This is exactly (2), which also suffices by (1). The zero-dimensional kernel has the trivial fiber and the same conclusion.

## Field trace on fractional ideals

Let $L/K$ be any finite extension of number fields of degree $d$, with canonical inner products counting all complex embeddings. The projection onto the embedded $K_\mathbb R$ is $\pi=\operatorname{Tr}_{L/K}/d$: testing the inner product against any vector from $K_\mathbb R$ groups the embeddings of $L$ by their restriction. The inherited inner product on $K_\mathbb R$ is $d$ times its own canonical form. For a fractional ideal $I$ of $L$, both the image and intersection lattices are full in this subspace, so (2) reads

$$
\frac{1}{d}\operatorname{Tr}_{L/K}(I)=I\cap K.
\tag{4}
$$

If (4) holds, the projected Gaussian in the canonical metric of $K$ has width $s/\sqrt d$. If it fails, no mean or covariance retuning yields exact equality on the image lattice.

Here is a local test valid for any $I$. Fix a prime $\mathfrak p$ of $K$; at each $\mathfrak P\mid\mathfrak p$ write $a_{\mathfrak P}=v_{\mathfrak P}(I)$, $e_{\mathfrak P}=e(\mathfrak P/\mathfrak p)$, and $\delta_{\mathfrak P}=v_{\mathfrak P}(\mathfrak D_{L/K})$, the relative different exponent. Condition (4) holds precisely if for every $\mathfrak p$,

$$
\min_{\mathfrak P\mid\mathfrak p}
 \left\lfloor (a_{\mathfrak P}+\delta_{\mathfrak P})/e_{\mathfrak P}\right\rfloor
 -v_{\mathfrak p}(d)
 =
\max_{\mathfrak P\mid\mathfrak p}
 \left\lceil a_{\mathfrak P}/e_{\mathfrak P}\right\rceil .
\tag{5}
$$

For the trace exponent at a completion, $\operatorname{Tr}(\mathfrak P^a)\subseteq\mathfrak p^b$ holds if and only if the trace is integral on $\mathfrak P^{a-eb}$. This fractional ideal is closed under multiplication by local integers, so integrality of all its traces is equivalent to its containment in $\mathfrak D^{-1}=\mathfrak P^{-\delta}$. Therefore the image exponent is the floor in (5). The global local trace adds the completions' images, so their minimum exponent applies. The intersection consists of elements whose valuations meet every $\mathfrak P$ constraint, giving the largest ceiling.

For $I=\mathcal O_L$, the right side is zero. For $I=\mathfrak D_{L/\mathbb Q}^{-1}$, the tower law for the different gives $a_{\mathfrak P}=-\delta_{\mathfrak P}-e_{\mathfrak P}v_{\mathfrak p}(\mathfrak D_{K/\mathbb Q})$. Substitution yields exactly the same yes/no criterion as for $\mathcal O_L$:

$$
\min_{\mathfrak P\mid\mathfrak p}\lfloor\delta_{\mathfrak P}/e_{\mathfrak P}\rfloor=v_{\mathfrak p}(d)
\quad\text{for all }\mathfrak p.
\tag{6}
$$

## Nested cyclotomic conductors

Let $u\mid v$, $K=\mathbb Q(\zeta_u)$, and $L=\mathbb Q(\zeta_v)$. For integers,

$$
\frac{1}{d}\operatorname{Tr}_{L/K}(\mathcal O_L)
   =\frac1{C}\mathcal O_K,\qquad
 C=\prod_{\substack{p\mid v\\p\nmid u}}(p-1).
\tag{7}
$$

To verify this, use the integral tensor product decomposition over the distinct prime-power conductors. When an existing prime-power conductor $p^a$ is raised to $p^b$, the relative integral basis is $1,\zeta_{p^b},\ldots,\zeta_{p^b}^{p^{b-a}-1}$. It spans integrally by division of each power's exponent by $p^{b-a}$ and is independent by the extension degree. Its normalized trace sends the first basis vector to 1 and all others to 0, by summing the equally spaced roots over the relative embeddings. When a prime is newly introduced, the traces of the absolute power basis in conductor $p^b$ generate $p^{b-1}\mathbb Z$: the trace of a power is $p^b{\bf1}_{p^b\mid j}-p^{b-1}{\bf1}_{p^{b-1}\mid j}$, and the basis contains a power yielding $-p^{b-1}$ if $p>2$. For $p=2$ the trace of 1 already gives $p^{b-1}$. Dividing by the degree $(p-1)p^{b-1}$ gives exactly $(p-1)^{-1}\mathbb Z$. Relative normalized traces multiply on simple tensors, proving (7).

Consequently the canonical spherical discrete Gaussian on either the integers or the absolute codifferent survives the normalized trace **exactly when no new odd conductor prime is added**. In particular raising an existing conductor exponent is different from adding a new odd prime, even if both operations produce the same relative degree.

## First discrepancy from a nontrivial projection twist

In the geometric setting, also suppose $\Lambda\cap W$ is full in $W$. Then the set of twists $c_y$ is a finite group $T\cong\Gamma/(\Lambda\cap W)$: the twist map is a homomorphism, and its kernel consists exactly of projected vectors that themselves lie in $\Lambda$. If $T\ne0$, let

$$
a^2=\min_{\substack{\xi\in D^*\\
           \chi_\xi|_T\ne1}}\|\xi\|^2,\qquad
F(t)=\sum_{\substack{\xi\in D^*,\ \|\xi\|^2=a^2\\
                    \chi_\xi|_T\ne1}}\chi_\xi(t),\qquad
\chi_\xi(t)=e^{2\pi i\langle\xi,t\rangle}.
$$

Characters of the full torus separate points, so the minimum exists. The function $F$ is real by symmetry and nonzero, since its character coefficients are positive multiplicities on at least one nontrivial character. Let $Q_s$ be the matching centered Gaussian of width $s$ on $\Gamma$. Then

$$
d_{\rm TV}(\mathcal L(\pi G_s),Q_s)
 = e^{-\pi s^2a^2}\left(\tfrac12\mathbb E_{t\sim U(T)}|F(t)|+o(1)\right)
\quad(s\longrightarrow\infty).
\tag{8}
$$

In (3), the terms trivial on $T$ yield a constant $C_s\to1$, and the remaining first shell contributes $e^{-\pi s^2a^2}F$ with uniform error $o(e^{-\pi s^2a^2})$. The error bound follows by discreteness of the dual spectrum and absolute summability of its theta series at any fixed positive width. The law of $c_y$ under $Q_s$ tends to uniform on the finite quotient, by Poisson summation for each coset of the full-rank sublattice $\Lambda\cap W$ in $\Gamma$. Hence the weighted average of $F$ tends to 0. The ratio of the factor in (3) to its $Q_s$ average is the likelihood ratio in (1); substituting the expansion and averaging its absolute deviation gives (8). This is an expansion against the matching Gaussian, not an optimization over approximate retunings.

For an explicit case let $p$ be odd, $L=\mathbb Q(\zeta_{p^b})$, $K=\mathbb Q$, $m=p^{b-1}$, and $I=\mathcal O_L$. Write $J=\operatorname{Tr}_{L/\mathbb Q}(G_s)/m\in\mathbb Z$. The matching scalar Gaussian on $\mathbb Z$ has width $s\sqrt{(p-1)/m}$. In (8) one has

$$
a^2=\frac{p-2}{(p-1)pm},\qquad
\tfrac12\mathbb E|F|=
  \frac{N_p}{2(p-1)}\sum_{j=0}^{p-2}|\cos(2\pi j/(p-1))|,
\quad
N_p=\begin{cases}2,&p=3,\\2(p-1),&p\ge5.\end{cases}
\tag{9}
$$

Indeed, the canonical trace Gram separates the basis into $m$ blocks by exponents modulo $m$, each a scaled copy $\sqrt{pm}\,P_p\mathbb Z^p$ with $P_p$ the projection off the constant line. All blocks other than index 0 are trace-zero and contribute no twist. In block 0, the rational subspace corresponds to the line through $P_p e_0$. Its orthogonal kernel lattice consists of classes $P_p z$ with $z_0-\bar z=0$; a common integer shift then gives $z_0=0$ and $\sum_{j\ne0}z_j=0$. Thus this kernel is $\sqrt{pm}\,A_{p-2}$. Quotient trace index $J=1$ is represented by $-P_p e_1$, whose remaining-component twist is $-P_{p-1}e_1$ under the same scaling. The dual is $(pm)^{-1/2}P_{p-1}\mathbb Z^{p-1}$, with shortest vectors the two signs of $P_{p-1}e_j$: decompose integer vectors into nested indicator sets whose projected dot products are nonnegative, and minimize $|S|(1-|S|/(p-1))$. For $p=3$ the two unsigned index choices are negatives, so there are just two distinct shortest vectors. They all yield the character $\exp(\pm2\pi iJ/(p-1))$, since the pairing with $-P_{p-1}e_1$ is $1/(p-1)\bmod1$ or its negative. Adding a nonzero component in another orthogonal block can only increase the squared length and cannot affect the phase. Thus the first nontrivial shell has sum $N_p\cos(2\pi J/(p-1))$. Orthogonal projection of $J$ corresponds to the rational number $J/(p-1)$ with squared norm $mJ^2/(p-1)$, giving the stated matching width.

## Comparison with primary sources

[Espitau–Wallet–Yu, §§2.2 and 3](https://pqshield.com/wp-content/uploads/2023/10/2023-1654.pdf) give the projection mass factor, Gaussian mass inequalities and orthogonal equality precedent for a general lattice quotient. [Lyubashevsky–Peikert–Regev, A Toolkit for Ring-LWE Cryptography](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) use the canonical prime-power tensor integral bases. Here the focus is the arithmetic application (5)–(7) to the field trace and its exact associated discrete law, and the first nonconstant-shell calculation (8)–(9). The classical splitting and trace ingredients are included to make the comparison self-contained. There is no change to their published hypotheses or result.

The verifier checks trace formulas, block geometry and the first-shell phases in exact small instances. The asymptotic statements are justified by the proof, not by the finite checks.
