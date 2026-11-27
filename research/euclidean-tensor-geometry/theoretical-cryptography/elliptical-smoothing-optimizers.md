# Extremal elliptical smoothing at a fixed geometric mean

The product-of-widths smoothing bound in Peikert–Regev–Stephens-Davidowitz holds uniformly over anisotropic widths. But which width vector is worst at a fixed geometric mean? For a fixed ideal, the answer in the wide limit is determined first by its minimum *algebraic* norm, then by successive embedding-energy shells. In particular a spherical width is eventually extremal for a Galois integer ring, but need not be extremal for a non-Galois ring. The example below gives the sign, rate and coefficient of the displacement.

This is a theorem about a fixed number field and a scalar tending to infinity. It is not a cryptographic algorithm, a new hardness claim, or a uniform estimate as the field degree grows.

## Model and results

Let $K$ be a number field of degree $n$, with archimedean places $v$, weights $m_v=1$ for real places and $m_v=2$ for complex places, and maximal order $R$. Let $J$ be a nonzero fractional ideal. Write

$$
H=\{s\in\mathbb R^{r_1+r_2}:\sum_v m_v s_v=0\},
\qquad
\langle u,v\rangle_H=\sum_j m_j u_jv_j .
$$

Use this weighted metric and let $P_H$ denote projection onto $H$. Logarithms of absolute embeddings of units form a lattice $\mathcal U\subset H$. For $c>0$ put $A=\pi c^2$ and define the nonzero dual theta mass

$$
F_c(s)=\sum_{0\ne x\in J}e^{-A E_x(s)},\qquad
E_x(s)=\sum_v m_v e^{2s_v}|\sigma_v(x)|^2,\qquad s\in H/\mathcal U .
\tag{1}
$$

Periodicity follows by multiplying $J$ by a unit. In the smoothing interpretation $J=I^\vee$, the trace-dual fractional ideal of the primal ideal $I$, and the Gaussian widths are $c e^{s_v}$ with complex places counted twice. Trace dual and Euclidean dual differ by coordinatewise conjugation in the canonical real space; this does not change (1).

Let $M=\min_{0\ne x\in J}|N_{K/\mathbb Q}(x)|$, $\rho=M^{2/n}$, and $L=n\rho$. For each norm-minimizing $x$ put $s_x=(n^{-1}\log M-\log|\sigma_v(x)|)_v\in H$, called its balancing point. There are finitely many such points modulo $\mathcal U$. At a point $s_0$ let $w(s_0)$ be the number of $x\in J$ with $E_x(s_0)=L$, counted in any fixed representative of $s_0$. Then, as $c\to\infty$,

$$
\max_s F_c(s)=e^{-A L}\left(\max_{s_0}w(s_0)+O(e^{-A\eta})\right)
\tag{2}
$$

for some $\eta>0$ depending on the field and ideal. All maximizing shapes lie exponentially close to these balancing points. Thus if $c_\varepsilon$ is the least geometric mean giving $F_c(s)\le\varepsilon$ for *every* choice of widths of that mean, then

$$
c_\varepsilon^2=\frac{\log(\max_{s_0}w(s_0)/\varepsilon)+o(1)}{\pi n M^{2/n}}
\qquad(\varepsilon\downarrow0).
\tag{3}
$$

The algebraic improvement over the standard floor $N(J)$ is exact:

$$
\frac{M}{N(J)}
 =\min\{N(\mathfrak a):\ \mathfrak a\subset R\text{ an integral ideal},\
                               [\mathfrak a]=[J]^{-1}\}.
\tag{4}
$$

Indeed, $x\in J$ gives the integral ideal $(x)J^{-1}$ of the indicated class, and every such ideal arises by writing $\mathfrak a J=(x)$. In particular the ratio is strictly above 1 in a nonprincipal class. This is only a fixed-ideal asymptotic strengthening of the product floor.

## The shape correction at a balancing point

Fix a balancing point $s_0$ and a sufficiently small closed neighborhood of it in $H/\mathcal U$. For all large $c$, there is a unique maximizer $s_c$ of (1) within that neighborhood. For each energy $B>L$ attained at $s_0$ define

$$
S_B=\sum_{x:E_x(s_0)=B}P_H\bigl((e^{2s_{0,v}}|\sigma_v(x)|^2)_v\bigr).
$$

If all $S_B$ vanish, the nearby maximizing shape is exactly $s_0$ for all large $c$. Otherwise let $B_*$ be the first energy with $S_{B_*}\ne0$, and put $w=w(s_0)$. For lifts chosen close to the same representative,

$$
\begin{aligned}
s_c-s_0
 &= -\frac{S_{B_*}}{2w\rho}\,e^{-A(B_*-L)}
       +o(e^{-A(B_*-L)}),\\
F_c(s_c)-F_c(s_0)
 &\sim \frac{A\|S_{B_*}\|_H^2}{2w\rho}\,e^{-A(2B_*-L)} .
\end{aligned}
\tag{5}
$$

In a principal ideal, the balancing point is unique modulo units because all elements of minimum algebraic norm are generators, differing by units. Thus this local maximizing shape is the unique global one for large $c$. For $J=R$, the balancing point is zero and $w$ is the number of roots of unity (kernel of the logarithmic unit map). If the field's automorphisms are transitive on archimedean places, every shell sum is constant on those places before projection, so (5) gives exact spherical maximality for large $c$. This includes Galois fields over $\mathbb Q$.

## Proof of the extremum and expansion

Weighted arithmetic–geometric mean gives

$$
E_x(s)\ge n|N(x)|^{2/n}\ge L,
$$

with equality exactly when the norm of $x$ is $M$ and $s=s_x$ before taking the unit quotient. The ideals $(x)J^{-1}$ below any fixed norm bound form a finite set, and all generators of each one after multiplication by $J$ differ by units. In particular the balancing points are finite. Existence of the minimal norm follows as well by clearing denominators so the nonzero absolute norms are positive integers up to a common factor.

Use a compact fundamental region of the unit lattice, or a finite union of compact lifts of local charts. There $E_x(s)$ is uniformly comparable to the spherical squared length of $x$. Only finitely many $x$ can get within any fixed bounded energy. Therefore off fixed small neighborhoods of the balancing points there is a uniform gap $E_x(s)\ge L+\eta_0> L$. Inside each such neighborhood, every term other than the $w$ terms balancing at its center also has a uniform positive gap above $L$, after shrinking the neighborhood if needed. For instance, first restrict to the finitely many terms of energy at most $L+1$ anywhere on the compact region, then shrink to obtain a strict gap for that finite list. Whenever the terms in a sum have an energy floor $B$ on such a compact set, the sum is $O(e^{-A B})$ for $A\ge1$: bound each summand by $e^{-(A-1)B}e^{-E_x(s)}$ and sum the fixed-width Gaussian. Derivatives of order one and two obey the same exponential bound times $O(A)$ and $O(A^2)$, respectively, because the derivatives add only polynomial factors in the embedding coordinates.

At $s=s_0+t$ near a balancing point the $w$ leading terms are exactly $w\exp(-A\rho\sum_v m_v e^{2t_v})$. The rest have the uniform gap. The leading term attains its maximum at $t=0$. Comparing the maxima over all neighborhoods and their complements proves (2). It also gives (3) by inversion, since the maximum is continuous, strictly decreasing to zero and positive at every finite $c$. More explicitly, if the supremum at two widths were equal, a maximizer at the larger width would give a strictly larger value at the smaller width.

For (5), a maximizing point over the chosen neighborhood already has value at least $F_c(s_0)\ge w e^{-AL}$. As the remainder is $O(e^{-A(L+\eta_0)})$, the leading term must be within relative $O(e^{-A\eta_0})$ of its value at the center. On $H$, $\rho\sum m_v e^{2t_v}-L$ has zero gradient at zero and quadratic growth there. Taking the logarithm gives $\|t\|_H=O(A^{-1/2}e^{-A\eta_0/2})$. All maximizers are therefore interior in a shrinking ball of that radius. On that entire ball the Hessian of the leading term is $-4Aw\rho e^{-AL}(I_H+o(1))$, since $A\|t\|_H^2\to0$, and the derivative estimate above makes the remainder negligible relative to this Hessian. The full Hessian is strictly negative there, proving uniqueness and the Hessian asymptotic along any segment from zero to the maximizer.

At $s_0$ the gradient of the remainder is $-2A\sum_{B>L}e^{-AB}S_B$. Discreteness of the energies and the same sum bound show this is $-2A e^{-AB_*}(S_{B_*}+o(1))$ when the first nonzero shell exists. Otherwise the gradient is exactly zero. The critical-point equation with the just-computed Hessian yields the first line of (5). Evaluating the quadratic Taylor expansion along the segment yields the second line, with the stated factor. No uniformity in varying $K$ or $J$ is used in the gaps or error terms.

## A nonspherical cubic counterexample

Take $K=\mathbb Q(\theta)$ with $\theta$ the real root of $x^3-x-1$, and $J=R$. This polynomial is irreducible by the rational-root test and has discriminant $-23$, so the signature is $(1,1)$; $1<\theta<4/3$. The unit $\theta$ generates the absolute-value unit lattice at the real place, as follows. If a smaller positive generator existed, after multiplying by $-1$ if necessary there would be a unit with real embedding $u\in(1,\theta)$. It must generate the cubic field, and its norm is 1 since the other two embeddings are conjugates. Its trace $T$ is an integer in $(-1,4)$ because the two other embeddings have magnitude $1/\sqrt u$. The second coefficient of its minimal polynomial is then the integer

$$
S=Tu-u^2+1/u.
$$

For $T=0,1,2,3$ the right-hand side is strictly decreasing on $(1,\theta)$ (even at $T=3$ its derivative is negative for $u>1$). Its endpoint values are $T$ and $T\theta-1$, the latter using $\theta^2=1+1/\theta$. For $T=0$ this is the open interval $(-1,0)$; for $T>0$ it is contained strictly between $T-1$ and $T$. This contradiction proves the generator assertion.

Every nonunit has spherical energy at least $3\cdot2^{2/3}$. The nontrivial unit powers with real log-absolute value $t$ have energy $f(t)=e^{2t}+2e^{-t}$, with $t\in(\log\theta)\mathbb Z$. The function decreases on $t<0$ and increases on $t>0$, and $f(t)>f(-t)$ for $t>0$. Since $f(-\log\theta)=\theta^{-2}+2\theta<11/3<3\cdot2^{2/3}$, the first non-root-of-unity shell is exactly $\{\pm\theta^{-1}\}$. Its squared embedding magnitudes are $(a,b)=(\theta^{-2},\theta)$, and therefore $S_{B_*}=2P_H(a,b)\ne0$, with $B_*=a+2b$. As $w=2$, $\rho=1$, and $H=\{s_{\rm r}+2s_{\rm c}=0\}$, (5) gives the explicit shift in the real log width:

$$
(s_c)_{\rm r}\ \sim\ \frac{b-a}{3}\,
    e^{-\pi c^2(a+2b-3)}\ >0 .
$$

Thus the spherical ellipse at this fixed product does not maximize the smoothing theta mass for any sufficiently large $c$. This is a counterexample to unconditional spherical extremality, not to the product-of-widths guarantee.

## Scope and primary precedents

[Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) use geometric mean and the ideal norm floor to obtain uniform elliptical smoothing. Equations (2)–(5) give a fixed-field extrema calculation for that theta mass; the cubic counterexample does not affect their bound or their reduction.

[Van der Geer–Schoof, §§4–5](https://reneschoof.github.io/arakelov.pdf) study the same theta object through the Arakelov size function, including decay at negative degree and the trivial-class maximum conjecture at degree zero for fields with the stated Galois hypotheses. [Tran–Tian](https://arxiv.org/abs/1609.02858) study degree-zero maxima in cyclic cubic fields and note that nonsymmetry is possible without Galois assumptions. The claims here concern the wide limit with a fixed ideal class, the exact algebraic-norm exponent and leading multiplicity, and the first nonzero shell determining the location and value correction. The cubic example and the eventual Galois statement do not resolve any degree-zero conjecture. This comparison is not an exhaustive priority claim.

The verifier checks the cubic field identities and the first-order perturbation coefficients. The asymptotic estimates are proved above.
