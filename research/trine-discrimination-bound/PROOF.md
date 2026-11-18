# A trine bound for three-state discrimination in arbitrary finite dimension

**AI-assisted research draft.** This note gives an exact upper bound for an equal-prior three-state discrimination witness. It determines the optimal value, not the entire set of quantum discrimination profiles or the set of mixed extremizers. The proof includes the 4.4 kB [certificate](certificate.json) and two independently implemented, exact-arithmetic checkers. It has had AI-assisted internal review, not external peer review. No priority claim is made.

## 1. Target

Let $\rho_i$ ($i=0,1,2$, cyclic subscripts) be arbitrary trace-one positive matrices on one complex finite-dimensional Hilbert space. Define the **unnormalized** optimal joint success and the sum of the three pair trace distances by
$$
 S=\max\left\{\sum_i\operatorname{Tr}\rho_i M_i:M_i\succeq0,\ \sum_iM_i=I\right\},
 \qquad T=\frac12\sum_i\|\rho_i-\rho_{i+1}\|_1.
$$
In [Weiner’s Eq. (43)](https://arxiv.org/html/2609.17920v1#S6.E43) and [Conjecture 6.3](https://arxiv.org/html/2609.17920v1#S6.SS5), the witness is $\beta=T-S$, not $T-S/3$. We show
$$
 \beta\le b:=\frac{3\sqrt 3}{2}-2.
$$
The pure qubit trine already attains this value. Weiner had proved the inequality for every qubit triple and for every triple of pure states in any dimension, and exhibited mixed triples attaining the trine value. The new ingredient below is the upper bound covering every mixed triple. No exclusivity of pure maximizers is claimed.

## 2. A signed chained-operator inequality

Let $A_0,A_1,A_2$ be Hermitian involutions on Alice and $B_0,B_1,B_2$ Hermitian involutions on Bob, each with square equal to identity (it is not required that both eigenvalue signs occur). Tensor factors are implicit: every $A_i$ commutes with every $B_j$, but **no relations within either party** other than the individual squares are assumed. Put
$$
 X=\sum_{i=0}^2(A_i-A_{i+1})B_i,qquad C=\sum_{i=0}^2 A_i.
$$
The exact sum-of-squares identity in §4 proves the operator inequality
$$
                   9I-\sqrt3 X+\tfrac34 C\succeq0. \tag{1}
$$
Simultaneously replacing $A_i\mapsto-A_i$ and $B_i\mapsto-B_i$ preserves every term of $X$ and replaces $C$ by $-C$. Thus (1) holds for both signs. Taking an expectation in one normalized vector $\psi$ gives
$$
 \langle X\rangle_\psi\le 3\sqrt3-\tfrac{\sqrt3}{4}|\langle C\rangle_\psi|. \tag{2}
$$
The absolute value here is applied to a scalar expectation, not to an operator; no claim about a bound by the operator $-|C|$ is needed.

For the application $A_i$ may instead be arbitrary **Hermitian contractions**. Embed their common Hilbert space $\mathcal H_A$ into $\mathcal H_A\oplus\mathcal H_A$ by the same map $Vx=(x,0)$ for every $i$. On this same doubled space take the three self-adjoint involutions
$$
 \widehat A_i=\begin{pmatrix}A_i&\sqrt{I-A_i^2}\\ \sqrt{I-A_i^2}&-A_i\end{pmatrix}.
$$
The blocks within each matrix commute by functional calculus, giving $\widehat A_i^2=I$. Every $V^*\widehat A_iV=A_i$. The operators on Bob stay unchanged; in the state $(V\otimes I)\psi$ every term of $X$ and $C$ has its original expectation since it contains just one Alice observable. This transfers (2) without replacing products of two compressed Alice observables by products of their compressions.

## 3. Reduction by a dual optimizer and purification

The success problem above has the standard dual $S=\min\{\operatorname{Tr} Y:Y=Y^*,\ Y\succeq\rho_i\ \forall i\}$. In finite dimensions, the primal is feasible and compact and has the strictly feasible POVM $I/3$; the dual has a strictly feasible scalar multiple of $I$. Thus strong duality and dual attainment apply. Also $1\le S\le3$. Fix a minimizing $Y$. It is positive, and on its kernel every $\rho_i$ vanishes since $0\preceq\rho_i\preceq Y$. Restrict to $\mathcal H_0=\operatorname{supp}Y$, on which $Y$ is invertible; none of the pair distances or success bounds is altered.

Let $\tau=Y/S$ and $P_i=Y^{-1/2}\rho_iY^{-1/2}$ on $\mathcal H_0$; $0\preceq P_i\preceq I$. In an eigenbasis of $\tau$, write $\tau=\sum_j t_j|j\rangle\langle j|$ and take its normalized purification $\psi=\sum_j\sqrt{t_j}|j\rangle_A|j\rangle_B$. With transpose in this fixed basis,
$$
 \langle U\otimes V\rangle_\psi=\operatorname{Tr}(\sqrt\tau\,U^{\mathsf T}\sqrt\tau\,V).
$$
Choose $A_i=(2P_i-I)^{\mathsf T}$ (a Hermitian contraction even for complex entries) and $B_i=\operatorname{sgn}(\rho_i-\rho_{i+1})$, assigning $+1$ on the kernel to make each $B_i$ an involution. These are *auxiliary* bipartite binary observables; they are not required to form the optimal three-outcome POVM. The latter enters only through its dual value $S$. Since $\sqrt\tau P_i\sqrt\tau=\rho_i/S$ and $\operatorname{Tr}\rho_i=1$,
$$
 \langle X\rangle=\tfrac{2}{S}\sum_i\operatorname{Tr}[(\rho_i-\rho_{i+1})B_i]
                 =\frac{4T}{S}, \qquad
 \langle C\rangle=\frac{6}{S}-3.
$$
Substituting these in (2) yields
$$
 T-S\le g(S):=(3\sqrt3/4-1)S-(3\sqrt3/16)|2-S|.
$$
The slope below $2$ is $15\sqrt3/16-1>0$ and above $2$ it is $9\sqrt3/16-1<0$ (their signs follow from $675>256>243$). Hence the right side never exceeds $g(2)=b$. Sharpness is witnessed by three pure qubit states with Bloch vectors at mutual angle $120^\circ$. Each distance is $\sqrt3/2$ and $\sum\rho_i=3I/2$. The POVM $M_i=(2/3)\rho_i$ and dual $Y=I$ both give $S=2$. This proves the desired sharp value provided (1) holds.

## 4. Complete finite certificate for (1)

Work in the real group algebra with coefficients in $\mathbb Q(\sqrt3)$ generated by the three self-adjoint involutions on each side, with every cross pair commuting. Represent a monomial by a pair of lists of indices $(u,v)$, meaning $A_{u_1}\cdots A_{u_k}B_{v_1}\cdots B_{v_l}$. Empty lists mean identities; adjacent repeats on the same side cancel; the involution reverses each list. These are exactly the reduced-word rules of two copies of the free product $\mathbb Z_2*\mathbb Z_2*\mathbb Z_2$ in direct product. Any polynomial identity found by these rules holds under all the operator substitutions in §2.

The certificate file contains 24 forms $f_j$ (67 terms in total) and the upper triangle of a symmetric $24\times24$ matrix $G$. Each record $[u,v,r]$ in a form encodes $r(\sqrt3)^{|v|}$ times its monomial; $r$ is the indicated exact rational number. **The Gram matrix itself is rational; the forms and the operator identity use $\mathbb Q(\sqrt3)$.** Let $\pi$ range over all six permutations of the indices. It acts by $A_i\mapsto A_{\pi(i)}$ and maps each oriented edge from $i$ to $i+1$ to that from $\pi(i)$ to $\pi(i+1)$. If the new edge is oriented cyclically, map $B_i$ to $B_{\pi(i)}$; if it is oriented against the cycle, map it to $-B_{\pi(i+1)}$. This preserves the operator relations and $X,C$. The data encode the equality
$$
 \boxed{\quad
 \frac16\sum_{\pi\in S_3}\sum_{j,k=1}^{24}G_{jk}\,\pi(f_j)^*\pi(f_k)
  =9I-\sqrt3\sum_{i=0}^2(A_i-A_{i+1})B_i+\frac34\sum_{i=0}^2 A_i .
 \quad} \tag{3}
$$

Here is a reproducible, finite arithmetic check so (3) need not be accepted as a numerical SDP bound.

1. Reflect the given upper triangle across the diagonal. Starting with $G-I/10^6$, take its top-left entry $d$, verify $d>0$, and replace the matrix $\left(\begin{smallmatrix}d&w^T\\w&H\end{smallmatrix}\right)$ by $H-ww^T/d$. All 24 exact rational pivots are positive. By Schur complementation, $G\succ I/10^6$, so each quadratic form on the left of (3) is a positive operator.
2. For each $\pi,j,k$, and every pair of monomials from $f_j,f_k$, relabel the symbols with their orientation signs, reverse the first monomial, concatenate the lists party by party, then cancel adjacent equal indices. Add its signed coefficient to the reduced word, divided by six, multiplied by $G_{jk}$. Reduce powers of $\sqrt3$ by $(\sqrt3)^2=3$; equivalently keep a pair of rational coefficients for every word.
3. Among 244 reduced words encountered, exactly ten have nonzero coefficients: $I$ has $9$; $A_i$ has $3/4$; $A_i B_i$ has $-\sqrt3$; and $A_{i+1}B_i$ has $+\sqrt3$. This is exactly (3), hence (1). No equivalence of adjoint words or permutation-orbit terms is assumed by the verifier in this comparison: every individual word is checked.
4. Run `python3 -B -O verify.py` and `python3 -B -O independent.py` with [certificate.json](certificate.json) next to the scripts. The first checker performs the rational expansion and Schur-complement tests just described. The independently written second checker instead clears denominators, tests all leading principal minors by integer Bareiss elimination, and expands the full polynomial **before** averaging the relabeled words. Both compare the resulting coefficients with the stated operator. Only the Python standard library is needed. The finite certificate, not the way its numbers were found, is part of the proof.

**Why strict positivity of $G$ does not preclude equality.** It is a Gram matrix on 24 polynomial combinations chosen to annihilate an ideal trine vector, not on all formal words of length at most two (there are 28). For an explicit model use the three coordinate-transpositions acting as reflections on the real plane $x_0+x_1+x_2=0$. Call those $A_i$, with transposition $i\leftrightarrow i+1$. In an orthonormal plane basis the $A_i$ are symmetric, $\sum A_i=0$, and $(A_i-A_{i+1})^2=3I$. Use $(A_i-A_{i+1})^{\mathsf T}/\sqrt3$ on Bob and the normalized maximally entangled vector. Then $\langle C\rangle=0$ and $\langle X\rangle=3\sqrt3$, so the expectation of (3) vanishes. Directly, the checker also tests each of the 24 forms on this vector using the rational plane basis $(e_0-e_2,e_1-e_2)$ and reversed Bob multiplication on the right of the vectorized identity. Equality pertains to annihilation of those combinations; it does not require a null eigenvalue of the reduced $G$.

The numerical discovery phase used a symmetry-reduced degree-two noncommutative moment SDP and rational reconstruction. Neither the relaxation’s alleged optimum, the observed numerical correlations, nor any convergence theorem is needed to verify the coefficient identity or the bound. See [SOURCES.md](SOURCES.md) for prior results and search limitations.
