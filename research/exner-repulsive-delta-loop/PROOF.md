# Equal spacing strictly maximizes the lowest energy of equally repulsive point interactions on a loop

Let \(N\ge2\), \(L>0\), and \(Y\) be an unordered set of \(N\) distinct points of \(\mathbb R/L\mathbb Z\). Write \(l_j>0\) for the cyclic gaps and \(g=L/N\). For \(\alpha>0\), define the repulsive point-interaction Hamiltonian by the closed quadratic form
\[
 q_Y[f]=\int_0^L |f'(x)|^2 dx+\alpha\sum_{y\in Y}|f(y)|^2,
 \qquad f\in H^1_{\rm per}(0,L).
\]
The associated operator acts as \(-f''\) off the sites. Its eigenfunctions are continuous and satisfy \(f'(y+)-f'(y-)=\alpha f(y)\), as follows by interval-wise integration by parts. Write \(\lambda_1(Y)\) for the minimum of the Rayleigh quotient. The minimum exists by compactness of the periodic Sobolev embedding, and every minimizing function satisfies the weak eigenvalue equation by first variation.

**Theorem.** Let \(k\) be the unique root in \((0,\pi/g)\) of
\[
  2k\tan(kg/2)=\alpha.
\]
Then \(\lambda_1(Y)\le k^2\), with equality if and only if all cyclic gaps equal \(g\). For \(L=2\pi\) this is exactly [P. Exner, Conjecture 5.1](https://arxiv.org/pdf/1906.01229), for all positive repulsive strengths in the 2019 convention. No minimization or higher-dimensional claim is made.

**Proof.** The function on the left of the displayed equation increases continuously from zero to infinity on the given branch. For \(0<l<\pi/k\) set
\[
 w_l(s)=\frac{\cos(k(s-l/2))}{\cos(kl/2)},\qquad 0\le s\le l.
\]
It is positive, equals one at both endpoints, solves \(-w_l''=k^2 w_l\), and has endpoint slopes \(+k\tan(kl/2),-k\tan(kl/2)\), respectively.

If all gaps equal \(g\), concatenate \(w_g\) periodically. The resulting positive function \(w\) satisfies the interface conditions and is a ground state: for periodic \(f=w v\), integration by parts on all gaps gives
\[
 q_Y[f]-k^2\|f\|_2^2=\int_0^L w^2|v'|^2\,dx\ge0.
\]
Indeed the endpoint terms sum to \(-\alpha\sum_y |f(y)|^2\); \(w\) is bounded away from zero, so the calculation applies throughout the form domain by density, or directly by the product rule. Equality holds for \(f=w\).

Now suppose the gaps are not all equal. If some \(l\ge\pi/k\), extend the first Dirichlet sine from that gap by zero. It belongs to the periodic form domain, all its site values vanish, and its Rayleigh quotient is \(\pi^2/l^2\le k^2\). For \(l>\pi/k\) this is strict. At \(l=\pi/k\), if the lowest energy equalled the quotient, the sine would satisfy the eigenfunction interface conditions. Its derivative has a nonzero jump at a zero-valued endpoint adjacent to a gap on which it vanishes (there are at least two distinct sites), which is impossible. Thus \(\lambda_1(Y)<k^2\) here as well.

If all \(l_j<\pi/k\), concatenate \(w_{l_j}\) to obtain a continuous periodic trial function \(w\); the derivative need not match the interface law for a trial function. On each gap integration by parts gives
\[
 \int_0^{l} (|w_l'|^2-k^2 w_l^2)ds=[w_l'w_l]_0^{l}=-2k\tan(kl/2).
\]
The penalty is \(N\alpha\). Since \(x\mapsto\tan x\) is strictly convex on \((0,\pi/2)\), and the gaps have mean \(g\),
\[
 q_Y[w]-k^2\|w\|_2^2=N\alpha-2k\sum_j\tan(kl_j/2)
 < N\alpha-2kN\tan(kg/2)=0.
\]
Therefore the Rayleigh principle gives the strict comparison on all unequal configurations. Equal cyclic gaps describe precisely the rotations of the equally spaced configuration. ∎
