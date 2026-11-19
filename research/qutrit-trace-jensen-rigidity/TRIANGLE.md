# A positive-definite qutrit triangle for a reciprocal trace Jensen generator

Companion exact certificate. Internally reviewed; not externally peer reviewed.

For the trace Jensen gap
$$
J_f(X,Y)=\tfrac12\operatorname{Tr}[f(X)+f(Y)]-\operatorname{Tr} f((X+Y)/2)
$$
on positive trace-one matrices, let $f(x)=(1+79x)^{-1}$ on $[0,\infty)$. This is finite and continuous at zero, non-affine, and operator convex. Indeed the Schur complement gives
$\left(\begin{smallmatrix}B&I\\ I&B^{-1}\end{smallmatrix}\right)\succeq0$ for each positive definite $B$. Convex combinations of two such block matrices, followed by another Schur complement, give $((1-t)B+tC)^{-1}\preceq(1-t)B^{-1}+tC^{-1}$. Apply this with $B=I+79X,C=I+79Y$.

Use three real symmetric qutrits:
$$
79\rho_\pm=\begin{pmatrix}1&\pm2&0\\\pm2&31&0\\0&0&47\end{pmatrix},\qquad 79\rho_0=\operatorname{diag}(1,23,55).
$$
The three numerators have trace 79; the off-diagonal states have upper-block determinant $31-4=27>0$, so all are positive definite. Flipping the sign of the first basis vector interchanges the endpoints and fixes the middle. Consequently $J_f(\rho_+,\rho_0)=J_f(\rho_-,\rho_0)$.

The gap adds over the upper two-by-two and lower scalar blocks. On the upper blocks the traces of $f$ at the endpoints, the middle state, the midpoint of the endpoints, and the midpoint of an endpoint with the middle state, respectively, are
$$
\frac{34}{60}=\frac{17}{30},\quad \frac12+\frac1{24}=\frac{13}{24},\quad \frac12+\frac1{32}=\frac{17}{32},\quad \frac{30}{55}=\frac6{11}.
$$
Here the endpoint matrices to invert are $\left(\begin{smallmatrix}2&\pm2\\\pm2&32\end{smallmatrix}\right)$, and the last ones are $\left(\begin{smallmatrix}2&\pm1\\\pm1&28\end{smallmatrix}\right)$. Thus the endpoint-endpoint gap is $17/480$ and the endpoint-middle gap is $23/2640$. On the scalar block these two gaps are $0$ and $(1/48+1/56)/2-1/52=1/8736$. In total,
$$
J_f(\rho_+,\rho_-)-4J_f(\rho_+,\rho_0)=\frac1{1760}-\frac1{2184}>0.
$$
Taking square roots violates the triangle inequality. Normalizing the trace by $1/3$ multiplies all squared quantities by the same factor and does not repair the triangle. Adding zeros in extra dimensions cancels $f(0)$ in each gap, and the strict inequality persists under mixing the resulting states with a sufficiently small common maximally mixed state; thus every fixed dimension at least three admits full-rank witnesses. Neither the extension nor the affine freedom in the generator is needed for the displayed witness.

The assertions in Teng Zhang, [arXiv:2602.08164v1, Theorem 1.9, Corollary 1.10 and Corollary 10.3](https://arxiv.org/html/2602.08164v1#S1.SS3), as stated in v1, include this generator and these matrices. This concerns the general operator-convex metric assertion, **not** Zhang's separate Shannon-generator Theorem 1.6, Virosztek's Shannon metric theorem or the known qubit Hilbert embedding. The example is a triangle obstruction to metricity, not merely a negative-type test. The qualitative existence mechanism is already implicit in results of Matsumoto; see [the derivation](PRIOR-IMPLICATION.md). No priority claim is made.
