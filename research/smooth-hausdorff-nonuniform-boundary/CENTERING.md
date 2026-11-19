# Explicit centering examples

The implicit centering (1) in PROOF.md needs no geometric hypothesis on the minimum set. The following are consequences of Laplace's method, not separate extreme-value theorems.

Let $Z=\{f=f_0\}$ and $m=\dim M$. If $v_g(Z)>0$, including when $Z$ has no interior, then
$$
 w_n=\log n+(m-1)\log\log n+\log(\alpha_m f_0 v_g(Z))+o(1).
$$
Indeed, after factoring out $w^{m-1}e^{-w}$ in (1), bounded convergence on the compact manifold leaves precisely $f_0v_g(Z)$.

If $Z$ is a compact smooth embedded submanifold of codimension $c>0$ without boundary, assume additionally $M,g,f$ smooth enough for normal tubular coordinates and $f$ twice continuously differentiable near $Z$, with positive definite Hessian of $f/f_0$ on each normal space. Write $H_z$ for that normal Hessian in a $g$-orthonormal basis. Then
$$
 w_n=\log n+(m-1-c/2)\log\log n+
 \log\!\left[\alpha_m f_0(2\pi)^{c/2}
    \int_Z (\det H_z)^{-1/2}\,dv_Z(z)\right]+o(1).
$$
For a proof, put $F=f/f_0$. Outside a fixed tube $F-1$ has positive minimum. In a sufficiently small tube, compactness and the Hessian assumption give $F(z,y)-1=\tfrac12 y^TH_z y+o(|y|^2)$ uniformly in normal coordinates and a lower bound $c_1|y|^2$. The normal volume Jacobian tends uniformly to one on the zero section. Substitute $y=w^{-1/2}y'$ and apply dominated convergence using $\exp(-c_1|y'|^2)$ in finitely many patches with a partition of unity. This gives
$$
 \int_M f F^{m-1}e^{-w(F-1)}dv_g
 \sim f_0(2\pi/w)^{c/2}\int_Z(\det H_z)^{-1/2}dv_Z.
$$
Both displayed centerings follow by (1) and $w_n/\log n\to1$. In dimension one the cases of positive nonuniform minima have classical precedents in maximal-spacing theory; these examples illustrate how the centering depends on the density, not a claim that those special cases are new.
