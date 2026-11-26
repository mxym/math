# Exact conic bounds for an odd cycle with one distinguished edge

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Consider an odd cycle on vertices \(0,1,\ldots,L\), where \(L\ge2\) is even. Give the \(L\) edges of the path \(0\to1\to\cdots\to L\) weight one and the closing edge \(\{0,L\}\) weight \(t\ge0\). We compute **both** of [Zhou's path-strengthened conic bounds](https://arxiv.org/html/2610.34273v3#S5.SS3), not in general the graph tensor's actual asymptotic rank exponent. Zhou's Theorem 6.6 is the special case \(t=1\).

For \(t\le (L-1)/L\), the conic value and the actual graph exponent are all \(L\) over every field. For \(t\ge (L-1)/L\), let \(x\in(0,2]\) be the unique solution of
\[
K=x+\frac{L-2}{4}x^2,\qquad t=1+\frac{1-x}{K}.
\]
Then, putting \(T=2+(L-1)x\),
\[
U^{\Delta}_{\mathrm{CP}}(W_t)=U^{\Delta}_{\mathrm{SDP}}(W_t)
=\frac{T^2}{4K}
=L+\frac{(2-x)^2}{4K}
=L-1+t+\frac{x^2}{4K}.
\]
The parameter map has derivative \((-1+(L-2)x(x-2)/4)/K^2<0\), value \((L-1)/L\) at \(x=2\), and tends to infinity as \(x\downarrow0\). The formula gives \(L+1/(L+2)\) at \(t=1\). The maximum cut is \(\max(L,L-1+t)\); the conic value is strictly greater than this for every \(t>(L-1)/L\).

## Upper bound: interpolate two *linear triangle certificates*

Write \(P=(p_{ij})\) for any feasible CP point, let \(E=\sum_{i=0}^{L-1}p_{i,i+1}\) and \(C=p_{0L}\), and define
\[
a=(1,x,\ldots,x,1),\qquad Q_x=\sum_{i<j}a_i a_jp_{ij}.
\]
Copositivity of \(J-2P\) gives \(Q_x\le T^2/4\). We use the triangle inequalities alone to show \(Q_x\ge K(E+tC)\). Indeed,
\[
Q_x-K(E+tC)=x(A+xB),
\]
where
\[
A=\sum_{j=1}^{L-1}(p_{0j}+p_{jL})-E,\qquad
B=\sum_{0<i<j<L}p_{ij}-\frac{L-2}{4}(E+C).
\]
For \(A\ge0\), keep the two endpoint path edges, and bound the other path edges by two endpoint distances: use endpoint \(0\) for the pairs \((2,3),(4,5),\ldots,(L-2,L-1)\), and endpoint \(L\) for \((1,2),(3,4),\ldots,(L-3,L-2)\). Each endpoint distance is charged exactly once.

For \(A+2B\ge0\), use \(x=2\) and the [even-path charging calculation](WeightedOddCycleExactThreshold.md#all-even-crossing-paths-the-exact-uniform-threshold), before imposing its copositive upper bound. Explicitly, put \(d_{ij}=1-p_{ij}\) on opposite-parity pairs. Then \(Q_2-L^2\) is the weighted sum of same-parity \(p\)'s minus the weighted sum of opposite-parity \(d\)'s, with endpoint weights 1 and interior weights 2. For each nonadjacent opposite-parity \(i<j\), charge \(d_{ij}\) to \(d_{i,i+1}+p_{i+1,j}\), to \(d_{j-1,j}+p_{i,j-1}\), or to their average. Use only the first option when \(i=0\), only the second when \(j=L\), and the average otherwise. The interior same-parity pairs cancel, each adjacent \(d\) ends with coefficient \(L\), and the endpoint same-parity pairs contribute at least \((L-1)C\), by \(p_{0j}+p_{jL}\ge C\). Thus \(Q_2-L^2\ge (L-1)C-L\sum_i d_{i,i+1}\), or \(Q_2\ge LE+(L-1)C\). (For \(L=2\) this is an identity.) This is exactly \(A+2B\ge0\).

Now \(A+xB=(1-x/2)A+(x/2)(A+2B)\ge0\) throughout \(0\le x\le2\). Dividing \(K(E+tC)\le Q_x\le T^2/4\) by \(K>0\) proves the upper bound. The certificate at \(x=2\), together with \(C\ge0\), also proves the constant regime below the threshold.

## Matching SDP witness: nonuniform mixture of maximum cuts

For each edge of the unweighted cycle there is an alternating cut that omits exactly that edge. Write \(s_j\in\{-1,1\}^{L+1}\) for its coloring, oriented so its coordinate sum is one; use \(j=0\) for the closing-edge omission. Let \(S\) have these as columns. By rotation, \(S\mathbf1=\mathbf1\). Let \(h=2-x\), so \(a^\mathsf{T}s_0=h\) because both endpoints have sign \(+1\), and \(a^\mathsf{T}s_j=x\) for \(j\ne0\) because the endpoints have opposite signs.

For \(0<x<2\), take
\[
\lambda=\frac{T}{T(x/h+L)-x},\qquad
\lambda_0=\frac{x}{h}\lambda,\qquad
M=\lambda_0+L\lambda.
\]
The denominator is positive since \(TL>x\). Let \(P\) be the sum of cut semimetrics \((J-s_js_j^\mathsf T)/2\) with these positive weights, using \(\lambda\) for every \(j\ne0\). It satisfies every triangle inequality and is nonnegative. Moreover,
\[
J-2P=S\left[\operatorname{diag}(\lambda_0,\lambda,\ldots,\lambda)
-(M-1)\mathbf1\mathbf1^\mathsf T\right]S^\mathsf T\succeq0,
\]
since \(M-1=\lambda x/T>0\) and
\[
(M-1)(1/\lambda_0+L/\lambda)=(h+Lx)/T=1.
\]
This is the weighted Cauchy–Schwarz inequality. Also \((J-2P)a=0\): each \(\lambda_j a^\mathsf T s_j=\lambda x\), and \(\sum_j s_j=\mathbf1\). Thus \(Q_x=T^2/4\).

For the single closing-omission cut, \(Q_x=(T^2-h^2)/4=KL\). For each other omission cut, \(Q_x=(T^2-x^2)/4=KL+1-x=K(L-1+t)\). In every case this is \(K\) times that cut's objective, so the same holds for the weighted sum. Therefore the SDP attains \(T^2/(4K)\), and hence both bounds agree. At and below \(t=(L-1)/L\) the single closing-omission cut supplies the value \(L\).

## Scope and examples

For \(t>(L-1)/L\), a CP optimizer must saturate the copositive test at the strictly positive vector \(a\). If a symmetric copositive matrix \(H\) has \(a^{\mathsf T}Ha=0\) at such a vector, evaluate it at \(a\pm\varepsilon v\) for arbitrary \(v\) and sufficiently small \(\varepsilon>0\). The linear term must vanish and then \(v^{\mathsf T}Hv\ge0\). Thus every CP optimizer in the active regime is automatically SDP-feasible, not just the explicit witness above.


For the weighted pentagon (\(L=4\)) and \(t\ge3/4\), the conic value has the equivalent form
\[
t+3+\frac{1}{2(t+1+\sqrt{(t+1)^2-3})}.
\]
For example at \(t=4/5\) this is approximately \(4.018350\), improving the convex upper bound from the two endpoints \(t=3/4,1\), which is \(4.033333\ldots\). At \(t=1\), the value is still \(25/6\) and does **not** close the unweighted rank problem. The known grouped rectangular lower bound remains different from this conic upper bound for general \(t\). A separate exact-arithmetic check verified the objective equality, positive-vector kernel and triangle constraints for 1,840 rational parameter choices, even \(2\le L\le40\). The proof above does not depend on those checks.
