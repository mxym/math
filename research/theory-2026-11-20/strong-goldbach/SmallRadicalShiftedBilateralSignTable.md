# Bilateral shifted high terms: exact sign table and a true same-parity two-window estimate

Use the smooth shifted-source high coefficient \(T(n)\), constants \(P,L,H=L^{3/5},U_\pm,R_+,z,y\), and the rough model \(V_y(P)\) from the preceding notes. Fix a symmetric compact \(J\subset(0,1)\), so \(n\in I=PJ\) if and only if \(m=P-n\in I\). Only actual squarefree rows are used below.

## 1. A sign table, without assuming mass of any pair class

Let \(A_2,A_3\) be ranks two and three with all prime factors \(>R_+=P^{1/4}\). Then \(T(x)=-\log x\) on them, and \(\lambda(A_2)=+1,\ \lambda(A_3)=-1\). Let \(B_3\) be rank three with two distinct primes \(p,q\) in \((z,U_-]\), their product \(b=pq>U_-\), and final prime \(r>R_+\). Then
\[
T(x)=(1-g(\log b))\log r\in[0,\log r],\qquad
\lambda(x)=-1\quad (x\in B_3).
\]
This follows from \(D_g(b)=1-1-1+g(\log b)\). The largest prime on \(B_3\) is \(\gg_J P/U_-^2=P^{1/2+o(1)}\), and is the final prime.

On the bilateral domains built from these three classes one may first remove the translated first-cover selector \(C\) at absolute cost \(o(PV_y/L)\) for any fixed \(M>200\). Apply the companion final-prime BV estimate with the other one/two true primes fixed as \(d_0\). They all exceed \(z=\exp(L^{.24})\), hence exceed the packet primes of size at most \(\exp(2L^{.2})\), and target primes; the final endpoint scale \(P/d_0\) has a fixed positive power. The rough and translated forbidden classes are reduced and disjoint by the same proof. On \(A_i\), the sum of reciprocals of the short labels is bounded. For \(B_3\), \(\sum_{z<p\le U_-}1/p=O(\log L)\) by Mertens, so \(\sum_{d_0}1/d_0=O((\log L)^2)\), still absorbed by the strict \(M/200>1\) margin. The weight \(|T(x)|\le L\ll\log r\) for the final prime used in this count. Both sides are \(y\)-rough, so ignoring the extra opposite-class constraints when paying the uncovered error is valid.

After removing \(C\), the actual paired score for the involution \(n\leftrightarrow m\) is
\(\mathcal H(n,m)=T(n)\lambda(m)+T(m)\lambda(n)\). Its sign table, using symmetry in the two inputs, is:

| Pair types | Paired score |
|---|---|
| \(A_2,A_2\) | \(-\log n-\log m<0\) |
| \(A_2,A_3\) | \(\log n-\log m=O_J(1)\), with rank 2 in \(n\), rank 3 in \(m\) |
| \(A_3,A_3\) | \(+\log n+\log m>0\) |
| \(A_2,B_3\) | \(\log n+T(m)>0\) |
| \(A_3,B_3\) | \(\log n-T(m)\ge\log(n/m)+\log b(m)>0\) for large \(P\) |
| \(B_3,B_3\) | \(-T(n)-T(m)\le0\) |

In the only nontrivial strict inequality, \(\log n-\log r_m=\log(n/m)+\log b(m)\), with the first term bounded centrally and the second \(\ge(1/4-o(1))L\). The \(A_2,A_3\) residual was bounded at the needed scale by the same-target upper sieve in the preceding note. This table is pointwise on actual pairs only. It neither asserts that any favorable pair type has a lower density nor that those favorable pairs offset the two negative types.

## 2. A same-parity rank-two joint upper bound

Fix \(\delta/2<\gamma<\delta\) (for example \(\gamma=3\delta/4\)). Consider the actual \(A_2,A_2\) rows \(n=rq,\ m=st\) whose smaller true primes satisfy
\[
|\log r-L/3|\le L^{1-\gamma},\qquad
|\log s-2L/5|\le L^{1-\gamma}.
\tag{1}
\]
The log factor profile intervals are disjoint for large \(P\), so \(r\ne s\) and \(r,s\) are coprime. With the actual complementary target fixed, \(r q+s t=P\). Fix integer \(q_0,t_0\) solving this equation and write all solutions as
\[
q=q_0+s k,\qquad t=t_0-r k,\qquad k\in\mathbb Z.
\]
The actual constraints \(rq,st\in I\) cut out one interval of length \(O_J(P/(rs))\); for symmetric \(I\) the two conditions are identical. Its scale \(P/(rs)=P^{4/15+o(1)}\) is polynomial. Both \(q,t\) are actual primes at polynomial scales far above the small sieve level \(Z=P^{1/40}\). This uses no approximation of the determinant \(P\) or independence across the two sides.

For every small prime \(\ell\le Z\), the affine slopes \(s,-r\) are units. The two forbidden residue classes of \(k\) coincide exactly if \(\ell\mid(rq_0+s t_0)=P\); at 2 they accordingly coincide since \(P\) is even. Apply the elementary two-class Selberg quadratic upper bound with cutoff \(Z\) and error \(O(Z^6)\) on this exact interval. The same local product as in the Goldbach upper sieve gives at most
\[
\ll S(P)\frac{P}{r s L^2}+O(Z^6)
\]
possible \(k\) for each \(r,s\). The \(O(1)\) counting endpoints are absorbed in the displayed error. No distribution at a coupled growing modulus is used here.

By PNT plus partial summation, the reciprocal prime mass in each window (1) is \(O(L^{-\gamma})\): the main term is the logarithm of the ratio of its endpoint logarithms, and the exponential PNT error is negligible. Summing modulus-free sieve floors gives \(O(P^{11/15+3/20+o(1)})=O(P^{53/60+o(1)})\), since the number of \((r,s)\) pairs is at most \(P^{11/15+o(1)}\). Thus the number of true rows in (1) is
\[
O(P S(P)L^{-2-2\gamma}+P^{53/60+o(1)}).
\]
Here both orientations have nonpositive score, and their absolute high coefficient is \(O(L)\) per row. Their total weight, even without deleting the first-cover selector (which is \(\le1\)), is
\[
O(P S(P)L^{-1-2\gamma}+P^{53/60+o(1)})
=o(PV_y(P)/L),
\]
because \(V_y(P)\sim e^{-\gamma_{\rm Euler}}S(P)L^{-\delta}\) and \(2\gamma>\delta\). This estimate genuinely uses both sides' windows: an upper of the same type with only one reciprocal factor \(L^{-\gamma}\) would not meet the relative goal because \(\gamma<\delta\). This conclusion is only for the specified shrinking double window, not the entire \(A_2,A_2\) sector.

No exact map from an adverse pair \(A_2,A_2\) to sufficiently many genuine \(A_i,B_3\) rows was established. Combining their opposite coefficient signs or separate one-side marginal estimates is not a substitute for such a map or a true joint count.
