# An explicit growing interval of moment orders

This quantitative supplement uses V.-E. Brunel's **existing** uniform deviation bound for missing volume ([2013 preprint, Theorem 1](https://arxiv.org/pdf/1311.2902), [journal-paper preprint, §5, Theorem 4](https://arxiv.org/pdf/1704.01620)). It concerns the comparison of hulls in two nested bodies, not a new proof of Brunel's concentration theorem or an optimal growth-rate assertion.

Let \(d\ge2\), \(\alpha=2/(d+1)<1\), and keep the notation \(F_p,V_n\) of PROOF.md.

1. For every fixed \(B>0\) there are \(c_{d,B}>0, N_{d,B}<\infty\) such that for all \(n\ge N_{d,B}\), all \(K\subset L\), and simultaneously all \(|p|\le B n^\alpha\),
\[
 E F_p(V_n(L))-E F_p(V_n(K))\ge c_{d,B}(F_p(|L|)-F_p(|K|)).
 \tag{G1}
\]
2. For some \(\kappa_d,c_d>0\), all sufficiently large \(n\), all \(K\subset L\) and \(|p|\le\kappa_d n^\alpha\log n\), the same inequality holds with \(c_d n^{-\alpha/2}\) on the right in place of \(c_{d,B}\). In particular the sign is strict under proper inclusion.

## Negative moments in the needed growing range

Uniformly over convex bodies, Brunel's bound says, with constants depending only on dimension, that for \(Z_k=V_k(K)/|K|, X_k=1-Z_k\), and \(t>0\),
\[
 \Pr(X_k>C k^{-\alpha}+t)\le C e^{-c k t}.
 \tag{G2}
\]
In particular \(E X_k^2=O(k^{-2\alpha})\), by integrating the tail of \((X_k-C k^{-\alpha})_+\). There are constants \(\epsilon,c_1,C_1>0\) depending only on \(d\) such that for large \(k\)
\[
 E Z_k^{-a}\le C_1 e^{c_1 a k^{-\alpha}},\qquad 0\le a\le\epsilon k .
 \tag{G3}
\]
On \(Z_k\ge1/2\), \(-\log Z_k\le2X_k\), and integrating (G2) gives \(E e^{2a X_k}\le e^{2aC k^{-\alpha}}(1+2a C/(ck-2a))\) for \(2a<ck\). Choose \(\epsilon<c/4\).

For small \(Z_k\), take the independent simplex-block bound from §1 of PROOF.md:
\(\Pr(Z_k\le s)\le (D s^{1/d})^r\), \(D\ge1\), \(r=\lfloor k/(d+1)\rfloor\). Set \(s_0=(2D)^{-d}<1/2\). For \(0<a<r/d\), integration of this tail below \(s_0\) gives
\[
 E[Z_k^{-a};Z_k<s_0]\le s_0^{-a}2^{-r}\left(1+\frac{a}{r/d-a}\right).
\]
This is bounded by 2 after decreasing \(\epsilon\) so that \(a\le r/(2d)\) and \(a|\log s_0|\le r\log 2/2\). For \(s_0\le Z_k<1/2\), the expression is bounded by \(s_0^{-a}C e^{-ck/4}\) for all large \(k\), by (G2). Decrease \(\epsilon\) once more. This proves (G3); \(a=0\) is immediate. The restriction \(\alpha<1\) ensures both advertised order windows are \(o(n)\), so (G3) applies to every fixed multiple of their upper endpoints when \(k=\lfloor n/2\rfloor\) or \(k=n\).

## Add-one estimates and transfer to all inclusions

Use \(n=m+1\), \(k=\lfloor n/2\rfloor\), \(v=|K|\) and normalized volumes. By the conditional Carathéodory inequality (6) of PROOF.md and the derivative bound \(F'_p(s)\le Z_k^{-|p|-1}\) for \(Z_k\le s\le1\),
\[
 0\le E[F_p(Z_n)-F_p(Z_m)]
 \le C n^{-1}\,(E Z_k^{-2(|p|+1)})^{1/2}(E X_k^2)^{1/2}
 \le C n^{-1-\alpha} e^{C(|p|+1)n^{-\alpha}} .
 \tag{G4}
\]
In (G2) choose \(t=c^{-1}m^{-1}\log(1+2C/\eta_d)\), where \(\eta_d\) is the uniform event probability in (4) of PROOF.md. With probability at least \(1-\eta_d/2\) we have \(Z_m\ge1-C_d' n^{-\alpha}\). Intersect this with the event that adding the fixed exterior point \(x\) increases normalized volume by at least \(b_d/m\). With probability at least \(\eta_d/2\) both hold. Over the credited interval \([Z_m,Z_m+b_d/m]\) we have \(|\log s|\le C_d'' n^{-\alpha}\) for large \(n\). Hence, regardless of a possible much larger actual new hull,
\[
 E[F_p(Z_x)-F_p(Z_m)]\ge c n^{-1} e^{-C(|p|+1)n^{-\alpha}} .
 \tag{G5}
\]
In (G4)–(G5) a common \(C\) can be taken depending only on dimension. For \(|p|\le B n^\alpha\), subtracting (G4) from (G5) leaves at least \(e_{d,B}/n\) for all sufficiently large \(n\). For \(|p|\le\kappa_dn^\alpha\log n\), choose \(\kappa_d>0\) so small that \(2C\kappa_d<\alpha/2\). The ratio of the upper bound in (G4) to the lower in (G5) then tends to zero uniformly; the difference is at least \(e_d n^{-1-\alpha/2}\).

For either window, let \(P_n\) denote its order bound. For each fixed sufficiently large \(n\) the fourth-moment estimate (10) of PROOF.md remains finite, uniformly in \(K,L,|p|\le P_n\) when \(1\le\lambda=|L|/v\le2\), by (G3) at \(a=4(P_n+1)=o(n)\). Its constant may depend on \(n,d,P_n\): this is harmless, since the admissible size of the local inclusion step may also depend on \(n\). Thus the event of at least two outside observations incurs an error \(O_{n,d,P_n}(q^{3/2})\), \(q=1-1/\lambda\), as before. Make the steps also satisfy \((P_n+1)\log\lambda\le\log2\); then \(F'_p(s)\le2\) on \([1,\lambda]\) and \(F_p(\lambda)\le 2(\lambda-1)\le4q\). Unlike the rough compact-interval bound, this last factor is independent of \(n\). The binomial expansion and telescoping of §3 of PROOF.md now prove both statements, preserving the stated constant in case 1 and the factor \(n^{-\alpha/2}\) in case 2. The proof gives a range on which uniform comparison holds; it does not identify a threshold exponent at which it fails.
