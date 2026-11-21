# One budget for deeper broad and narrow rough-reflected triprime debit

This extends [RoughTriprimeDebitBudget](RoughTriprimeDebitBudget.md) below its previous reflected threshold \(x^{.138}\). It retains the actual quotient bands, the actual reflected mark, the original coefficient, the actual centered correction and its **single** negative mean. It accounts for all previously unhandled reflected ranks in the two stated deeper rough windows, not for arbitrarily small factors. It gives no Goldbach bound.

## Coverage and joint statement

Use all definitions of the cited note, including its high quotient chart, original \(C\), old Selberg square \({\cal R}(b)\), \(B'=D_B(q)/\log q+2F_2/3\), and mean \(-(\rho+o(1))M_N\). In particular
\[
 \rho=\frac{40}{3}J_s h_a h_Q h_E^2(1-h_E).
\]
Let \(\mathcal D\) be the broad actual quotient packet of that note: true squarefree triprime \(b\), with a true factor in each of \(B_2=(.164,.16524)\), \(B_3=(.16525,.167)\), and the old actual high \(s,a,Q\) and central unit conditions. Let \(\mathcal B\subset\mathcal D\) be the *narrow* actual six-distinct-prime packet of [CoupledQRShortPart](CoupledQRShortPart.md), with
\[
 s\in(.1384,.1386),\quad a\in(.0684,.0686),\quad Q\in(.2974,.2976),\quad
 r\in(.1650,.1651),\quad b_2\in(.16512,.16524),\quad b_3\in(.16525,.16545)
\]
in exponent notation. The independent \(b_2,b_3\) bands and the remaining actual labels are not weakened in these definitions.

At each sufficiently large even \(N\), the following two **disjoint physical charges** can be paid from that one \(\rho M_N\):
1. the actual added positive debit \(\frac13 W_s(q)(-C(m))_+\) on \(\mathcal D\setminus\mathcal B\), with exactly one \(E\)-mark and \(P^-(m)>x^{.110}\), costs \(\le(.801\,\rho+o(1))M_N\);
2. the entire corrected positive weight \(W_s(q)\big((B'-1/3)C(m)\big)_+\) on \(\mathcal B\), with exactly one \(E\)-mark and \(P^-(m)>x^{.055}\), costs \(\le(.141\,\rho+o(1))M_N\).

The second packet includes its pre-existing positive part *and* the new increment on that packet. The first upper is allowed to majorize its outside-\(\mathcal B\) portion by an upper calculated on all of \(\mathcal D\), a conservative overcount of the bound only; the actual charges are disjoint and no part of the negative mean is counted twice. The combined coefficient is strictly less than \(.942\), leaving more than \(.058\) of the mean before any further charge. This supersedes, rather than adds to, the older rough-charge comparison. No pre-existing positive part outside \(\mathcal B\) is included, and the masks with smaller least factor or different quotient shape remain open.

## Exact refined sign at the half and its genuine cutoff cost

For either fixed threshold \(\alpha\in\{.110,.055\}\), remove squareful rough \(m\) with power-small physical error as in the prior note. Write \(m=p u\) with the actual \(E\)-mark \(p\), and \(k=\Omega(u)\). In this sector \(\Lambda(m),T_2,T_3\) vanish exactly, as all its prime factors exceed \(x^\alpha>H^2\). Thus \(-C=T_1\) with its original sharp cutoff \(U=\sqrt x/H^4\).

For a polynomially rough bounded rank, the difference between this cutoff and the half \(\sqrt m\) has \(o(M_N)\) cost **on the genuine weighted packets here**. Here is the explicit comparison. Fix \(\eta>0\) and take the union of profile slabs
\[
 \left|\sum_{j\in S}\log_x p_j-\tfrac12\right|<\eta
\]
over nonempty proper subsets \(S\) of the distinct true prime factors of \(m\). The actual cutoff difference \(U<d\le \sqrt m\) forces membership for sufficiently large \(x\), since \(\log U=\tfrac12 L-4L^\sigma\) and \(m\in[x,3x/2)\). The original sharp score and its half replacement have absolute difference at most \(O_\alpha(L)\) on this slab union and vanish in difference outside it. Apply the **same nonnegative inclusion and Selberg square** as in the cited note, retaining its independent slots \(q_1=s b_2,\ q_2=b_3d',\ q_3=a\) and genuine reflected prime SW source \(p\). Source \(u\) is now a real prime product of bounded rank, and the angular slab restrictions are separated by freezing the actual \(p\) in fine relative boxes; only an arbitrarily small enlargement of the slabs is needed. The other prime-factor conditions then act on the long coefficient alone. The principal can be evaluated with the same uniform logarithmic reserve; the overlap deletion of modulus primes and the target is power-small as before (all source primes \(>x^{.055}>x^{.034}\) exclude sieve-prime overlaps). For each rank, ordinary PNT by fixing all but one real prime gives the profile density \(\prod_j dt_j/t_j\) on the sum-one simplex, with all \(t_j\ge\alpha\), after multiplying by \(L\), and with fixed geometric boundaries approximated from outside. Each specified slab has simplex volume \(O_\alpha(\eta)\): its central hyperplane is not constant on the simplex because \(S\) is proper and nonempty. The density is bounded for fixed \(\alpha\). After the same \(1/G_{R'}\) factor this costs \(O_\alpha(\eta M_N)+o_{\eta,\alpha}(M_N)\). Let \(\eta\downarrow0\) *after* the asymptotic in \(x\); this proves the asserted \(o(M_N)\) cost, without assuming actual divisors never enter the neck. The same argument handles the \(O(1/L)\) difference between \(\log_x p_j\) and \(\log p_j/\log m\) in the subsequent fixed profile inequalities.

At the half, put \(t=\log p/\log m\), \(A=1/2-t\) and \(t_S=(\sum_{j\in S}\log p_j)/\log m\) for subsets of the \(k\) true factors of \(u\). For \(k\ge2\), \(\sum_{d\mid u}\mu(d)=\sum_{d\mid u}\mu(d)\log d=0\), since \(u\) is squarefree composite. Open the \(p\)-bit in the half-cutoff \(T_1\), and in the term without \(p\) replace its long part by the complementary subsets of \(u\). This gives the exact half score away from the ties:
\[
 \frac{T_1^{\rm half}}{\log m}
 =-\sum_{\substack{S\subseteq u\\t_S<A}}(-1)^{|S|}
       \big[(-1)^k(t+t_S)+(1-t-t_S)\big]
 =\begin{cases}
 -\displaystyle\sum_{t_S<A}(-1)^{|S|},& k\ {\rm even},\\
 -2\displaystyle\sum_{t_S<A}(-1)^{|S|}(A-t_S),& k\ {\rm odd}.
 \end{cases}                                                            \tag{1}
\]
Here \(S\subseteq u\) means subsets of the prime list, not integers. This is a marked **physical** identity, not a parity asymptotic.

As before rank-two \(m\) has exact \((-C)_+=\log p\), and rank-three has no negative \(C\). In rank four with all singles below the half use the shorter complementary pair proof of the preceding note. If one factor is above the half (possible at the narrower packet's smaller \(\alpha\)), all short divisors are exactly the divisors of its composite complement, and the sum \(T_1^{\rm half}\) is zero. The same giant-factor argument is valid for all higher ranks here. For rank five, if there is no giant, all singles are short and no fourfold product can be short. Dropping the negative triples and retaining all pair weights gives \((T_1^{\rm half})_+\le3\log m\). This proves the same bound also with a giant (when the score is zero).

For broad \(\alpha=.110\) rank five (\(k=4\)), no two factors of \(u\) can lie in a subset below \(A<.189+o(1)\); hence (1) is \(j-1\) in the normalized exponent limit, with \(j=\#\{i:t_i<A\}\). Always \(j\ge1\): otherwise \(1-t=\sum_{i=1}^4t_i\ge4(1/2-t)\), contradicting \(t<1/3\). This exact rank-five sign formula replaces the much larger unweighted majorant from the earlier rough cutoff.

For all other \(k\ge5\), the following uniform upper on \(T_{1,+}^{\rm half}/\log m\) follows immediately from (1) (with \(o(1)\) harmless for fixed ranks):
\[
 c_k(\alpha)=
 \begin{cases}
 \min\{2^{k-1},\ \sum_{j\ {\rm odd},\, j\alpha<.189}\binom{k}{j}\},&k\ {\rm even},\\
 \min\{2^{k-1},\ 2\sum_{j\ {\rm odd}}\binom{k}{j}(.189-j\alpha)_+\},&k\ {\rm odd}.
 \end{cases}                                                            \tag{2}
\]
The subset bounds discard the even-subset contributions, and \(A\le.189+o(1)\). The first cap \(2^{k-1}\) is also elementary: for even \(k\), hence odd total rank, pair each even subset of the full prime list with its odd complement. Its contribution is \(1-\sum_{j\in S}t_j\) if the even subset is short, and \(-\sum_{j\in S}t_j\) otherwise, so the total is the number of short even subsets minus \(2^{k-1}\). For odd \(k\), complementary subsets have the same parity, so at most \(2^{k-1}\) positive subsets can contribute and each weight is at most one. On the narrow packet use \(c_4=3\) in addition to (2). On the broad packet only \(k\le6\) is possible, and on the narrow packet only \(k\le12\), from \(1-t\le.689+o(1)\).

## Principal arithmetic and the finite envelope

Apply the transfer and its **nonnegative physical** Selberg majorant from the preceding note, keeping \(s,a,b_2,b_3\) genuine, while \(Q\) and the third quotient prime are dropped only in that upper. The SW, distinctness and rail checks are identical: the source \(p\) is independent and the long coefficient may be an arbitrary divisor-bounded sum of the prescribed true prime products. For a fixed rank \(k\) of \(u\), the coefficient of the \(\log m\)-weighted principal is an integral over
\[
 .311\le t\le .321,\quad u_i\ge\alpha,\quad \sum_{i=1}^k u_i=1-t,
 \qquad
 \frac{dt\,du_1\cdots du_{k-1}}{k!\,t\,u_1\cdots u_k}.
\]
The factor \(k!\) is exact for the unordered distinct non-marker prime factors. If a second \(E\)-prime is allowed by these bounding conditions, counting it is **only** a nonnegative inclusion in the upper. Before the signed Selberg coefficient is evaluated, modulus-prime collisions are removed in the unprogressioned main by power-small errors, not by a termwise monotonicity claim for its signed coefficients. All profile tests in the integral have fixed piecewise smooth boundaries; the ordinary PNT for the free prime, after fixing the other actual factors, gives this integration by enclosing in finite boxes. The reflected coefficient for rank two remains \(I_2=\log(.689/.679)\) when its weight is \(\log p\).

For \(k\ge4\), bounding the product denominator by its minimum on the simplex, achieved at a vertex by the concavity of \(\sum_i\log u_i\), gives
\[
 H_k(\alpha)=
 h_E\frac{(.689-k\alpha)_+^{k-1}}
  {k!(k-1)!\,\alpha^{k-1}(.689-(k-1)\alpha)}
\]
when \(k\alpha<.689\), and zero otherwise. The bound increases with the sum \(1-t\), so its maximum uses \(.689\). This envelope suffices for the higher broad ranks and all narrow ranks. For the broad \(k=4\) case let \(J_5\) be the integral with weight \((j-1)/3\); the \(1/3\) is the actual adjustment coefficient. The exact rational checker gives \(J_5\le .002546403\).

For clarity the certificate of this last upper writes \(u_i=\alpha+S y_i\), \(S=1-t-4\alpha\), \(\sum y_i=1\), \(\alpha=.110\). The short threshold for \(y_i\) is \((.5-t-\alpha)/S\), decreasing in \(t\). On each of five exact equal rational \(t\)-slabs use its lowest \(t\) for the largest threshold and largest Jacobian \(S^3\), and largest \(t\) for the smallest \(S\) in the denominators. Each cell in a \(200^3\) cube mesh on \((y_1,y_2,y_3)\) uses its coordinate minima and the true minimum of \(y_4=1-y_1-y_2-y_3\) on its simplex intersection for the positive reciprocals and indicators. If the remaining number of mesh lengths before the simplex wall is 1, 2 or at least 3, the cell-volume fraction is respectively \(1/6,5/6,1\). The reciprocal is rounded upward by exact integer division. Finally \(dt/t\le \Delta t/t_{\rm low}\). This is an upper enclosure, not numerical random quadrature.

For broad \(\mathcal D\setminus\mathcal B\), retain the full \(J_s h_a h_{B_2}h_{B_3}\) upper. Relative to \(\rho\), the fraction is at most
\[
 R_{\rm broad}=
 \frac{h_{B_2}h_{B_3}
       [I_2+3J_5+c_5(.110)H_5(.110)+c_6(.110)H_6(.110)]}
 {40\delta\,h_Qh_E^2(1-h_E)}<.801,\qquad \delta=.017 .
\]
For narrow \(\mathcal B\), the exact \(B'\) is negative and has magnitude \(<2.1\) as in the preceding note. The actual corrected positive weight is therefore at most \( (2.1+1/3)W_s(q)(-C)_+\), so use the coefficient relative to \(1/3\), namely \(7.3\). Retain the genuine narrower \(s\) and \(a\) bands here (not just the \(b_2,b_3\) bands). Write \(J_s^\flat,h_a^\flat,B_2^\flat,B_3^\flat\) for their narrower harmonic weights or intervals. Since \(W(t)=(1-t)(1-2t)^2\) decreases on the \(s\)-bands,
\[
 R_{\rm narrow}\le
 \frac{7.3\,(J_s^\flat/J_s)\,(h_a^\flat/h_a)\,
       h_{B_2^\flat}h_{B_3^\flat}
       [I_2+\sum_{k=4}^{12}c_k(.055)H_k(.055)]}
 {40\delta\,h_Qh_E^2(1-h_E)}<.141 .
\]
The checker uses \(J_s^\flat/J_s\le W(.1384)h_s^\flat/[W(.139)h_s]\) and positive atanh-series rational enclosures for every logarithm. The two certified upper values are below \(.799905\) and \(.140376\), respectively. These are fixed-target charges on the original exact-one correction and the original narrow physical ledger, not average bounds for the defect or lower bounds on prime-pair counts.
