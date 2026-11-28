# Restriction and incidence moments for ternary projective weights

## 1. Statement

For \(m\ge0\) write \(P_m=(3^{m+1}-1)/2\), with \(P_{-1}=0\). For a linear code \(C\) and \(0\le r\le\dim C\), let \(d_r(C)\) be the least size of the union of supports of an \(r\)-dimensional subcode (with \(d_0=0\)). Write \(C_d(m)=\mathrm{PRM}_3(d,m)\) for the code evaluating homogeneous degree-\(d\) forms on projective representatives with first nonzero entry 1, and \(R_e(m)=\mathrm{RM}_3(e,m)\) for the code evaluating affine polynomials of total degree at most \(e\). Use \(C_e(m)=0\) if \(e\le0\) **only** in the recurrence for a subcode supported inside a hyperplane.

For every positive \(d\) and every \(1\le r\le k_d(4)=\dim C_d(4)\),
\[
 d_r(C_d(4))=\mathcal B_r(3,d,4)
\]
where \(\mathcal B\) is San-José's 2026 Theorem 6.7 upper bound. In particular \(d_{11}(C_3(4))=77\) and \(d_{31}(C_6(4))=45\). The latter does not follow by Wei duality from the unaugmented degree-2 code, because degree 6 is a multiple of \(3-1\) and its dual is \(C_2(4)+\langle\mathbf1\rangle\).

### Formula for the complete tables

Let \(A(n,t)\) count the integers \(0\le i<n\) whose base-3 digit sum is at most \(t\); it is zero for \(t<0\). Set \(k_d(m)=\sum_{j=0}^{m} A(3^j,d-1)\) for \(d\ge1\). For \(n>0\), write its leading base-3 block as \(n=a3^s+b\), \(1\le a\le2\), \(0\le b<3^s\). With \(h_d(0)=0\) and \(h_d(n)=0\) for \(d\le0\), set
\[
 h_d(n)=
 \begin{cases}
  A(a3^s,d)+h_{d-2}(b), & b\le P_{s-1},\\
  \min\{A(n,d),\,k_d(s)+A(n-P_s,d-1)\}, & b>P_{s-1}.
 \end{cases}
\]
These are Corollary 3.3 of the 2024 recursive paper and Proposition 6.6 of the 2026 preprint in the ternary case (both cited in SOURCES). The claimed exact weights are therefore
\[
 \mathcal B_r(3,d,4)=121-\max\{0\le n\le121:h_d(n)\le k_d(4)-r\}.    \tag{1}
\]
All quantities here are integers, and the included calculator prints every entry. One checker uses this recursion; the independent one evaluates the actual two projective point constructions of the 2026 paper directly and computes their ranks over \(\mathbb F_3\).

## 2. Pointwise restriction bounds

The following are the terms of San-José's 2024 Theorem 5.5, applied to each hyperplane separately. Here is a proof of the embeddings and the relevant positive-exponent convention.

Consider an \(r\)-dimensional subcode \(D\subseteq C_d(m)\) with support \(S\) of size \(w\). Fix a hyperplane \(H\); put \(x=|S\cap H|\),
\[
 \alpha=\dim(D|_H),\qquad
 \gamma=\dim\ker(D\longrightarrow D|_{\operatorname{PG}(m,3)\setminus H}).
\]
The latter kernel consists of vectors supported inside \(H\). A projective change of coordinates carries \(H\) to \(X_0=0\), inducing a monomial equivalence (permutation and coordinate rescaling) on the evaluation code, so it does not affect dimensions or supports. On the chart \(X_0=1\) every degree-\(d\) form dehomogenizes as \(f+g\), with \(\deg f\le d-1\) and \(g\) homogeneous of degree \(d\); on \(H\) only \(g\) contributes. If a word vanishes on \(H\), then \(g\) vanishes as a function on the full affine space of \(m\) remaining coordinates, including its origin. This gives \(r-\alpha\) independent words in \(R_{d-1}(m)\) outside \(H\). The entire projection outside \(H\) has dimension \(r-\gamma\) and lies in \(R_d(m)\).

Conversely, if the word vanishes outside \(H\), the unique reductions of \(f\) and \(g\) modulo \(x_i^3-x_i\) sum to zero. The reduced \(g\) has no monomial of degree \(d\) and no constant monomial: for a positive exponent subtracting 2 to reduce it never cancels its variable, and every remaining total degree is positive, at most \(d-2\), and congruent to \(d\) modulo 2. Such a monomial may have any one of its positive exponents increased by an even amount to total degree \(d-2\) without changing its evaluation. Thus the inside-only kernel injects into \(C_{d-2}(m-1)\) on \(H\) (it is zero if \(d-2\le0\)). The whole restriction to \(H\) lies in \(C_d(m-1)\).

Use zero-indexed weight arrays
\[
 L_a=d_a(C_d(m-1)),\quad E_g=d_g(C_{d-2}(m-1)),\quad
 A_a=d_a(R_{d-1}(m)),\quad B_g=d_g(R_d(m)).
\]
Here \(A_a\) is an indexed affine *weight*, not the two-argument digit count \(A(n,t)\) in (1). The valid rank pairs are all \(0\le\gamma\le\alpha\le r\) for which the four indices \(\alpha,\gamma,r-\alpha,r-\gamma\) are in their corresponding arrays. In particular, considering *all* such pairs can only weaken the necessary conditions. For each hyperplane, there is such a pair with
\[
    \ell_{\alpha,\gamma}\le x\le w-u_{\alpha,\gamma},\qquad
   \ell_{\alpha,\gamma}=\max(L_\alpha,E_\gamma),\quad
   u_{\alpha,\gamma}=\max(A_{r-\alpha},B_{r-\gamma}).               \tag{2}
\]
Taking the minimum of \(\ell+u\) gives the previous recursive numerical bound. A first refinement applies the bound to a hyperplane minimizing \(x\), so \(x\le wP_{m-1}/P_m\) by the first identity (3) below. Thus
\[
 \widehat L_r=\min_{\alpha,\gamma}
           \max\left(\ell_{\alpha,\gamma}+u_{\alpha,\gamma},
                 \left\lceil \ell_{\alpha,\gamma}P_m/P_{m-1}\right\rceil\right)
                                                               \tag{2a}
\]
is also a lower bound. For fixed \(w\), let \(I(w)\) be the union of the integer intervals in (2). We retain the information that \(x\in I(w)\) for *every* hyperplane.

The affine inputs are Heijnen–Pellikaan Theorem 5.10 in its digit form: \(d_r(R_e(m))=3^m-z_r\), where \(z_r\) is the \(r\)-th integer in **decreasing** order in \([0,3^m)\) with base-3 digit sum at most \(e\). Equivalently complement every digit and use increasing order, then add one to the resulting integer. The indices here refer to all admissible digits including the zero exponent tuple.

## 3. Exact incidence certificates

The points and hyperplanes of \(\operatorname{PG}(m,3)\) each number \(P_m\). A point belongs to \(P_{m-1}\) hyperplanes, and a pair of distinct points belongs to \(P_{m-2}\). Indeed hyperplanes are nonzero dual vectors up to scaling, and vanishing at the specified point or at an independent pair imposes respectively one or two independent linear equations. Thus, writing \(x_H=|S\cap H|\), the incidence identities are
\[
 \sum_H x_H=wP_{m-1},\qquad
 \sum_H x_H^2=wP_{m-1}+w(w-1)P_{m-2}.                              \tag{3}
\]
When \(x_H\in[a,b]\), the elementary inequality \((x_H-a)(x_H-b)\le0\) gives \(\sum_H x_H^2\le(a+b)\sum_H x_H-abP_m\). We only apply it after deriving the interval from (2).

The small calculation in Section 4 gives the surviving tuples below. For each row, \(w\) is the direct 2024 lower bound and the upper bound is \(w+1\). The first two are already excluded by the minimum-intersection refinement (2a). The last two remain when (2a) is applied independently to their own layers; here we rule them out using the allowable interval on every hyperplane. A tuple is \((\alpha,\gamma,\ell_{\alpha,\gamma},w-u_{\alpha,\gamma})\); no other rank pair leaves a nonempty interval.

| \(m,d,r\) | \(w\) | All surviving tuples |
| --- | ---: | --- |
| \(3,4,1\) | 5 | \((1,0,2,2)\) |
| \(3,4,7\) | 15 | \((4,1,6,6),(5,1,6,6)\) |
| \(4,3,11\) | 76 | \((6,0,22,22),(8,0,25,25)\) |
| \(4,6,31\) | 44 | \((13,6,14,14),(14,8,17,17),(15,8,17,17),(15,9,18,18),(16,8,17,17),(16,9,18,18),(17,9,18,18)\) |

At \(m=3\), the tested weights would respectively give means \(5\cdot13/40=13/8\) and \(15\cdot13/40=39/8\), below the respective forced values 2 and 6. These entries are already known (minimum distance and the 2026 paper's software verification); the incidence calculation just supplies a derivation not using its subcode-enumeration software.

At \(m=4,d=3,r=11\), all \(x_H\le25\) would force \(\sum_H x_H\le25\cdot121=3025\), but \(76\cdot40=3040\). Thus \(w\ge77\). This is a direct alternate proof: the exact degree-5 hierarchy from (2a) also proves the degree-3 result by Wei duality, because \(3+5=8=4(3-1)\) and the degrees are odd.

At \(m=4,d=6,r=31\) all \(x_H\in\{14,17,18\}\subset[14,18]\) are forced when \(w=44\). Equation (3) gives
\[
 \sum x_H=1760,\qquad \sum x_H^2=1760+44\cdot43\cdot13=26356,
\]
but the interval gives \(32\cdot1760-14\cdot18\cdot121=25828\) as an upper bound for the second sum. This excludes \(w=44\), proving \(d_{31}=45\). The corresponding mean is \(160/11\); the obstruction is strict and purely integral.

## 4. Inputs, complete checking chain, and scope

The known \(m=2\) base arrays, without their leading zero, are:
\[
\begin{array}{c|l}
 d&\text{weights on }\operatorname{PG}(2,3)\\\hline
 1&(9,12,13)\\
 2&(6,8,9,11,12,13)\\
 3&(3,4,6,7,8,9,10,11,12,13)\\
 4&(2,3,\ldots,13)\\
 d\ge5&(1,2,\ldots,13).
\end{array}
\]
The first two are the \(d<q\) theorem (2026 v2 Theorem 1.2 or its Corollary 5.2); the next is Wei/Sørensen duality and the last two are the single-parity-check and full-code cases. For \(m=3,4\), the \(d=1,2\) exact arrays similarly come from stacking the affine \(R_{d-1}(j)\) weights for \(j=m,m-1,\ldots,0\), adding the sizes of preceding charts as offsets (2026 Corollary 5.2). When \(d>2(m-1)\) and \(d<2m\), the high degree is \(d=2m-1\) and the dual is \(C_1(m)\), so remove \(P_m+1-b\) from \(\{1,\ldots,P_m\}\) for each degree-1 generalized weight \(b\). At \(d=2m\) use \(d_r=r+1\), and at \(d>2m\) use \(d_r=r\). These are the boundary cases of the standard duality used in 2026 Corollary 4.2 and the paragraph following it.

For every remaining layer evaluate (1), the raw bound from (2), and the least-intersection refinement (2a) at all ranks. At \(m=3,d=3,4\), use the \(m=2\) inputs; for \(m=4,d=3,4,5,6\), use the now exact \(m=3\) arrays. The number of ranks and remaining gaps at each comparison stage is:

| \(m,d\) | Number of ranks | Raw lower-bound gaps \(r\) | Gaps after (2a) |
| --- | ---: | --- | --- |
| \(3,3\) | 20 | none | none |
| \(3,4\) | 29 | \(1,7\) | none |
| \(4,3\) | 35 | \(11\) | \(11\) |
| \(4,4\) | 60 | \(1,2,5,11,12,15,21,32,38\) | none |
| \(4,5\) | 86 | \(21\) | none |
| \(4,6\) | 105 | \(1,7,31,32\) | \(31\) |

At every rank not in the final column, (2a) equals the constructive upper. The two gaps in the final column are exactly one, so the excluded values in Section 3 complete them. This is a finite enumeration of integer rank pairs and opportunities for incidence, not an enumeration of subcodes. The two scripts independently evaluate the inputs and justify all numerical entries, including the exact tuples. High and low boundary layers are also checked against (1); checking the full-code layer at \(d=2m+1\) suffices for all higher \(d\), since in each higher-degree full code the evaluation map onto any subset is surjective. In particular both point configurations defining the upper bound then impose exactly \(n\) conditions.

In the idealized wiretap-II coding interpretation of these quantities, take the dealer word uniformly from an assigned coset of \(C^\perp\) and choose the coset uniformly. For revealed coordinates \(T\), the information about the coset in \(\log_2(3)\)-bit units is \(|T|-\dim(C^\perp|_T)=\dim(C\cap\mathbb F_3^T)\), where the latter subspace consists of words supported on \(T\). Thus fewer than \(d_r(C)\) coordinates always reveal less than \(r\) such units. This is the standard use of ordinary generalized Hamming weights; the result is not a computation of relative weights of arbitrary nested codes or a claim about a deployed system.
