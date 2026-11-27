# Coprime adjacent divisors with a nearly superincreasing prime sequence

**Scope.** This is a restricted result for the squarefree extremal question in [Erdős Problem 1100](https://www.erdosproblems.com/1100). It gives both a sharp exponential base in a specified regime and a structural obstruction to beating it. It does not determine the unrestricted extremal growth.

For a squarefree integer \(n\) with \(k\) prime factors, let \(\tau_\perp(n)\) count the consecutive coprime pairs in the increasing divisor list. Suppose that \(m=k-r\ge1\) of its prime factors can be listed as \(q_1,\ldots,q_m\) with
\[
q_j>\prod_{i<j}q_i .
\]
There is no restriction on the other \(r\) primes. With \(F_0=0,F_1=1\) and \(F_{j+2}=F_{j+1}+F_j\), we prove
\[
\boxed{\quad \tau_\perp(n)\le m+(3^r-1)F_{m+1}.\quad} \tag{1}
\]
For \(r=0\) there is equality. In particular, any family permitting \(r=o(k)\) has \(\limsup \tau_\perp(n)^{1/k}\le\varphi=(1+\sqrt5)/2\). This exponential base is attained already in the subclass permitting one exception. Quantitatively, to reach \(\tau_\perp(n)\ge(\varphi+\epsilon)^k\), the smallest number \(r\) of deleted primes that makes the rest satisfy the displayed product condition must obey
\[
r\ \ge\ \frac{\log(1+\epsilon/\varphi)}{\log(3/\varphi)}\,k-O_\epsilon(1).
\]
Indeed, \(F_{m+1}\le\varphi^m\), so (1) bounds the count by \(k+\varphi^k(3/\varphi)^r\); for large \(k\) the additive \(k\) is at most half of the putative lower bound.

## Two translates of a superincreasing subset-sum list

A list \(w_1,\ldots,w_m>0\) is called superincreasing here when \(w_j>\sum_{i<j}w_i\). Let \(A_j\) be the subset sums of its first \(j\) entries, with each sum labeled by its original subset; write \(S_j=\sum_{i\le j}w_i\). For a positive shift \(t\) for which the two colored lists \(A_j,A_j+t\) have no ties, write \(D_j(t)\) for the number of adjacent pairs in their merged sorted list that have opposite colors and disjoint **original** labels. Translation does not add a coordinate to a label. We prove uniformly that
\[
D_j(t)\le 2F_{j+1}\qquad(j\ge1). \tag{2}
\]

For the fixed initial prefixes, define \(P_j=\sup_{t>0}D_j(t)\), and define
\[
Q_j=\sup_{\substack{a,b>0\\ a+b>S_j}}\big(D_j(a)+D_j(b)\big),
\]
taking only shifts with no ties at the indicated level. We have \(P_0=1,Q_0=2\). Fix \(j\ge1\), and abbreviate \(w=w_j>S=S_{j-1}\). The four groups of the merge are
\[
A_{j-1},\quad w+A_{j-1},\quad t+A_{j-1},\quad t+w+A_{j-1}.
\]
The second and fourth groups contain coordinate \(j\), so no pair joining them has disjoint labels. The first and fourth groups cannot be adjacent to each other, because the unshifted value \(w\) lies strictly between any such endpoints. Thus there are only two possible types:
- A pair joining the second and third groups contributes to a merge with count at most \(D_{j-1}(|w-t|)\). Deleting the other groups preserves adjacency and dropping coordinate \(j\), which occurs on exactly one side, preserves label disjointness.
- A pair joining the first and third groups contributes at most \(D_{j-1}(t)\). If \(t>w\), there is no such pair because \(w\) separates the two groups; if \(S<t<w\), there is at most one such pair because the two lists lie in disjoint intervals.

The shifts just used are admissible at level \(j-1\): any cross tie there would be a tie between the corresponding groups in the original merge. Also \(t=w\) itself is inadmissible. When \(t\le S\) the two arguments \(t,w-t\) sum to \(w>S\). This proves
\[
P_j\le\max\{Q_{j-1},1+P_{j-1}\}. \tag{3}
\]
For \(Q_j\), if \(a,b>S\), the two case bounds together give at most \(2+2P_{j-1}\). If, say, \(a\le S\), the condition \(a+b>w+S\) forces \(b>w\), and the case bounds give at most
\[
D_{j-1}(a)+D_{j-1}(w-a)+D_{j-1}(b-w).
\]
Here \(a+(b-w)>S\). Group the two arguments on either side of \(D_{j-1}(w-a)\) to conclude
\[
Q_j\le\max\{2+2P_{j-1},Q_{j-1}+P_{j-1}\}. \tag{4}
\]
The possibility that both \(a,b\le S\) is excluded by \(w>S\).

Equations (3)–(4) give \(P_1\le2\), \(Q_1\le4\). Inductively \(P_j\le2F_{j+1}\) and \(Q_j\le2F_{j+2}\): for \(j\ge2\), use \(1+2F_j\le2F_{j+1}\), \(2+4F_j\le2F_{j+2}\) (as \(F_{j+2}=2F_j+F_{j-1}\)), and \(2F_{j+1}+2F_j=2F_{j+2}\). This proves (2).

## Divisors and the exceptional coordinates

Take logarithms of the prime factors. Unique factorization makes all full subset sums distinct, and two divisors are coprime exactly when their labels are disjoint. Fixing a subset \(B\) of the exceptional coordinates gives one translate of the superincreasing list \(A_m\).

For a coprime adjacency within one translate, necessarily \(B=\varnothing\). The base list has exactly \(m\) disjoint adjacencies: its order is that of the binary ranks \(0,\ldots,2^m-1\), because the largest coordinate on which two labels differ dominates the lower coordinates. The rank masks \(i,i+1\) are disjoint exactly when \(i+1\) is a power of two (the addition changes the trailing run of ones into zeros and leaves all higher bits unchanged). The full merge can only remove some of these adjacencies.

For a coprime adjacency between two different translates, their exceptional labels \(B,B'\) must be disjoint. There are \((3^r-1)/2\) unordered distinct disjoint pairs: each coordinate lies in the first, the second, or neither; the only ordered pair counted here with equal labels is the empty–empty pair. For any fixed two translates, deleting all the others preserves adjacency. Their positive relative shift is admissible by unique factorization. By (2), each pair of translates contributes at most \(2F_{m+1}\). Adding the two counts proves (1).

## Sharpness of the exponential base and prior work

[Chevyrev, Searles and Slinko, *Order* 30 (2013), Theorem 3(a) and its proof](https://www.pure.ed.ac.uk/ws/portalfiles/portal/153145907/Chevyrev2013_Article_OnTheNumberOfFacetsOfPolytopes.pdf) use a base on \(m\) coordinates with weights \(2,4,\ldots,2^m\) together with one odd weight to obtain \(F_{m+2}\) flippable pairs in dimension \(m+1\). Each such pair is disjoint and adjacent. For any fixed dimension, the strict full subset-sum order and the strict superincreasing inequalities survive sufficiently small perturbations. For each weight \(w_i\), Bertrand's postulate supplies a prime between \(\lceil e^{T w_i}\rceil\) and \(2\lceil e^{T w_i}\rceil\); for large \(T\) these primes are distinct and their normalized logarithms approach the chosen weights. Thus the same count holds as a lower bound for squarefree examples with at most one exceptional prime, proving sharpness in exponential scale. Neither that construction nor the weight-to-prime realization is claimed here as new.

The unrestricted upper exponential base \(3\cdot 2^{-2/3}\) is in [Erdős and Tenenbaum, *J. Number Theory* 31 (1989), Théorème 1](https://tenenb.perso.math.cnrs.fr/PPP/div-consec.pdf); [Ross's squarefree note](https://zenodo.org/records/20767146) gives another bound on that exponential scale. Formula (1) does not improve the unrestricted base. It limits every construction whose prime sequence becomes superincreasing after deleting a sublinear number of terms, not just perturbations of one particular dyadic construction. The generic two-translate bound accounts for arbitrary positive exceptional weights.

A finite integer-weight check, [verify_factor_erdos1100_superincreasing_merge.js](verify_factor_erdos1100_superincreasing_merge.js), checks the merge inequalities on small configurations. The argument above applies to real weights without a discretization assumption.
