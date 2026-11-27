# The monopole–dipole smoothing cutoff for a dyadic module kernel

A dyadic module kernel can be surjective at the defining row yet have a strongly noncubic dual geometry. For a nearest-neighbor family the dual theta mass has an exact logarithmic cutoff: the leading population consists of single coordinates for one range of the coupling, adjacent opposite charges for the other range, and **both** in a \(1/\log d\) transition window. The finite-dimensional shortest shell alone can miss a factor of two at the tie.

**Scope and comparison.** [Albrecht–Felderhoff–Lai–Lapiha–Woo](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf) and [Düzlü–Gargava–Tairi](https://opencryptology.org/2026/2180) need small Gaussian mass of dual module kernels in positive lattice-Gaussian regularity theorems. Their general/random sufficient bounds do not give the exact dual theta profile for this deterministic one-row family. The inverse matrix uses the geometric-correlation structure studied for other boundary conditions by [Kac–Murdock–Szegő and subsequent work](https://www.egormaximenko.com/toeplitz/inverses_of_positive_tridiagonal_Toeplitz_matrices.pdf). The new calculation below is an integer-energy classification and a finite-width theta cutoff for an antiperiodic dual kernel, not a new matrix inversion theorem. This is an abstract Gaussian mass calculation, with no preimage method, concrete scheme assessment, or cryptanalytic claim.

## 1. Model and result

Let \(d\to\infty\) be even; in the dyadic examples \(d\) runs over powers of two. On \(\mathbb R^d\) let \(P\) shift \(e_j\) to \(e_{j+1}\) for \(0\le j<d-1\) and send \(e_{d-1}\) to \(-e_0\). Thus \(P^d=-I\). Fix \(a>2b>0\) and write
\[
 G=aI+b(P+P^{-1}),\quad
 \rho=\frac{a-\sqrt{a^2-4b^2}}{2b}\in(0,1),\quad
 \kappa=(a^2-4b^2)^{-1/2}.
\]
For the lattice with Gram matrix \(G\), the dual Gram matrix is, by a diagonal sign change, \(\kappa K_{d,\rho}\), where
\[
 (K_{d,\rho})_{ij}=\sum_{h\in\mathbb Z}(-1)^h\rho^{|i-j+hd|},\qquad
 Q_{d,\rho}(x)=x^{\mathsf T}K_{d,\rho}x .
\]
The sign change is integral and unimodular, hence does not affect theta mass. Write
\[
 \Theta_d(t,\rho)=\sum_{x\in\mathbb Z^d}e^{-tQ_{d,\rho}(x)},\qquad
 m_\rho=\min(1,2(1-\rho)).
\]
When the dyadic canonical metric carries an additional factor \(d\) in the primal Gram matrix, replace \(\kappa\) by \(\kappa/d\) for the dual.

**The two-species profile.** Uniformly for \(\rho=\rho_d\) in any fixed compact subinterval of \((0,1)\) and \(t=(\log d+O(1))/m_\rho\), one has
\[
 \log\Theta_d(t,\rho)
   =2d\left(e^{-t}+e^{-2(1-\rho)t}\right)+o(1). \tag{1}
\]
Under the normalized lattice weight in \(\Theta_d(t,\rho)\), with probability \(1-o(1)\) all nonzero coordinates split into widely separated objects of just two kinds: a single \(\pm1\), or two cyclically adjacent \(\pm1\) coordinates which are opposite in an antiperiodically unfolded interval. If each term \(2d e^{-t}\), \(2d e^{-2(1-\rho)t}\) has a limit, the two object counts converge jointly to **independent** Poisson variables with these means.

For fixed \(\rho\ne1/2\), \(t=(\log d+c)/m_\rho\) gives limit \(\exp(2e^{-c})\) for \(\Theta_d\); the first species is active below \(1/2\) and the second above \(1/2\). At fixed \(\rho=1/2\), the limit at \(t=\log d+c\) is \(\exp(4e^{-c})\). More generally if \((\rho_d-1/2)\log d\to\xi\) and \(t=\log d+c\), then
\[
 \Theta_d(t,\rho_d)\ \longrightarrow\
             \exp\!\left(2e^{-c}(1+e^{2\xi})\right). \tag{2}
\]
For the usual smoothing parameter at a fixed \(0<\varepsilon<1\), the dual nonzero mass requirement is \(\Theta_d(\pi s^2\kappa,\rho)-1\le\varepsilon\), with the actual dual factor \(\kappa\) for the chosen metric. Thus for fixed \(\rho\ne1/2\),
\[
 \pi\kappa\,\eta_\varepsilon^2
 =\frac{\log d+\log(2/\log(1+\varepsilon))+o(1)}{m_\rho}. \tag{3}
\]
At \(\rho=1/2\) replace \(2\) by \(4\); in the scaling of (2) replace \(2\) by \(2(1+e^{2\xi})\) and the denominator by \(1\). These follow by bracketing the strictly monotone theta mass with two fixed offsets and then letting their gap tend to zero.

**A dyadic example.** In \(R_d=\mathbb Z[Y]/(Y^d+1)\), consider the abstract row \((-\nu(1+Y),1)\) with \(\nu\) a fixed positive integer. It is surjective and its kernel is the graph \(\{(x,\nu(1+Y)x):x\in R_d\}\). Its Gram in coefficient norm is \(G=(1+2\nu^2)I+\nu^2(P+P^{-1})\), and in canonical norm it is \(dG\). The value \(\nu=1\) gives \(\rho<1/2\), while \(\nu=2\) gives \(\rho>1/2\). The split is therefore present in genuine dyadic module kernels, not only in matrices with a chosen correlation parameter.

## 2. Integer energy on the infinite line

The matrix inverse follows from
\[
 G=(b/\rho)(I+\rho P)(I+\rho P^{-1}).
\]
Expand the two inverse factors in geometric series, giving \(G^{-1}=\kappa\sum_{j\in\mathbb Z}(-\rho)^{|j|}P^j\). Because \(d\) is even, conjugating by \(\operatorname{diag}((-1)^j)\) changes \(P\) to \(-P\). The sum then has coefficients \(\rho^{|j|}\) and the entries stated above, by \(P^d=-I\).

For a finitely supported integer sequence \(x\) on \(\mathbb Z\), set
\[
 Q_\rho(x)=\sum_{i,j}x_i x_j\rho^{|i-j|}.
\]
Both \(Q_\rho\) and \(Q_{d,\rho}\) satisfy the spectral lower bound
\[
 Q(x)\ge\gamma_\rho\sum_i x_i^2,\qquad \gamma_\rho=(1-\rho)/(1+\rho). \tag{4}
\]
For the line this is Fourier integration against \((1-\rho^2)/(1-2\rho\cos\theta+\rho^2)\); for the antiperiodic cycle take the values of the same symbol at eigenangles of \(P\).

The essential integrality argument is the decomposition into interval sums:
\[
 Q_\rho(x)= (1-\rho)^2\sum_{l\ge1}\rho^{l-1}
             \sum_{j\in\mathbb Z}\left(\sum_{i=j}^{j+l-1}x_i\right)^2. \tag{5}
\]
For fixed \(i,i'\) exactly \(l-|i-i'|\) intervals of length \(l>|i-i'|\) contain both indices; summing this geometric series proves the identity. The squared interval sums are integers.

If \(S=\sum_i x_i\ne0\), summing all interval sums of length \(l\) gives \(lS\). Hence their squared sum is at least \(l|S|\ge l\), since an integer square is at least its absolute value. A singleton \(\pm e_i\) attains equality for all \(l\) and has energy \(1\). Every other sequence in this case has \(\sum_i x_i^2\ge2\), giving a gap of at least \((1-\rho)^2\) above \(1\) already from \(l=1\).

If \(S=0\) and \(x\ne0\), at each \(l\) the sequence of interval sums is nonzero (convolution of two nonzero finitely supported integer sequences), integral and sums to zero. Its squared sum is at least \(2\). The adjacent dipole \(\pm(e_i-e_{i+1})\) attains equality for all \(l\) and has energy \(2(1-\rho)\). A sequence with \(\|x\|_2^2>2\) has a positive gap already from \(l=1\). The only other possibility with \(\|x\|_2^2=2\) is a nonadjacent opposite pair, for which the squared length-two interval sum is \(4\), giving a gap of \(2\rho(1-\rho)^2\). Consequently every nonzero sequence outside the two identified species has energy at least
\[
 m_\rho+\delta,\qquad
 \delta=\min(1,2\rho_-)(1-\rho_+)^2>0
 \quad\hbox{for }\rho\in[\rho_-,\rho_+]\subset(0,1). \tag{6}
\]
Only the lower bound for sequences outside both species is needed near the transition.

## 3. Unfolding sparse supports

Let \(R=\lceil(\log d)^2\rceil\), and suppose \(d\) is large enough that \(R<d/4\). Order the support positions of a nonzero \(x\) cyclically. If all successive cyclic gaps are \(\le R\), the support size is at least \(d/R\). Otherwise cut the cycle at every gap greater than \(R\), obtaining clusters with successive internal gaps at most \(R\). A single-site support has one cyclic gap of length \(d\), so it is included in this case. For each cluster \(C\), unfold its interval starting at the support position just after a cut. Its vector \(x_C\) carries the antiperiodic sign when the coordinate origin is crossed.

In this decomposition the difference between the cycle energy and the line energies satisfies
\[
 \left|Q_{d,\rho}(x)-\sum_C Q_\rho(x_C)\right|
 \le C_0\rho_+^{R}\|x\|^2
 \le \epsilon_R\sum_C Q_\rho(x_C),\qquad
 \epsilon_R=O_{\rho_+}(\rho_+^R). \tag{7}
\]
To check the row-sum estimate, extend the list of support positions to all their integer lifts spaced by \(d\). For a given support coordinate in its cluster interval, the retained representatives of positions in that same interval contribute precisely its line form, with signs accounted for by antiperiodicity. Every other lift with nonzero coefficient lies at distance greater than \(R\) from that coordinate: between clusters one crosses a cut, and the other representatives of the same cluster are also separated by at least one cut. The tail of the absolute row sum is bounded by \(2\sum_{j>R}\rho_+^j\), since each integer lift has at most one original support coordinate. Symmetry, or \(2|x_i x_j|\le x_i^2+x_j^2\), gives the first inequality. Equation (4) gives the second. At the cutoff \(t\epsilon_R=o(1)\).

Vectors with no large gap have negligible total Gibbs weight. With \(\gamma_*=(1-\rho_+)/(1+\rho_+)\), the one-coordinate nonzero sum \(A_t=2\sum_{j\ge1}\exp(-t\gamma_* j^2)=O(\exp(-t\gamma_*))\). By (4) their weight is at most
\[
 \sum_{s\ge d/R}\binom ds A_t^s
 \ \le\ \sum_{s\ge d/R}(e R A_t)^s=o(1).
\]
Indeed \(t\ge\log d-O(1)\) uniformly since \(m_\rho\le1\).

## 4. Dilute cluster sum

For an upper bound use (7) with \(\tilde t=t(1-\epsilon_R)\). A candidate cluster of support size \(s\ge1\) is described by a starting index, at most \(R^{s-1}\) patterns of internal positive gaps, and its nonzero integer coefficients in its sign-unfolded interval; retain only intervals of span less than \(d\). Bound its activity by \(e^{-\tilde t Q_\rho(x_C)}\). The sum of all candidate activities other than the two primitive species is \(o(1)\):
* Choose fixed \(s_0\) with \(\gamma_*s_0>2\). By (4), the sum at \(s\ge s_0\) is bounded by \(d\sum_{s\ge s_0} R^{s-1}A_{\tilde t}^s=o(1)\). In this estimate \(A_{\tilde t}\) uses the same \(\gamma_*\) as above.
* If \(s<s_0\), contributions with at least one coefficient of magnitude \(B_0\) or greater are similarly \(o(1)\) on choosing a fixed \(B_0\) with \(\gamma_*B_0^2>2\). Use a union over the at most \(s_0-1\) large-coordinate positions, its weight sum \(O(e^{-\tilde t\gamma_* B_0^2})\), and the remaining one-coordinate weights.
* The rest contain \(O(dR^{s_0-1})\) descriptions, where the hidden constant is fixed. Every nonprimitive example costs at least \(m_\rho+\delta\) by (6), giving total \(O(dR^{s_0-1}e^{-\tilde t(m_\rho+\delta)})=o(1)\).

The two primitive species each have exactly \(2d\) descriptions, accounting for translation and sign (the wrap interval has the sign determined by the same unfolding convention). Their activities sum to \(2d(e^{-t}+e^{-2(1-\rho)t})+o(1)\); replacing \(\tilde t\) by \(t\) costs \(o(1)\), as \(t\epsilon_R=o(1)\) and the sum is bounded. A vector having a cut corresponds to a compatible **set** of distinct candidate clusters. Dropping all incompatibility restrictions for the upper bound gives the product over candidates of \(1+\mathrm{activity}\), bounded by the exponential of the sum of activities. Countably many integer coefficient choices are allowed; the activity sum estimate justifies the product. Vectors without cuts add \(o(1)\). This proves the upper bound in (1).

For the lower bound fix an integer \(k\ge0\) and keep only vectors made of \(k\) primitive clusters, separated by gaps greater than \(R\). In ordered cluster choices, forbidden pairs affect \(O_k(Rd^{k-1})\) descriptions (each species has span at most one), whose total weight is \(o(1)\) because every primitive activity is \(O(1/d)\). Divide by \(k!\); a compatible ordered list gives its vector uniquely up to permuting the list, since cluster decomposition is unique. The energy error in (7), using \(t(1+\epsilon_R)\) for a lower bound, is negligible for fixed \(k\). The resulting weight sum is the \(k\)-th exponential term for the sum of primitive activities, up to \(o(1)\). Summing through any fixed \(k\) and then increasing the cutoff proves the matching lower bound because the activities remain bounded; the exponential series tails are uniform on bounded intervals. This proves (1). Keeping the two species counts separately gives the same argument with factors \(1/(k_1!k_2!)\), and normalization by (1) proves the independent Poisson limit. Contributions containing any nonprimitive cluster are \(o(1)\) (their total activity is \(o(1)\) times a bounded exponential), as are the vectors without a cut. These estimates identify the two species for the normalized law as claimed.

## 5. Why the exact finite shortest shell is not enough

In the antiperiodic cycle the single-coordinate energy and the unfolded adjacent dipole energy are exactly
\[
 E_{\rm single}=\frac{1-\rho^d}{1+\rho^d},\qquad
 E_{\rm dipole}=\frac{2(1-\rho)(1+\rho^{d-1})}{1+\rho^d}.
\]
They follow by summing the entries at displacement zero and one. In fact for **every even \(d\ge4\) and \(0<\rho<1\)** these two species exhaust the possible shortest vectors, with exact ties included.

First \(E_{\rm dipole}/\gamma_\rho<4\) for \(d>1\): after canceling \(1-\rho\), the difference between \(2(1+\rho^d)\) and \((1+\rho)(1+\rho^{d-1})\) is \((1-\rho)(1-\rho^{d-1})>0\). Thus any shortest vector has squared coefficient norm at most three by (4). Its nonzero entries are each \(\pm1\). For two support positions the best pair uses the largest absolute off-diagonal correlation. Write
\[
 A(r)=\frac{\rho^r-\rho^{d-r}}{1+\rho^d},\quad 1\le r\le d-1 .
\]
It strictly decreases with \(r\), and \(A(d-r)=-A(r)\); hence the largest absolute value occurs at cyclic distance one with the sign giving the unfolded dipole.

For three positions, let their cyclic gaps be \(a,b,c\ge1\) with \(a+b+c=d\). The off-diagonal expression, divided by two, has the form \(uA(a)+vA(b)+wA(c)\), where \(u,v,w\in\{\pm1\}\) and \(uvw=-1\). To see the twist, the sign for the first-to-last pair includes \(A(a+b)=-A(c)\). If all gaps are at most \(d/2\), the minimum over signs takes all three signs negative. If one gap exceeds \(d/2\), its correlation is negative but has the smallest absolute magnitude, since the sum of the other two gaps is \(d\) minus that largest gap. The unconstrained minimizers of the three terms would have sign product \(+1\), so at least one term must give up its individual minimum; paying this loss on the smallest magnitude again gives all three signs negative.

The sum \(A(a)+A(b)+A(c)\) is maximized at a permutation of \((1,1,d-2)\). Indeed write \(u_0=\rho^a,v_0=\rho^b,w_0=\rho^c\). Its numerator is
\[
 u_0+v_0+w_0-u_0v_0-u_0w_0-v_0w_0.
\]
At fixed \(c,a+b\) this increases with \(u_0+v_0\), whose strict convexity in the lengths allows replacing \(a,b\) by \(1,a+b-1\) whenever both exceed one. Repeating with another pair if necessary gives the indicated boundary gaps. Thus the minimum energy of three support positions is \(3E_{\rm single}-4A(1)+2A(2)\). Its difference from \(E_{\rm dipole}\), multiplied by \(1+\rho^d\), is
\[
 1-2\rho+2\rho^2-\rho^{d-2}(\rho^2-2\rho+2)
 \ \ge\ 1-2\rho+2\rho^3-\rho^4
 = (1-\rho)^3(1+\rho)>0 .
\]
This rules out the final candidate support size.

The sign of \(E_{\rm dipole}-E_{\rm single}\) equals the sign of
\[
 h_d(\rho)=1-2\rho+(2-\rho)\rho^{d-1}.
\]
For \(d=4\) this is \((1-\rho)^3(1+\rho)>0\). For \(d>4\), it is strictly convex for \(0<\rho<1\), positive at \(1/2\), zero at \(1\) with derivative \(d-4>0\), and hence has exactly one root \(\rho_d^\circ\in(1/2,1)\). The singleton wins below it and the dipole above, with both at the root. For large \(d\), evaluating \(h_d\) at \(1/2+2^{-(d-1)}\) is negative (after division by \(2^{-(d-1)}\) the limit is \(-2+3/2\)). The root equation then gives
\[
 \rho_d^\circ-\tfrac12=\tfrac34\,2^{-(d-1)}(1+o(1)).
\]
In particular at exactly \(\rho=1/2\) the finite shortest shell consists only of singletons, but its gap to the dipoles tends exponentially to zero. The \(t\asymp\log d\) calibration cannot separate those energies, so the dipoles contribute a second intensity in (1) even though they are not in the exact shortest shell.

**Replay.** Run `python3 verify-dyadic-dipole-cutoff.py` for exact rational checks of the antiperiodic inverse, the interval decomposition, finite shell classification and illustrative isolated-cluster counts. The asymptotic bounds are proved above. The code uses small artificial matrices and requires only Python's standard library.
