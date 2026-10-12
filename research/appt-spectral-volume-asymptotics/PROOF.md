# Sharp spectral-volume asymptotics and a common limit shape

**Written analytic proof; not Lean-formalized.** The measure is flat Lebesgue measure on the eigenvalue probability simplex, not Hilbert–Schmidt or Bures measure on density matrices. The smaller local dimension is fixed. This note does not solve the unrestricted maximal-purity conjecture or prove APPT equals absolute separability.

## 1. Statements and scope

Fix an integer m>=2, let n>=m and D=mn, and set

\[
R=\frac{m(m-1)}2,\quad S=\frac{m(m+1)}2,\quad
\alpha=\frac{m-1}2,\quad\beta=\frac{m+1}2=\alpha+1.
\]

A density matrix is APPT if partial transpose remains positive after every global unitary conjugation. It is absolutely separable (AS) if every conjugate is separable. Define V_E as the volume of the corresponding spectra divided by the volume of the probability simplex. Permutation invariance gives the same ratio on its nonincreasing ordered section. There is no Vandermonde weight.

Put

\[
q_m=\frac{\alpha^\alpha}{\beta^\beta},\qquad
C_m=\frac{\sqrt{2\pi}\,m^{m^2-1}\alpha^{R+1/2}\beta^{S-1/2}}{R!(S-1)!}.
\]

**Theorem 1.** For each fixed m>=2, as n tends to infinity,

\[
\boxed{V_{\rm APPT}(m,n)=C_m\sqrt D\,q_m^D(1+O_m(D^{-1})).}
\tag{1}
\]

In particular,

\[
V_{\rm APPT}(2,n)\sim\frac{9\sqrt{3\pi}}2\sqrt n(4/27)^n,\qquad
V_{\rm APPT}(3,n)\sim\frac{2916\sqrt{3\pi}}5\sqrt n\,64^{-n}.
\tag{2}
\]

An explicit finite-dimensional sandwich underlies (1). Define

\[
W_{m,D}=\frac{m^{m^2-1}\Gamma(D)\Gamma(\alpha D+R+1)}
{(D+m)^R(D-m)^{S-1}R!(S-1)!\Gamma(\beta D-S+1)}.
\tag{3}
\]

For K=m^2-2 and c=2m(m+1), put

\[
E_{m,D}=\frac{576m^2}{D+1}
+\frac{144c^2K(K+1)}{D(D+1)}+\frac{6c^2K(K+1)}D.
\tag{4}
\]

For D>=12m(S-1), as well as D=mn and n>=m,

\[
(1-E_{m,D})W_{m,D}\leq V_{\rm APPT}(m,n)\leq W_{m,D}.
\tag{5}
\]

The lower bound may be negative for moderate D; its constants are not optimized.

**Theorem 2.** Using [KBNKB, Supplemental Lemma 2],

\[
V_{\rm AS}(m,n)=\Theta_m(\sqrt D\,q_m^D).
\tag{6}
\]

For either APPT or AS, sample the spectrum uniformly under this flat measure and order its entries. Let

\[
L=\log(\beta/\alpha),\quad a=\alpha L,\quad b=\beta L,\quad
Q_m(s)=a+\log\frac\beta{\alpha+s}\quad(0\leq s\leq1).
\]

Then

\[
\boxed{\max_{1\leq i\leq D}|D\lambda_i-Q_m(i/D)|\longrightarrow0
\quad\text{in probability}.}
\tag{7}
\]

Thus the scaled empirical eigenvalues have limiting density

\[
f_m(x)=\beta e^{a-x}\mathbf1_{[a,b]}(x),
\tag{8}
\]

and typical scaled purity satisfies

\[
D\operatorname{Tr}(\rho^2)\longrightarrow2-\alpha\beta[\log(\beta/\alpha)]^2.
\tag{9}
\]

The scaled minimum and maximum converge to a and b, respectively, and the extreme-eigenvalue ratio tends to (m+1)/(m-1). These are typical-spectrum conclusions, not maximum-purity bounds.

**Corollary 3.** For the inner polytope of [AKW, Proposition 6.14],

\[
\frac{V_{\rm APPT}}{V_{\mathcal P}}\longrightarrow
\frac{m^{m^2-1}\alpha^{R-m+1}\beta^{S-m}(m-1)!m!}
{4^{m-1}R!(S-1)!}.
\tag{10}
\]

The limit is 3 for m=2 and 2187/40 for m=3.

**Attribution.** Hildebrand's spectral method and the permutation-invariant APPT formulation of [AKW] are established inputs. Section 6.3 of [AKW] gives the exact inner-polytope volume and numerical comparisons for m=2,3,4; its stated theorem gives a lower bound, with a constant-factor comparison discussed numerically. [Tran] proves qubit volume order Theta(sqrt(n)(4/27)^n) using explicit inner and outer bounds. Here the new argument is asymptotically full volume in an explicit containing affine simplex, its general leading coefficient, and the conditional limit shape. The AS criterion is credited to [KBNKB]. No exhaustive historical-priority or peer-review claim is made.

## 2. Physical tests and a uniform Schur bound

For a unit vector with Schmidt coefficients s_i>=0 and sum s_i^2=1, the partially transposed rank-one projector has eigenvalues

\[
s_i^2\ (1\leq i\leq m),\qquad\pm s_i s_j\ (i<j),\qquad D-m^2\text{ zeros}.
\tag{11}
\]

This follows by transposing matrix units; the off-diagonal two-dimensional blocks have symmetric and antisymmetric eigenvectors. Partial transpose is self-adjoint for the trace pairing:

\[
\langle\psi,(U\rho U^*)^\Gamma\psi\rangle
=\operatorname{Tr}(U\rho U^*(|\psi\rangle\langle\psi|)^\Gamma).
\tag{12}
\]

The minimum over the unitary orbit is the oppositely ordered eigenvalue pairing: squared absolute unitary entries form a doubly stochastic matrix, rearrangement gives the bound, and a permutation unitary attains it.

For sorted nonnegative lambda define

\[
h(\lambda)=\sum_{j=D-S+1}^D\lambda_j-\sum_{j=1}^R\lambda_j.
\tag{13}
\]

Taking all Schmidt coefficients equal in (11) proves APPT implies h>=0.

Assign the largest R eigenvalues to slots a_ij for i<j, and the smallest S to slots b_ij for i<=j, in arbitrary orders. Form the real symmetric matrix

\[
(L_{a,b})_{ii}=2b_{ii},\qquad(L_{a,b})_{ij}=b_{ij}-a_{ij}\quad(i<j).
\tag{14}
\]

If all these matrices are PSD, lambda is APPT. Indeed, for strictly positive Schmidt coefficients the worst trace pairing puts the top R entries on negative terms and the bottom S on positive terms, with some slot assignments. Its value is s^T L_{a,b}s/2, while middle eigenvalues pair with zeros. Lower Schmidt ranks follow by continuity. Local Schmidt basis changes are absorbed into global unitaries. No numerical chamber enumeration is needed.

Write

\[
\bar a=R^{-1}\sum_{j=1}^R\lambda_j,\quad
\bar b=S^{-1}\sum_{j=D-S+1}^D\lambda_j,\quad g=\bar a+\bar b,
\]
\[
A=\lambda_1-\lambda_R,\quad B=\lambda_{D-S+1}-\lambda_D,\quad
\epsilon=(m-1)A+(m+1)B.
\]

For m=2, A=0. Let e=(1,...,1)/sqrt(m), J be the all-ones matrix, and
L_0=gI+(bar b-bar a)J. Every assignment satisfies

\[
e^TL_0e=2h/m,\quad L_0|_{e^\perp}=gI,\quad e^T(L_{a,b}-L_0)e=0.
\tag{15}
\]

The last equality is exact because the sums of the a- and b-slots do not change. Perturbation entries are bounded by 2B on the diagonal and A+B off it, so the symmetric operator norm is bounded by the maximum absolute row sum epsilon. The e-perpendicular block is therefore at least (g-epsilon)I, the coupling to e has norm at most epsilon, and the e,e entry remains exactly 2h/m. Completing the square gives the sufficient condition

\[
\boxed{\lambda_D\geq0,\quad g>\epsilon,\quad (2h/m)(g-\epsilon)\geq\epsilon^2
\quad\Longrightarrow\quad\lambda\text{ is APPT}.}
\tag{16}
\]

The same estimate controls every assignment at once.

## 3. The containing affine simplex

The ordered probability simplex has vertices u_k=(1/k,...,1/k,0,...,0). Its barycentric coordinates are

\[
x_k=k(\lambda_k-\lambda_{k+1})\ (k<D),\quad x_D=D\lambda_D,\quad\sum x_k=1.
\tag{17}
\]

Temporarily retain x_k>=0 for k<D while allowing x_D<0. This auxiliary affine region is not a space of density matrices. Direct counting in (13) gives

\[
h(u_k)=\begin{cases}-1&k\leq R,\\-R/k&R<k\leq D-S,\\(k-D+m)/k&D-S<k\leq D.\end{cases}
\tag{18}
\]

The middle range may be empty. The maximum is uniquely h(u_D)=m/D. Set c_k=(m/D)/(m/D-h(u_k)) for k<D. Explicitly,

\[
c_k=\begin{cases}
m/(D+m)&k\leq R,\\
k/(k+\alpha D)&R<k\leq D-S,\\
m(D-l)/[l(D-m)]&k=D-l,\ 1\leq l<S.
\end{cases}
\tag{19}
\]

These numbers are positive. The simplex

\[
T=\{x_k\geq0\ (k<D),\ \sum_{k<D}x_k/c_k\leq1\},\quad x_D=1-\sum_{k<D}x_k
\tag{20}
\]

contains all ordered APPT spectra. Its intersection with x_D>=0 is exactly the physical ordered linear relaxation h>=0.

Put x_k=c_k y_k for k<D and y_D=1-sum_{k<D}y_k. Then y ranges over the standard probability simplex, with constant affine Jacobian, and

\[
h(\lambda)=(m/D)y_D.
\tag{21}
\]

The volume of T divided by that of the ordered probability simplex is prod c_k. Indeed the affine map from barycentric coordinates to lambda has the same Jacobian in numerator and denominator. Multiplying (19),

\[
\frac{\operatorname{vol}(T)}{\operatorname{vol}(\Delta_D^\down)}
=\left(\frac m{D+m}\right)^R
 \prod_{k=R+1}^{D-S}\frac{k}{k+\alpha D}
 \prod_{l=1}^{S-1}\frac{m(D-l)}{l(D-m)}=W_{m,D}.
\tag{22}
\]

Cancellation gives precisely (3), including an empty middle product. All Gamma arguments are integers in product dimensions since alpha D=m(m-1)n/2 is integral.

## 4. Almost-full physical APPT volume inside T

Under uniform volume on T, y is Dirichlet(1,...,1) on D entries. Elementary simplex integration gives

\[
\mathbb Ey_i=1/D,\quad\mathbb Ey_i^2=2/[D(D+1)],\quad
\mathbb Ey_i y_j=1/[D(D+1)]\quad(i\ne j),
\tag{23}
\]

and

\[
\operatorname{Var}(\sum_i d_i y_i)
=\frac{D\sum_i d_i^2-(\sum_i d_i)^2}{D^2(D+1)}.
\tag{24}
\]

Also t=y_D has Beta(1,D-1) distribution independently of (y_1,...,y_{D-1})/(1-t), which is uniform Dirichlet on D-1 entries. This follows by the change-of-variables Jacobian (1-t)^{D-2}, not an asymptotic independence assumption.

Assume D>=12m(S-1), hence D>=2m. All c_k<=2m, and for k<=D-S one has c_k<=2/(m+1)<=2/3. Thus

\[
\mathbb Ex_D=1-D^{-1}\sum_{k<D}c_k\geq1/3-2m(S-1)/D\geq1/6.
\]

Taking d_k=c_k for k<D and d_D=0 in (24), Chebyshev gives

\[
\Pr_T(x_D<1/12)\leq576m^2/(D+1).
\tag{25}
\]

Let J={1,...,R-1} union {D-S+1,...,D-1}. It has K=m^2-2 entries, none equal to D, and its ranges are disjoint. Put Z=sum_{j in J}y_j. The endpoint gaps are exactly

\[
A=\frac m{D+m}\sum_{j=1}^{R-1}y_j/j,\quad
B=\frac m{D-m}\sum_{l=1}^{S-1}y_{D-l}/l.
\tag{26}
\]

It follows that epsilon<=cZ/D, c=2m(m+1). On the three simultaneous events

\[
x_D\geq1/12,\qquad Z\leq1/(12c),\qquad y_D\geq6c^2Z^2,
\tag{27}
\]

we have lambda_D>=1/(12D), g>=1/(6D), epsilon<=1/(12D), and therefore

\[
(2h/m)(g-\epsilon)\geq(2y_D/D)/(12D)
\geq c^2Z^2/D^2\geq\epsilon^2.
\]

Thus (16) proves physical APPT on their intersection.

The second moment E Z^2=K(K+1)/[D(D+1)] yields

\[
\Pr_T(Z>1/(12c))\leq144c^2K(K+1)/[D(D+1)].
\tag{28}
\]

For the last event write t=y_D and Z=(1-t)Z'. Then Z' is independent of t, with second moment K(K+1)/[(D-1)D]. The event t<6c^2(1-t)^2(Z')^2 implies t<6c^2(Z')^2. The beta CDF satisfies Pr(t<u)<=min(1,(D-1)u) for u>=0, by 1-(1-u)^{D-1}<=(D-1)u on [0,1]. Consequently

\[
\Pr_T(y_D<6c^2Z^2)\leq6c^2K(K+1)/D.
\tag{29}
\]

There is no incorrect independence assumption between Z and y_D. Applying the union bound to (25), (28), (29) proves

\[
1-E_{m,D}\leq\Pr_T(\lambda\text{ is APPT})\leq1.
\]

Multiplication by (22) gives (5). In particular the entire affine simplex and its physical linear relaxation both have volume asymptotic to APPT, although the relaxation is not a finite-dimensional equivalence criterion.

## 5. Leading constant and inner-polytope comparison

For fixed a>0 and fixed b, Stirling's formula gives

\[
\Gamma(aD+b)=\sqrt{2\pi}(aD)^{aD+b-1/2}e^{-aD}(1+O_{a,b}(D^{-1})).
\]

Apply it to the three Gamma factors in (3). The exponentials cancel because 1+alpha=beta. Their combined D-power is R+S-1/2=m^2-1/2; the two other powers in the denominator contribute D^{m^2-1}. The remaining exponential is q_m^D and the coefficient is exactly C_m. This proves W=C_m sqrt(D) q_m^D(1+O_m(1/D)); (5) then proves Theorem 1.

The exact inner-polytope formula [AKW, Eq. (64)] similarly gives

\[
V_{\mathcal P}=C_m^{\rm in}\sqrt D q_m^D(1+O_m(D^{-1})),\quad
C_m^{\rm in}=\frac{4^{m-1}\sqrt{2\pi}(\alpha\beta)^{m-1/2}}{(m-1)!m!}.
\tag{30}
\]

Its last Gamma quotient tends to Gamma(2)/Gamma(m+1)=1/m!; the other fixed factor is Gamma(m)=(m-1)!. Dividing the coefficients proves (10).

## 6. An absolutely separable constant-fraction subset

Let K={lambda_max<=(beta/alpha)lambda_min}. By [KBNKB, Supplemental Lemma 2] every state with such a spectrum is separable. The criterion is spectral, so it implies absolute separability and K subset AS subset APPT. This is an external established criterion, not a new assumption about AS=APPT.

Normalize independent mean-one exponential variables E_i by their sum; the result is uniform on the probability simplex. The Jacobian of E_i=t lambda_i is t^{D-1}. The ratio event is homogeneous. Integrating over the unique minimum gives the exact volume

\[
\begin{aligned}
V_K&=D\int_0^\infty e^{-Dx}(1-e^{-x/\alpha})^{D-1}\,dx\\
&=\alpha D B(\alpha D,D)
=\frac{\Gamma(\alpha D+1)\Gamma(D)}{\Gamma(\beta D)}.
\end{aligned}
\tag{31}
\]

Use u=e^{-x/alpha} for the beta integral. Stirling gives

\[
V_K=\sqrt{2\pi\alpha\beta}\sqrt D q_m^D(1+O_m(D^{-1})).
\tag{32}
\]

This lower bound and Theorem 1 prove (6). More precisely the lower and upper limits of V_AS/(sqrt(D)q_m^D) lie between sqrt(2 pi alpha beta) and C_m. The exact leading AS coefficient for m>=3 remains undetermined. In particular AS occupies a fraction bounded away from zero of T for each fixed m.

## 7. Conditional spectral limit shape

Under T, equations (17) and (19) give

\[
D\lambda_i=1+\sum_{j<D}d_{ij}y_j,\quad
 d_{ij}=c_j[(D/j)\mathbf1_{j\geq i}-1].
\tag{33}
\]

Uniformly in i,j, |d_ij|<=2m for all sufficiently large D. If j<i the bound follows from c_j<=2m. If j>=i, the three ranges in (19) give upper bounds m/j<=m, (D-j)/(j+alpha D)<=1/alpha<=2, and m/(D-m), respectively. Thus (24) yields

\[
\operatorname{Var}_T(D\lambda_i)\leq4m^2/(D+1).
\tag{34}
\]

The mean is

\[
\mathbb E_T(D\lambda_i)=1-D^{-1}\sum_{j<D}c_j+
                         \sum_{j=i}^{D-1}c_j/j.
\tag{35}
\]

Away from finitely many boundary indices, c_j=j/(j+alpha D) and c_j/j=1/(j+alpha D). Replacing boundary terms by these formulas changes (35) by O_m(1/D), uniformly in i: the first sum has a factor 1/D, and every boundary term in the second sum is itself O_m(1/D). Smooth Riemann-sum estimates therefore show uniformly that the mean differs by O_m(1/D) from

\[
1-\int_0^1\frac{s}{s+\alpha}\,ds+\int_{i/D}^1\frac{ds}{s+\alpha}
=\alpha\log(\beta/\alpha)+\log\frac\beta{\alpha+i/D}.
\tag{36}
\]

At a fixed finite grid of indices, (34)--(36) and Chebyshev imply convergence in probability. All spectra in T are ordered, even when their least coordinate is negative. Monotonicity between grid points and uniform continuity of Q_m give convergence uniformly over all indices: choose the grid for a fixed tolerance, then let D grow. The two endpoint indices are 1 and D and converge to Q_m(0) and Q_m(1). This proves (7) under T.

For APPT, its T-probability tends to one by (5). For AS, (32) and (22) give a positive lower limit for its T-probability. For any bad event B, Pr_T(B|E)<=Pr_T(B)/Pr_T(E), so the same uniform convergence holds after conditioning on either property. Equality of those two sets or their volumes is not needed.

The monotone change of variables s=beta exp(a-x)-alpha shows that Q_m(U) for U uniform on [0,1] has density (8). Its integral is beta-alpha=1, using exp(a-b)=alpha/beta. Its first moment is beta(a+1)-alpha(b+1)=1, and its second moment is

\[
\beta(a^2+2a+2)-\alpha(b^2+2b+2)=2-\alpha\beta L^2.
\tag{37}
\]

Uniform convergence (7) and Riemann summation imply convergence of the empirical measure and the second moment in probability. Endpoints and the ratio follow because a>0. This completes Theorem 2.

## 8. Verification boundary and remaining problems

The ancillary checker verifies rational identities, slot counts, simplex moments, Gamma-product identities in finite regressions, leading-coefficient specializations, symbolic density moments, and deliberately corrupted controls. It is not a finite-verification substitute for the all-dimension analytic proof above. This result has not been formalized in Lean. The earlier frozen qutrit purity Lean proof is a different result and does not certify this note.

Unsuccessful three-level numerical purity searches motivated the switch to this complete geometric law. They are not premises. The unrestricted maximal-purity conjecture, the exact AS leading coefficient in m>=3, proportional growth of both local dimensions, and non-flat matrix measures remain distinct unsolved targets here. AI assistance is disclosed; no external peer review or exhaustive priority verification is claimed.

## References

[H] R. Hildebrand, *Positive partial transpose from spectra*, Physical Review A 76, 052325 (2007), arXiv:quant-ph/0502170. https://arxiv.org/abs/quant-ph/0502170

[AKW] J. Ahiable, N. B. T. Kothakonda, A. Winter, *The geometry of absolute separability and other convex matrix properties from spectrum*, arXiv:2608.03390v1 (4 August 2026), especially the spectral criterion, Proposition 6.14 and Section 6.3. https://arxiv.org/html/2608.03390v1

[Tran] A. T. Tran, *Spectral Optimization for Absolutely PPT States: Purity, Entropy, and Volume Decay*, arXiv:2609.18568 (16 September 2026). The publicly retrieved abstract states the qubit volume order and the ratio of its explicit bounds; no stronger priority comparison is presumed. https://arxiv.org/abs/2609.18568

[KBNKB] T. V. Kondra, P. Barrios Hita, J. Neumann, H. Kampermann, D. Bruß, *Fundamental limitations on entanglement extraction from purity*, arXiv:2605.29197v1, Supplemental Lemma 2. https://arxiv.org/html/2605.29197v1
