# Complete complex Chollet: Gaussian replacement attempt

14 October 2026, Asia/Shanghai. Internal authoring agent: /root/written_breadth. Active ordinary mathematical exploration, not a solved conjecture, priority claim, or new Lean audit.

## C0. Whole target and effective clock

For every finite n and every complex Hermitian positive semidefinite A and B of order n, prove or rigorously refute
\[
 \operatorname{per}(A\circ B)\leq\operatorname{per}A\,\operatorname{per}B.
\]
No bound on n, rank, graph support, entry arguments, or aspect ratio is part of the target. A single actual PSD counterexample would refute the whole statement; a proof for a fixed rank/order is not its resolution.

The active stage started at 2026-10-13 20:19:32 UTC, after preservation of the U stage at 61a9e79791e0847d1f605bb032407407a447598c. Service reviews and interruptions will be excluded from the 45–90 effective minute switch rule. No discovery search is being passed off as a proof.

## C1. Fresh primary status check

The complete inequality through n=6 is already the public claim of Li–Zhao–Luo, v1 posted 31 August 2026. This stage read their entire Sections 2–4, including coefficient positivity, singular-border normalization and the actual induction. Their coefficientwise method expressly stops at n=6. This is an input/status check, not our solution of those orders.

Ma, 2609.37461v1, Theorems 1.2–1.3 cover rank at most four for n>=10 and order-nine rank-four tight correlation matrices; they expressly exclude unrestricted ranks and non-tight order-nine matrices. Only the stated theorems and relevant normalization were freshly read, not the entire finite certificate package.

The previously independently read October 3 rank-three/order-seven public proof remains excluded from new attack and credit. Pant–Singh v2 structural graph/Z-matrix classes also remain existing results. The current author-maintained Minc page is useful to locate original statements, but its stale order-seven gap is not accepted as a current-status proof. No exhaustive priority determination is made.

Sources: https://www.preprints.org/manuscript/202608.2196 ; https://arxiv.org/html/2609.37461v1 ; https://arxiv.org/html/2604.24192v2 ; https://yair-lavi.com/mincs-list/conjecture-30/index.html . See CHOLLET_REPLACEMENT_SOURCES.json for exact read scope.

## C2. Exact Gaussian replacement formulation

Choose independent centered proper complex Gaussian vectors Z and W with covariances A and B. Singular covariance is allowed, by linear images of standard proper Gaussians. Set F_i=Z_i W_i. Independence gives
\[
 \mathbb E F_i\overline F_j=A_{ij}B_{ij},\qquad
 \mathbb E F_i F_j=0,\qquad
 \mathbb E\prod_i|F_i|^2=\operatorname{per}A\,\operatorname{per}B.
\]
For a proper Gaussian vector G with covariance A circle B, complex Wick expansion gives
\[
 \mathbb E\prod_i|G_i|^2=\operatorname{per}(A\circ B).
\]
Thus the complete conjecture is precisely the comparison between these two product square moments at their common covariance. The vector F is bilinear chaos, not Gaussian. Scalar GPC or the already attributed PSD quadratic-form corollary gives a product-of-marginals bound; neither supplies this fixed-covariance comparison.

The Wick identity can also be derived directly: expand each Gaussian linear form and pair each holomorphic factor with exactly one antiholomorphic factor; properness removes same-type pairings. There is one term for each permutation.

Zero diagonal in A or B forces the corresponding row and column zero, so both sides vanish. Otherwise diagonal congruence reduces to correlation matrices without rank changes. Permutation-monomial Cauchy–Schwarz gives
\[
 |\operatorname{per}(A\circ B)|^2
 \leq \operatorname{per}(A\circ\overline A)\,
       \operatorname{per}(B\circ\overline B).
\]
Together with nonnegative PSD permanents, this proves equivalence with the self-conjugate target, not the target itself.

## C3. Exact replica polynomial, without a limiting-moment assumption

For every integer N>=1, let (Z^(k),W^(k)), 1<=k<=N, be independent copies and put
\[
 F_i^{(N)}=N^{-1/2}\sum_{k=1}^N Z_i^{(k)}W_i^{(k)}.
\]
Its covariance is still A circle B. Direct Wick expansion with copy labels gives the finite identity
\[
 M_N:=\mathbb E\prod_i|F_i^{(N)}|^2
 =\sum_{\sigma,\tau\in S_n}
 N^{c(\sigma^{-1}\tau)-n}
 \prod_i A_{i,\sigma(i)}B_{i,\tau(i)}.
 \tag{C3}
\]
Here c(rho) counts all cycles, including fixed points. For fixed sigma,tau, the holomorphic copy labels must be constant on cycles of sigma^{-1}tau; this gives exactly N^c choices. All antiholomorphic labels are then forced. The normalization is N^-n. In particular M_1=per A per B and its exact polynomial limit as N→infinity is per(A circle B), because c=n only for sigma=tau. No convergence-in-law argument or moment-determinacy claim is needed.

A proof that M_N is nonincreasing for all actual A,B and every real N>=1 would suffice, but is not established here. Termwise positivity in powers of 1/N is stronger and already false; see the next diagnostic.

## C4. Positive mixtures cannot repair the uniform border scalar comparison

For an arbitrary scalar border, the Li–Zhao–Luo method uses nonnegative ordinary coefficients alpha_k and doubled coefficients gamma_rs. A positive probability measure mu on t>=0 that repaired the same coefficientwise comparison would require
\[
 \int t^k\,d\mu\leq k+1,\qquad
 \int t^{r+2s}\,d\mu\geq s+1
\]
for the full relevant ranges. Already r=0,s=1 forces E_mu t^2>=2, while k=6 forces E_mu t^6<=7. Jensen for the nonnegative random variable t^2 gives E_mu t^6>=(E_mu t^2)^3>=8, a contradiction. For a finite positive measure the degree-zero comparison forces its mass to be one. Consequently a universal positive mixture of the same scalar evaluations cannot extend that coefficientwise argument beyond the sixth order. This does not rule out matrix-dependent aggregate estimates or another complete proof.

The obstruction is separate from the inherited weighted-graph x-squared obstacle; no weighted numerical search has been resumed.

## C5. Scope

No complete all-order comparison has been proved. Current exact identities and shortcut exclusions are research diagnostics only. In particular they do not solve Lieb dominance, Marcus per-in-per, the Gaussian polynomial U conjecture, or a new Gaussian product conjecture. No importance score, external peer review, publication, or proof-assistant coverage is asserted.

## C6. Exact negative replica coefficient and failed complete monotonicity

Take the actual correlation matrix
\[
 A=B=Y_3=\begin{pmatrix}1&-1/2&-1/2\\-1/2&1&-1/2\\-1/2&-1/2&1\end{pmatrix}.
\]
Its eigenvalues are 0,3/2,3/2. The six permutation monomials are 1, three copies of 1/4, and two copies of -1/8. In (C3), a fixed relative transposition contributes the cross-correlation 3/8; a fixed relative 3-cycle contributes -3/64. Consequently
\[
 M_N=\frac{39}{32}+\frac{9}{8N}-\frac{3}{32N^2},\quad
 M_1=\frac94,\quad M_\infty=\frac{39}{32}.
\]
The negative N^-2 coefficient is an exact obstruction to a coefficientwise-positive replica proof. Moreover
\[
 (-1)^k\frac{d^k}{dN^k}(M_N-M_\infty)
 =\frac{k!}{N^{k+2}}
 \left(\frac{9N}{8}-\frac{3(k+1)}{32}\right),
\]
which is negative at N=1,k=12. Thus complete monotonicity of this natural rational extension is also too strong. The actual first derivative is negative for every N>=1, so the example does not refute monotonicity or Chollet. Rank two here is only a shortcut countercheck, not a repeated attack on its existing positive theorem.

A second exact bounded control used the already known five-row rank-two Gram family with rows (1,sqrt(2)i^j), j=0,1,2,3, and (1,0). Its replica cycle coefficients, in ascending cycle counts, are
\[
 (0,-15808,11760,110312,115248,32504).
\]
They sum to 504^2; M_2=118188=(67/144)504^2. This is a diagnostic on the known Tran-type example, not a new permanent-on-top or Chollet counterexample. The reproducible integer control is in exploration/chollet_replica_exact_controls.py and the corresponding JSON. No random campaign was run.

## C7. Fixed-covariance comparison cannot be strengthened to all polynomial tests

Let Z_1,Z_2,W_1,W_2 be independent standard proper complex Gaussians and take
\[
 F=(Z_1W_1,Z_2W_2,Z_1W_2,Z_2W_1).
\]
These are legal decomposable bilinear factors, and their covariance is I_4 with zero pseudocovariance. But
\[
 F_1F_2-F_3F_4=0
\]
identically. For the matching proper Gaussian vector G with covariance I_4,
\[
 \mathbb E|G_1G_2-G_3G_4|^2=2.
\]
Therefore the Gaussian reference measure is not dominated by this bilinear field on all squares of holomorphic polynomials, and the difference of their degree-two polynomial moment matrices is not PSD. A proof using arbitrary-test convex order, a positive fourth-cumulant matrix, or a positive Fock-space replacement operator would assert a false strengthening. The requested product monomial still has expectation 16 for F and 1 for G. The signed test does not refute the original complete Chollet inequality.

## C8. Generic PSD-covariance Jensen is false, even with fixed diagonal

Let a=3/4 and let C have diagonal one and every off-diagonal entry a. Its smallest eigenvalue is 1/4. Put
\[
 X=\begin{pmatrix}
 0&0&1&1\\0&0&-1&-1\\1&-1&0&0\\1&-1&0&0
 \end{pmatrix},\qquad\epsilon=1/16.
\]
The operator norm of X is 2, so both C+epsilon X and C-epsilon X are positive definite, with smallest eigenvalue at least 1/8. Direct permutation expansion gives
\[
 \operatorname{per}(C+tX)
 =1+6a^2+8a^3+9a^4+(4-12a^2)t^2+4t^4
 =\frac{2713}{256}-\frac{11}{4}t^2+4t^4.
\]
If a random covariance T takes those two positive definite correlation matrices with equal probability, then
\[
 \operatorname{per}(\mathbb ET)-\mathbb E\operatorname{per}T
 =\frac{175}{16384}>0.
\]
Thus permanent is not convex on the positive definite fixed-diagonal domain. Conditional Gaussian representation alone cannot justify a generic covariance Jensen step. The original random diagonal-Gaussian orbit in C2 has additional constraints, and no conclusion about that particular orbit follows from this two-point counterexample.

## C9. Current unresolved step

The complete target remains the monomial product comparison in C2. A replica monotonicity proof could still work, but its coefficients and full test-function moment operator have unavoidable signs. A new proof must exploit the actual factorized Gaussian covariance/copy structure without assuming any of C4, C6, C7, or C8's false strengthenings. These are ordinary complete proofs of route obstructions, not a new solution of a major conjecture.

## C10. Actual ordinary/doubled sectors cannot be paired separately

Let m=2, H=J_2, x=(1,-1)^T. The normalized border is the actual PSD Gram matrix
\[
 A=\begin{pmatrix}2&0&1\\0&2&-1\\1&-1&1\end{pmatrix};
\]
Gram rows are (1,1),(1,-1),(0,1). Direct expansion gives
\[
 F(t)=2+2t^2,\qquad
 \Gamma(a,b)=2(1+b)^2+8a^2.
\]
Thus ordinary alpha_1=0, although the doubled occupation profile with one label2 and one label3 has squared-norm coefficient4. Indeed its complete sector vector is -2 times the symmetric tensor of the two orthogonal unit label vectors; its squared norm is8, divided by m!=2. The two remaining profiles with two label2 or two label3 each contribute2, giving gamma_(2,0)=8. Consequently an individual-profile estimate against alpha_1 alpha_1 is false on an actual PSD border.

Even the ordinary inductive deficit has a negative coefficient:
\[
 F(t)^2-\Gamma(t,t^2)=2(1-t^2)^2\geq0.
\]
Its middle coefficient is -4. At t=1 the smaller matrix R(1)=2I_2 is an equality case, so a pointwise inductive inequality does not yield coefficientwise dominance. The full border still has per A=8 and per(A circle A)=24<64; this is not a Chollet counterexample or new rank-two result.

## C11. Nonnegative coefficients plus pointwise induction alone are insufficient

This next example concerns an abstract implication, not actual PSD matrices. With m=64 set
\[
 F(t)=1+2^{-16}t^{64},\qquad \Gamma(a,b)=b^8/8.
\]
Their coefficients are nonnegative and in the usual degree ranges. For t>=0, put s=t^16/16. Then F(t)=1+s^4 and Gamma(t,t^2)=2s. Elementary differentiation gives
\[
 \inf_{s>0}\frac{(1+s^4)^2}{s}=\frac{64}{7^{7/4}}>2;
\]
the last sign is the exact integer comparison 32^4=1048576>823543=7^7. Hence Gamma(t,t^2)<=F(t)^2 for every t>=0. Nevertheless
\[
 \Gamma(1,1)+\partial_b\Gamma(1,1)=9/8
   > (F(1)+F'(1))^2=(1+65/65536)^2.
\]
The exact squared comparison is 8(65601)^2<9(65536)^2.

Therefore positivity of both coefficient lists and pointwise self-conjugate induction along every parabolic evaluation cannot by themselves imply the complete border inequality. This pair of abstract polynomials is expressly NOT a legal Gram witness: alpha_64>0 would force every x_i nonzero and gamma_(0,64)=alpha_64^2/64!>0, which the displayed Gamma lacks. The diagnostic isolates the additional actual sector relations that a valid complete proof must use.

## C12. The polynomial-moment-operator obstruction persists in the self case

The signed-test failure in C7 does not disappear after reducing to B=conjugate(A). Let Z and W be independent standard proper complex Gaussian vectors of dimension2, and set
\[
 F_1=Z_1W_1,\quad F_2=Z_2W_2,\quad
 F_3=(Z_1+Z_2)(W_1+W_2),\quad
 F_4=(Z_1+iZ_2)(W_1-iW_2).
\]
These have coefficients a_i and conjugate(a_i), for a_i=(1,0),(0,1),(1,1),(1,i), so the covariance is precisely A circle conjugate(A) for the PSD Gram A of these rows. Put
\[
 Q(z)=4z_1z_2-(z_3-z_1-z_2)^2-(z_4-z_1-z_2)^2.
\]
Writing u=Z_1W_1,v=Z_2W_2,a=Z_1W_2,b=Z_2W_1 shows Q(F)=4(uv-ab)=0 identically. The matching Gaussian vector is obtained by applying the same linear formulas to four independent standard complex Gaussian matrix entries H_11,H_22,H_12,H_21. Its covariance is A circle conjugate(A), and
\[
 Q(G)=4(H_{11}H_{22}-H_{12}H_{21}),\qquad
 \mathbb E|Q(G)|^2=32.
\]
Thus a PSD replacement operator on all holomorphic polynomial squares would still be false in the exact self-conjugate setting. The determinant-like signed polynomial is not the required product of legal rank-one factors; its failure does not decide Chollet.

## C13. Phase boundary and next analytic requirement

At 20:46:03 UTC the active Chollet research time was22 minutes45 seconds: wall time since20:19:32 minus the independent finite-APPT service review20:36:46–20:40:32. The stage remains active. No stochastic optimization or exhaustive small-order rerun was performed. The remaining route must control actual coupled ordinary/doubled sectors, rather than use an abstract nonnegative-polynomial implication or PSD replacement operator. All six diagnostics above are retained as exclusions, without promoting them to a complete result.
