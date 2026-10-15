# New root scope: total-dimension, two-scale diverging-order spectral reduction

Author working proof, 2026-10-15. Not yet frozen or independently reviewed.
This records the substantive derivation before public-layout work resumes.
Original complex PSD trace-one all-global-unitary APPT objects throughout.

## Uniform physical core, even when dimensions stay fixed

For D=mn,2<=m<=n define R=m(m-1)/2,S=m(m+1)/2,j=D-S+1,
B={max(2,R),...,j}. This excludes index1 also for m2 (the old R1
body included the peak). N=D-m^2+2 ifm>=3, N=D-3 ifm2; alwaysN>=1.
Let H_alpha(y)=y^alpha-1-alpha(y-1),alpha>=2 and y_i=Dlambda_i.
K=1+[H_alpha(y1)+sum_B H_alpha(yi)]/D. Exact trace centering gives
M=K+R_E/D withR_E>=0 from the omitted nonleading exceptional coordinates.

New uniform lemma: there exist UNIVERSAL constants Q0<infinity and
rho in(0,1), independent of all m,n, such that

  sum_E(yi-1)^2<=Q0,
  every omitted nonleading yi<=rho u_D, u_D=3D/(D+2)>=2.

Proof for m>=M0: mature G12/G13 give common bounded Q_E and y2<=5/2,
while u>=8/3, by one fixed sufficiently large M0.
For3<=m<M0: Ecardinality<=M0² and0<=yi<=3 giveQ_E<=4M0².
Exact mature G7 givesg1²+g2²<=4, g1>=g2>=0, so a2<=g2<=sqrt2.
Actual pivot A=Dy_j<=D/j (firstj eigenvalues are>=lambda_j).
Thus y2<=A(1+sqrt2)<= (1+sqrt2)/[1-(S-1)/D].
ForD sufficiently large uniformly over this finite m list, this is<=5/2.
For the remaining finite dimension pairs m>=3, D>=9, compact APPT sets
give a strict bound max y2<u_D. Indeed equality y2=u_D would also give
y1=u_D; equality in G15's smallest-three-tail average, sinceD-1>3,
forces ALL other eigenvalues equal y1/3, contradictingy2=y1.
The maximum ratio over finitely many such pairs is strictly below1.
For m2: omitted nonleading indices are onlyD-1,D, bounded byD/(D-1),
whose ratio to u_D is (D+2)/[3(D-1)]<=2/3. QE<=6. This is why the
qubit reindexing is necessary. Take max of the finite ratio,15/16,2/3.
No effective numerical value of rho or M0 is claimed from compactness.

This is not assuming a general uniform second-peak gap for qubits:
qubit second peaks may approach3. They are retained in B, not discarded.

Then R_E<=C alpha² rho^alpha u_D^alpha by the real-power kernel andQE.
The actual spike gives M*-1>=(u_D^alpha-1-2alpha)/D>=u_D^alpha/(2D)
after a universal alpha threshold, sinceu_D>=2. Thus

  0<=(M-K)/(M*-1)<=C alpha² rho^alpha

for EVERY dimension pair, even fixedD, and every actual state.

The S9 own-peak polynomial comparison is re-proved from this uniformQE:
on positive deviations H(1+x)/x² is monotone foralpha>=2; split
x1>=1/alpha vsx1<1/alpha. On negative deviationsH<=a_alpha x².
HenceR_E<=C alpha²(1+H_peak), and DK>=1+H_peak yieldsM/K<=1+C alpha².
Combine loggap<=R_E/D andloggap<=log(1+C alpha²), split
chi=log(u_D^alpha/D) at0 and(-logrho)alpha/2. The actual spike lower
logM*>=log(1+expchi/2) gives exactly

  0<=(logM-logK)/logM*
       <=C[alpha² rho^(alpha/2)+log(1+alpha)/alpha].

This extends the new author's S9 growing-m reduction. Credit its original
three-regime idea; the new global physical lemma handles bounded m and
qubits and makes both reductions uniform in ALL dimensions at alpha->infinity.
S9 is currently an author proof pending review, so the final manuscript
will contain the full core argument, not rely on an unreviewed PASS.

## Exact finite body coordinates

A=y_j>0,Aplus=y_max(2,R),kappa=Aplus/A-1,
mu=mean_B yi,theta=(mu/A-1)/kappa (theta0 at kappa0).
Use the exact size-biased chord loss Lambda of FAST/S9:
sum_B yi^alpha=N A^alpha[1+theta((1+kappa)^alpha-1)(1-Lambda)].
At kappa0 setLambda1. K is then a function of actual
y1,mu,kappa,theta,Lambda, retaining both centered linear terms.
Constantbody does not justifymu1. No endpoint-shape assumption or real rank.

## New global calibrated moment benchmark

For m>=3 use the OLD finite scalar V of ALL_ORDER_VARIATIONAL (same asX).
For m2 use EXACT finite compact Song--Chen three-family power maximum
(the X paper's exact qubit reduction). This is an explicit scalar T,
not an optimization over an unknown APPT set. Claim jointD->infinity,
alpha->infinity: (M*-1)/(T-1)->1 uniformly over ALL dimension pairs;
then logM*/logT->1. No fixedD version of this benchmark claim.

Growingm case is the existingG1/V18 small-alpha/m relativeEXCESS plus
V1/V17 positive-floor argument foralpha>=epsilon*m, as proved inS9.
Include that derivation directly and credit old inputs.

Fixed m>=3 case is NEW strengthening ofX's merely relative entropy glue:
putt=q-1>0,delta=t/2. For kappa<=delta bulk<=F_(1+delta),peak<=R;
for kappa>=delta bulk<=F_q,peak<=R*c_m^alpha withc_m<1 (eta(delta)>0).
F_q>=q^alpha/(alpha*exp(t)) by choosingtheta1/alpha.
ThusF_(1+delta)/F_q decays exponentially and
V/max(F_q,R)->1 uniformlyD asalpha->infinity.

M* is eventually EXACT max(hole,F_integer,pole) by oldA5, oneD0(m)
for allorders. Foralpha<=A logD, nearest physical integer theta to the
continuous optimum gives logF_integer-logF_q=O_m(alpha²/D²):
theta*~1/(talpha), derivativezero, HessianO_m(alpha²) within1/(2D).
Foralpha>A logD chooseA>2/log(u0/q) withq<u0<3, alsoA>2/log3.
ThenF_q/R<=D(q/u_D)^alpha<=D^-1 eventually; hole/R similarly,
andpole/R=1+(D-1)/3^alpha=1+o1. BelowAlogD hole->1 andpole<=R+1,
whileF_q->infinity. HenceM*/V->1 on everyfixedm jointD/alpha path.
M* grows at leastexp(c_m(alpha-1)) using a half-rank APPT projection
and Renyi monotonicity, so raw moment andEXCESS comparisons agree here.

For m2 T exact. A bad totalD/alpha subsequence has growingm or fixedm
subsequence, proving the SINGLE joint-tail uniform statement. This is
stronger than taking logarithms of a factor2 sandwich. Fixedm logerror
alone would NOT prove the moment benchmark.

## Actual tests and endpoints

Z=K-1. Under jointD->infinity,alpha->infinity,
sharp moment-excess iffZ/(T-1)->1;
relative entropy iff log(1+Z)/logT->1.
These are full spectral OBSERVABLE reductions, not a complete geometric
classification of every body law or an instantaneous scalar argmax distance.
At alpha=infinity separately use log(y1)/log(u_D), exactly; no exponent
substitution is required. All finite construction, low-order geometry,
absolute separability and old Lean scope remain separate.

Next: capture exact input blobs/authorS9, write final proof and theorem map,
controls for qubit double-counting, actual constant body/centering, both
optimality scales, fixedm V vs integer grid and logarithmic transitions.
No proof promotion or claim of independent review yet.
