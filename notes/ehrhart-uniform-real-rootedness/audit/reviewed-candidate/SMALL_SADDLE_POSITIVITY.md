# Parent theorem: positive reverse coefficients in the small-saddle regime

INTERNAL DRAFT: the argument below is complete at the auxiliary-theorem level,
but has not had independent review/Lean checking. It does NOT solve the full
Ehrhart conjecture. Not for publication while the main attack is active.

Let d>=1001, 1<=m<=d-2, and choose x>0 with mu_d(x)=m. Under x<=1/10,
[z^m]R_d(z)>0. Definitions R_d,J_n,P_n,H_s,lambda and the marked identity
are those of de Castro 2609.06096v1, Sections 8–9. Set R=1/lambda,
p=x/(1+x), nu=integral_0^1 xt/(2+(x-1)t)dt, y=dx, and kappa=[z^m]P_d.

## Scalar/majorant bounds

The exact program verify_small_x_majorant.py certifies the finite rational
inequalities used here; it is not itself a full theorem verifier.
At x=1/10, q=(1+x)R=(11/20)^(20/9)<53/200<4/15, certified by ninth powers.
For all x<=1/10, v_a=(1+x)P_a(x)R^a and q increase with x:
 d(log v_a)/dx=(p-e_a)/x>=0, e_a=a nu-mu_a in [0,p].
Thus the majorant b_n and h_s increase with x as well.
The primitive product estimate gives v_a<(3/10)a^(-5/2) for a>=2
(using pi>55/18); v_1=q<3/10 also.
Finite sums over a<=64,h<=16 plus the explicit geometric and integral tails
in the program prove
 beta<2/5, beta1<4/5, T1<3/25, T2<1/5,
where Tj=sum_(a,h) w_(a,h)((h-1)a)^j and
w=v_a phi(h)/h^2 q^((h-1)a).
For T1,T2 one may instead use the direct bounds printed in the program.

For n>=16,
 n^(5/2)b_n <=3/10+(9/10)n^(3/2)(4/15)^(n/2)<2/5.
The expression after 3/10 decreases for n>=16; its endpoint is an exact
rational comparison. The n<16 base is checked by squaring.
For h_s, the finite base s<=23 is checked by h_s^2 s^5<1. The recurrence
bound in LARGE_COMPONENT_SMOOTHING.md with B=2/5,C=1,beta1<4/5,exp(beta)<3/2
closes the induction at s>=24. Hence h_s<s^(-5/2) for every s>=1.
Moreover E=exp((x-1)J(R,x))>exp(-beta)>2/3 and exp(beta)/E<9/4.

Elementary integral/log bounds give (9/25)x<=nu<(2/5)x. A rational logarithm
series certificate for the lower endpoint is to be included in the verifier.
The integer-mean condition implies y>5/2, since m<=d nu<(2/5)dx.
Always V_d<=mu_d<(2/5)y.

## Centered degree moments

For a component of dimension n=ha, K=X_a+Bin((h-1)a+1,p).
Its centered mean is t_a+(n-a)(p-nu), where 0<=t_a=p-e_a<=p.
After including the first extra Bernoulli, Jensen bounds its variance by
 a nu(1-nu)+p max(1-2nu,0); the remaining n-a Bernoulli variables add
(n-a)p(1-p). This yields
 M1<= (13/25)x,
 M2+M1^2< (24/25)x,
where Mj are the first/raw second moments of K-n nu in the logarithmic
compound-Poisson intensity (so the exponential's raw second moment is
exp(beta)(M2+M1^2)). For clarity, a loose bound for M2 is
(21/25)x+(21/25)x^2, and M1^2<=(169/625)x^2; their sum is <(24/25)x
when x<=1/10.
The exponential absolute first centered moment is at most
exp(beta)(2nu beta1+M1)<exp(beta)(29/25)x.

## Split the marked identity at S=floor(d/8)

For s<=S, n=d-s>=7d/8. The primitive multiplier is
 A=(n/d)lambda^s P_n/P_d=(d/n)^(3/2)exp(delta_n-delta_d).
The source product estimate -1/n<delta_n<0 implies
 A<5/4, |A-1|<((9/4)s+3)/d for s>=1, while A=1 at s=0.
The derivative of (1-t)^(-3/2) is <9/4 on [0,1/8];
exp(1/n)<=1/(1-1/n) supplies elementary rational endpoint certificates.
Consequently the normalized prefactor error is <27/(4d).

Write eta=mu_d-mu_n-s nu. The trapezoidal error for f_x(t) gives
|eta|<=3x/(16n)<x/(4d), since 0<=x<=1/10 and
|f'_x(1)-f'_x(0)|<=3x/2. Thus the exponential absolute and squared shift
moments for delta=mu_d-k-mu_n are bounded respectively by
exp(beta)(117/100)x and exp(beta)(97/100)x.
The parameter distance D between the padded n- and d-arrays is <=2sp;
its weighted sum is <=exp(beta)(8/5)x.

For these arrays V_n>=(63/220)y-1/11 and
W=min(V_d,V_n)-1/4>=(63/220)y-15/44.
The same lower bound holds for V_d because d>=n and the elementary
V_j>=mu_j/(1+x)>=(j nu-p)/(1+x) applies to either j.
Use the variance-order interpolation in CENTERED_COMPARISON_LEMMA.md.
For y>5/2 its C2/A1 bounds imply the uniform inequalities
 y sqrt((24/5)y+1) C2(W)<50,
 y sqrt((24/5)y+1) C2(V_n)<50,
 y sqrt((24/5)y+1) A1(V_n)<100.
For C2 split at y=7/2: below it use C2<10/3 and sqrt((24/5)y+1)<17/4; above it W>=3y/16 and sqrt((24/5)y+1)<(23/10)sqrt(y). The Gaussian constant is <8/5 and (16/3)^(3/2)<25/2. Each resulting bound is <50.
For A1 split at y=5: below it A1<=4; above it V_n>=y/4>=1 and
A1<=4/V_n^(3/2). The resulting constants are <50 and <100.
The modal lower bound is Pr(X_d=m)>=1/sqrt(12V_d+1).
Therefore the normalized small-s probability error is less than
 (5/4)(9/4)[(12/5)*50+(117/100)*100+(97/200)*50]/d <735/d.
Together with the prefactor error this is <742/d.

## Middle and large components

The omitted E tail is at most
 E^(-1)sum_(s>S)h_s <27 d^(-3/2), since S>=d/9.
For S<s<=d/2, use the primitive X_n atom bound and h_s mass.
Here V_n>=(9/55)y-1/11 and the ratio of its largest atom to the d-mode
is <5 (square the Gaussian atom bound and use y>5/2, pi<4).
The source bound A<4 gives total normalized middle primitive contribution
<540 d^(-3/2).

For s>d/2 use the full J_n, n=d-s. The positive-majorant degree smoothing
has c(x)>=1/6 and p(1-p)>4x/5, so its maximal atom is bounded by
sqrt(15/(4sx)). Also P_d(x)R^d>(5/19)d^(-5/2), and the reciprocal d-mode
is <(23/10)sqrt(y). Multiplying these inequalities gives the upper bound
(35/2)d^2 sum_(n<d/2) n ||J_n||_x R^n (d-n)^(-3).
Since sum n ||J_n||_x R^n<=beta1/(1+x)<4/5 and E>2/3,
this normalized large contribution is <169/d.

For all periodic terms with n>=d/2, the source estimate for J_n-P_n and
the same modal/product lower bounds yield normalized error
<35 d^3 exp(-d/20)<1/1000 for d>=1001.
This function decreases there; the endpoint follows from exp(1)>8/3
and the exact rational inequality 35000*1001^3*(3/8)^50<1.

## Conclusion of this auxiliary theorem

All marked-identity terms and the omitted E tail have been accounted for.
The relative error with respect to E is less than
 912/d+567/d^(3/2)+1/1000
 <=912/1001+567/(1001*31)+1/1000<1.
Hence [z^m]R_d>0 in the stated small-saddle regime.

Still missing for the FULL problem: the complementary x>1/10 reverse-saddle
range, a complete independent audit of these parent bounds, and binding the
original d<=1000 finite certificate in a final deliverable.
