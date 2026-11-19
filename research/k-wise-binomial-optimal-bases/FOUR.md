# Complete realizability test and exact maximal spread for four-wise independent bits

Write N=n−1 and take n≥5. Use the preceding phase definitions, so k=4 and the four nondistinguished sites can be written uniquely as {u−1,u,v,v+1} with 1≤u<v≤N−1. Put d=v−u≥1 and define
  C=N−(u+v−N)^2/(N−1),       p_0=(u+v−1)/(2(N−1)).
Then this basis is realizable on a positive-length interval if and only if
  d² < C < (d+2)².                                         (1)
When C equals either boundary, the only interior feasible parameter is p_0. When C is outside the closed range there is none. In particular for every n≥6 the maximal spread of a realizable basis is
  floor(sqrt(n−2))+2.
Thus BEKK Conjecture 5.13 holds exactly (also giving their monotonicity Conjecture 5.12 at k=4).

**Proof of the test.** By the interpolation formula of Hermann, it suffices to test the four signs of the cardinal interpolation weights for D~Bin(N,p) at those four sites. Write c=(u+v)/2 and Q(x)=(x−u)(x−v), R(x)=(x−u+1)(x−v−1). For either polynomial T=Q or R, writing t=Np and V=Np(1−p) gives
  Cov(D,T(D))=V[1−2p+2(t−c)],
since the third central moment is V(1−2p), and both quadratics have linear coefficient −2c. Now p_0 lies strictly between zero and one. At p=p_0 the covariance vanishes and t−c=p_0−1/2 lies strictly between −1/2 and 1/2. Thus u<t<v since d≥1. Direct substitution gives
  4 E Q(D)=C−d²,  4 E R(D)=C−(d+2)².
Indeed, for example, E Q=V+(t−c)^2−d²/4, and 4V+4(p_0−1/2)^2=1+4(N−1)p_0(1−p_0)=C.

Up to strictly positive fixed divisors the two outer weights at u−1 and v+1 are the expectations of (v+1−D)Q(D) and (D−u+1)Q(D). At p_0 both signs are therefore the sign of E Q(D). Similarly, for the inner weights at u and v the two expectations are (D−v)R(D) and (u−D)R(D), respectively. Their signs at p_0 are both minus the sign of E R(D). A lower member of a pair changes sign only from positive to negative as p increases, and an upper member only from negative to positive, by the strictly increasing tilted mean in §2 of the phase proof. This is a sign rule, not monotonicity of the weight itself.

Each of the outer and inner couples consists of one lower and one upper member. Thus if (1) holds, all four weights are strictly positive at p_0 and on a neighborhood. If either couple is strictly negative at p_0, its upper member remains negative to the left and its lower member remains negative to the right; feasibility is impossible anywhere. If either couple is zero at p_0, the same argument gives infeasibility everywhere else. The other couple is strictly positive at p_0 in this case, so that p_0 really is feasible. This proves all the asserted alternatives.

**Proof of the maximum.** The spread is d+2; necessity gives d²<C≤N, hence d≤floor(sqrt(N−1)) for integers. For n≥6, choose d=floor(sqrt(N−1)), u=floor((N−d)/2), v=u+d. Then 1≤u<v≤N−1. The centering error |u+v−N| is at most 1. Since N≥5, C≥N−1/(N−1)>N−1≥d². Also (d+1)²>N−1, so (d+2)²>N≥C. This realizes the stated maximum.

**Rationality at exceptional four-wise transitions.** In BEKK's definition at least two sites depart the old phase basis. They have zero mass at the shared breakpoint. Since n has positive mass and every upper member of an old pair is positive, exactly the two lower members depart or vanish and the tilted quadrature law on J consequently uses just two integers h<j. Specifically the masses for this law are (n−s)w_s/[n(1−p)]=E l_s(D) at s∈J; they are nonnegative, sum to one, and match the first three moments of D by interpolation. Set U(x)=(x−h)(x−j). Moment matching gives E U(D)=E[D U(D)]=0. The covariance calculation above with 2c=h+j yields
  h+j=1+2(N−1)p,
and hence p is rational. This establishes the four-wise instance of BEKK Conjecture 5.9, not its general instance. It does not rely on every isolated feasible basis being a phase.
