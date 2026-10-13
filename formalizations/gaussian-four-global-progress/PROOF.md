# Analytic profile and ordered rank-one obstruction

This supplement records new proofs without changing frozen manuscript editions.
The formal sources, rather than numerical calculations, are the proof evidence.

Let phi be the actual standard Gaussian density, T(a)=integral_(a,infinity) phi,
and q=upperQuantile(1/4). Gaussian symmetry gives T(0)=1/2 and T(-a)=1-T(a).
Strict monotonicity gives q>0. The existing actual half-line flux theorem gives
integral_(a,infinity) x d gamma_1 = phi(a).

## A shorter exact proof of the strict margins (12)

Mathlib's proved bound pi<3.15 gives phi(0)>39/100. The global analytic inequality
exp(t)>=1+t implies phi(x)>=phi(0)(1-x^2/2). Therefore

    integral_0^(7/10) phi(x) dx
      >= phi(0)*(7/10-(7/10)^3/6)
      > (39/100)*(3857/6000)
      = 150423/600000 > 1/4.

It follows that T(7/10)<1/4 and hence q<7/10. Thus

    phi(q) >= phi(0)*(1-q^2/2) > (151/200)*phi(0) > (3/4)*phi(0).

Squaring and using phi(0)^2=1/(2*pi) gives phi(q)^2>9/(32*pi).
`Profile.lean` proves these statements using actual integrals, derivatives,
monotonicity and rational arithmetic; the displayed numbers are not floating
approximations and no numerical Gaussian-CDF bound is assumed.

## Actual intervals and affine winners

For four strictly increasing slopes a_i, compare the affine scores a_i*x-p_i.
Adjacent equality occurs at t_i=(p_(i+1)-p_i)/(a_(i+1)-a_i). Positive Gaussian
mass of the middle two winners supplies points proving t_0<t_1<t_2. Direct
comparison of all four scores identifies every winner set with its ordered
open interval. Endpoint singletons are Gaussian-null, so the balance equations
force (t_0,t_1,t_2)=(-q,0,q).

Actual Gaussian integration then gives the moment vector

    (-h, h-phi(0), phi(0)-h, h),  h=phi(q).

For self-moment inducing scores this is also the slope vector. The middle
facet weight is w_1=phi(0)/(2*(phi(0)-h))>2. All other adjacent weights are
positive. At z=(0,1,-1,0), whose coordinates sum to zero, the facet quadratic
form equals w_0+4*w_1+w_2>8 while sum z_i^2=2. Thus the required spectral
upper bound fails.

## Actual ambient transport and exact limitation

For unit u in R^d, the pushforward of the actual standard Gaussian by
x -> inner(u,x) is gaussianReal(0,1). The winning cells for a_i*u are precisely
preimages of the scalar winner sets. Their masses agree; commuting the linear
functional inner(u,.) with the Bochner integral proves the projected-moment
identity. An actual vector self-moment identity consequently implies the
scalar self-moment identity used above, in every ambient dimension.

This does not prove the covariance Hessian, the normal-cone rescaling of a
singular maximizer, automatic sorting/relabeling of arbitrary rank-one data,
or the rank-two case. The explicit facet form is not silently equated to an
unproved covariance Hessian. See GAPS.md for the remaining global chain.
