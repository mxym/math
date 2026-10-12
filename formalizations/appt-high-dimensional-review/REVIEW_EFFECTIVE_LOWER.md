# Effective spike-plateau lower bound and the complete wide-sector asymptotic

This checkpoint verifies a lower branch of the existing high-dimensional purity research. It does not certify the multiscale coefficient eight below aspect ratio four, the full entropy laws, or dimension-varying rigidity. No new preprint or Release is prepared.

## Physical construction and exact finite statement

For integers h>=1, m>=2 and n>=m, write D=mn, k=ceil(D/2), and b=(h+1)m+2h^2+h. Take a coordinate projection P of rank k and a coordinate unit vector v in its range. Define

    B=b I+2h P+2mh |v><v|,
    Z=Db+2h(k+m),
    rho=B/Z.

`effectiveSpike_absolutelyPPT` proves all-global-unitary APPT of the unnormalized matrix for every positive contraction P and every unit vector v, without assuming v belongs to its range. The range condition is used only for the exact moment computation of the chosen coordinate family. `exists_effective_lower` constructs the finite support and the distinguished coordinate internally. It proves actual density, APPT and

    (h/(h+2))^2 (4+n/m) <= D^2 [purity(rho)-1/D]

whenever m>=2h^2+4h. All coefficients of these integer-parameter states are rational. No floating-point optimization, numerical unitary test, or supplied Schmidt decomposition is used.

## Finite positivity certificate

For any real Schmidt coordinates s and two distinct indices i,j, put H=s_i^2+s_j^2, T=sum of the other coordinates, Q=sum of their squares, and u=s_i+s_j. The proof verifies the exact identity

    b sum(s_l^2)-2h sum_{l<r}s_l s_r-2mh s_i s_j
      = (h u-T)^2+(h+1)(mQ-T^2)+mH
          +h(m+h+1)(s_i-s_j)^2+2h(h+1)Q.

Cauchy--Schwarz gives T^2<=mQ. All terms are nonnegative. The existing physical signed Schmidt model, including zero vectors/singular rows, lifts this certificate to the original complex partial-transpose quadratic form and every global unitary. These hypotheses are proved in the final physical construction, not retained as a replacement for APPT.

## Exact moments and uniformity

With T0=2h(k+m) and S0=4h^2(k+m^2+2m), the original trace-square purity is

    [Db^2+2bT0+S0]/[Db+T0]^2.

Writing d=2k-D in [0,1], exact centered arithmetic gives

    D S0-T0^2-D h^2(4m^2+D)=h^2[4mD-(2m+d)^2]>=0.

The upper bound Z<=D(h+2)m holds under the displayed finite threshold. This proves the lower estimate before any limit. `effective_ratio_error` supplies an explicit parameter approximation: h>=4/epsilon implies (h/(h+2))^2>=1-epsilon. Consequently one smaller-dimension threshold works for every n>=m.

`appt_total_dimension_branch_lower` combines this construction with the already verified fixed-local projection family. It proves that, for every epsilon>0, one total-dimension threshold works for ALL 2<=m<=n and produces an actual APPT density satisfying

    D^2[Tr(rho^2)-1/D] >= (1-epsilon)[4+D/(m^2-1)].

There is no hidden interchange of an unbounded number of levels or an aspect-ratio-dependent threshold. The smaller m range is treated separately with the exact fixed-local rounding bound.

## Complete asymptotic endpoints

In the sector n>=4m, the matching previously verified upper branch is also 4+D/(m^2-1). `appt_wide_relative_error` proves a uniform two-sided relative bound for the actual purity supremum as D grows. `appt_wide_purity_asymptotic` is a genuine Tendsto theorem along every dimension sequence eventually satisfying 2<=m and 4m<=n, with D tending to infinity. The smaller dimension may remain fixed, grow, or oscillate between regimes.

`appt_large_aspect_purity_limit` separately proves

    D^2[P_sup(m,n)-1/D] -> 4+gamma

whenever m tends to infinity and n/m tends to any fixed finite gamma>=4. For gamma=4, convergence from BELOW four is allowed; eventual membership in the wide sector is not assumed. The proof sandwiches the actual physical supremum between the uniformly constructed lower states and the unrestricted upper theorem. Supremum nonemptiness, boundedness and attainment are inherited from verified physical theorems.

## Failure controls and exact audit scope

Even 6x24 and odd 7x29 instances check actual density, APPT, half-rank counts and exact purities. A separate physical control shows that deleting the finite interaction reserve is invalid: the positive trace-one 2x2 state diag(8,8,26,8)/50 is NOT APPT, witnessed by the actual Hadamard orbit. Another control rejects replacing a finite state by its limiting coefficient.

The final audit retains every previously checked rectangular/physical endpoint and adds all new theorem dependencies. Exact-type corruption tests target the final fixed-aspect limit, the total-dimension wide limit, the generic physical sufficiency theorem, the existential finite construction and the all-total-dimension lower branch. Standalone compiler success is not independent verification; full build and trust-zero evidence must be read from the source-bound verification directory.

The remaining balanced/multiscale sector 1<=gamma<4 requires a matching lower coefficient eight, rather than the lower coefficient 4+gamma proved here. The measure/forest limit, simultaneous hierarchies, full entropy minima and asymptotic rigidity are not inferred from this checkpoint. No priority claim or minimum-dimension threshold claim is made. Original quantum definitions and immutable releases remain unchanged.
