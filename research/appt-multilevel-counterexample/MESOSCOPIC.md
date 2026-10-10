# An intermediate-rank plateau defeats the coefficient 4+gamma

Research working proof, 10 October 2026. No new preprint or Release. The previous coefficient 4+gamma was proved sharp ONLY when the plateau rank lies between m(m-1)/2 and D-m(m+1)/2. It is not an unrestricted bound, as this note proves.

## 1. A finite all-unitary sufficient condition

Let 3<=m<=n, D=mn, 1<=r<=m(m-1)/2. Let Q be a rank-r orthogonal projection and v a unit vector in its range. Consider

    B=I+cQ+(a-c)|v><v|,   a>=c>=0.

Its eigenvalues are 1+a once, 1+c with multiplicity r-1, and 1 with multiplicity D-r. It is APPT after normalization if

    max{a,c sqrt(2r)}+c sqrt(2m)<=2.                              (M1)

Proof. Fix any global unitary and any unit Schmidt test vector with coefficients x_i>=0. For W=(|psi><psi|)^Gamma, a rank-r projection has trace against W bounded below by minus the sum of the r largest pair products x_i x_j (padding with zero products when necessary). This follows by evaluating the projection's diagonal entries in an eigenbasis of W: they lie in [0,1] and sum to r. The additional vector term is at least -(a-c) max_{i<j}x_i x_j. Hence the expectation of the partial transpose is at least

    1-c sum_{r largest pairs} x_i x_j-(a-c)max_pair x_i x_j.

Choose the r largest pairs as a graph G; it contains a largest-product edge. The weighted adjacency matrix has weight a on that distinguished edge and weight c on the other r-1 graph edges. Split its two distinguished vertices from the remaining m-2 vertices. The first diagonal block has maximum eigenvalue a. The second has operator norm at most c sqrt(2r), by its Frobenius norm. The cross block has at most 2(m-2) entries bounded by c, so its operator norm is at most c sqrt(2m). The norm of the symmetric off-block matrix equals this cross-block norm. Therefore its largest eigenvalue is bounded by the left side of (M1). The quadratic expectation is nonnegative. Both the unitary and test vector were arbitrary, proving APPT.

This is a sufficient condition for actual quantum states, not feasibility in a necessary-only relaxation. The nested projection/vector structure is needed for the stated spectrum, not for independently applying the two lower trace bounds.

## 2. Explicit rational family in all sufficiently large local dimensions

For m>=9 and n>=m set

    r=m ceil(sqrt(m)),
    L=ceil(sqrt(2r)), H=ceil(sqrt(2m)),
    c=2/(L+H), a=2L/(L+H).

One has r<=m(m-1)/2: ceil(sqrt(m))<=sqrt(m)+1<=(m-1)/2 for m>=9. Since L>=sqrt(2r), H>=sqrt(2m), and a=cL, the left side of (M1) is at most c(L+H)=2. Thus every finite member is APPT with rational eigenvalues. No eventual graph enumeration is required for this family.

Put T=a+(r-1)c and S=a^2+(r-1)c^2. For rho=B/(D+T),

    D^2[Tr(rho^2)-1/D]=(S-T^2/D)/(1+T/D)^2.                      (M2)

If m tends to infinity and n/m tends to any finite gamma>=1, then

    r/m -> infinity, r/m^2 ->0,
    a ->2, r c^2 ->2, T^2/D ->0, T/D ->0.

Consequently

    D^2[Tr(rho^2)-1/D] ->6.                                     (M3)

In square systems this exceeds the earlier coefficient 4+gamma=5. The difference is not produced by a failure of the previous proof: this plateau rank r is outside its stated intermediate-rank class and grows strictly between m and m^2.

An exact finite comparison, without storing a huge matrix, is m=n=16384, r=2097152, L=2048, H=182. Here c=1/1115 and a=2048/1115. The normalized centered purity is

    D^2[Tr(rho^2)-1/D]
      =452164212835264520781824/89585058955962578104321,

and it exceeds even the previous subclass's finite bound 4+D/(m-1)^2 by

    1134801570907058645479805042684
    /24044870718003888546572278919169 >0.

The finite example is only an arithmetic diagnostic; (M1)-(M3) prove the full family and its limit.

## 3. Exact graph reduction for a nested four-level class

Let P,Q be nested projections with ranks k,r, and let v be a unit vector in the range of Q. For a,c,d>=0 set

    B=I+dP+cQ+a|v><v|,
    R=m(m-1)/2<=k<=D-m(m+1)/2,
    1<=r<=R.

Then B is APPT if and only if, for every m-vertex graph G with exactly r edges and every distinguished edge e of G,

    lambda_max(d A_complete+c A_G+a E_e)<=2,                      (M4)

where E_e has ones at the two off-diagonal positions of e.

Sufficiency follows exactly as in Section 1: the rank-k projection contributes at worst minus the sum of all negative Schmidt-projector eigenvalues, the rank-r projection contributes minus the r largest such magnitudes, and the vector contributes the most negative one. Their simultaneous worst assignment maximizes over graphs and distinguished edges.

For necessity, fix any nonnegative Schmidt vector and the selected graph. Put P on all R antisymmetric vectors and k-R zero eigenvectors; the rank condition ensures enough zero slots. Put Q on the r selected antisymmetric vectors, and v on the distinguished one. This realizes the given nested flag by a global unitary. Positivity gives the corresponding quadratic form bound for every nonnegative vector. The adjacency matrix is nonnegative, so its largest Rayleigh quotient is attained on a nonnegative vector. Conversely, maximizing graph weight for a fixed vector chooses the r largest products and a largest-product edge, so requiring e in G loses nothing. This proves (M4).

The eigenvalues of B are 1+d+c+a once, 1+d+c repeated r-1 times, 1+d repeated k-r times, and 1 repeated D-k times. Thus (M4) addresses a genuine four-level family. GRAPH_LIMIT.md analyzes all graph arrangements at once when m<<r<<m^2; it must not be replaced by a few sampled graphs.

## Scope

The finite family and its coefficient 6 are proved above. They show that the current unrestricted optimization cannot be settled by promoting the previous sharp subclass coefficient to a global assertion. Absolute separability, the exact unrestricted maximum, and the smallest finite dimensions admitting these improvements remain separate questions. The new arguments are analytic and are not covered by the frozen qutrit Lean certificate.
