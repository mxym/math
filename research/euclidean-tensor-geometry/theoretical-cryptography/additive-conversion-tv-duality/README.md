# Exact TV certificates for additive distribution conversion

## Question

Let (G) be a finite abelian group and let (mu,
u) be probability distributions on (G). A common proof step in cryptography and randomized reductions asks whether one can transform (Xsimmu) into the target law (
u) by adding independent randomness (Dsimkappa):

[
X+Dsim mu * kappa stackrel{?}{approx} 
u.
]

When exact conversion is impossible, what is the **best possible total-variation error**, and how can impossibility or optimality be certified without guessing a Fourier-frequency obstruction?

This note gives an exact finite-dimensional answer, a dual certificate, a symmetry reduction, and a sparse-support bound for an optimal converter. It is a standalone assurance result about synthetic distributions; it does not recover secrets or attack an implementation.

## Translation-hull theorem

For (yin G), write
[
(T_ymu)(x)=mu(x-y).
]
Let
[
mathcal P_mu=operatorname{conv}{T_ymu:yin G}.
]

Because
[
mu*kappa=sum_{yin G}kappa(y)T_ymu,
]
the set of all laws obtainable by independent additive randomization is exactly (mathcal P_mu).

Define the optimal conversion error
[
delta(mu,
u)=min_{kappainDelta(G)}
  operatorname{TV}(mu*kappa,
u).
]

Then

[
oxed{
delta(mu,
u)
=
rac12max_{|f|_inftyle1}
left(
langle f,
uangle
-max_{yin G}langle f,T_ymuangle
ight).
}
]

Consequently:

- exact conversion exists iff (
uinmathcal P_mu);
- any (f:G	o[-1,1]) with
  [
  langle f,
uangle>max_ylangle f,T_ymuangle
  ]
  is a rigorous impossibility certificate;
- if a candidate converter (kappa) and a dual function (f) attain the same value, both are optimal.

### Proof

Use the dual representation of the (ell_1) norm and finite-dimensional minimax:

[
egin{aligned}
2delta
&=min_{kappainDelta(G)}
  max_{|f|_inftyle1}
  langle f,
u-mu*kappaangle\
&=max_{|f|_inftyle1}
  min_{kappainDelta(G)}
  left(langle f,
uangle
  -sum_ykappa(y)langle f,T_ymuangleight)\
&=max_{|f|_inftyle1}
  left(langle f,
uangle
  -max_ylangle f,T_ymuangleight).
end{aligned}
]

All feasible sets are compact convex polytopes and the displayed objective is bilinear before the inner minimization, so the minimax interchange is exact.

## Linear programs

The primal LP has converter variables (kappa_y), residual slacks (u_x), and objective (rac12sum_xu_x):

[
egin{array}{ll}
	ext{minimize}&rac12sum_xu_x\
	ext{subject to}&-u_xle
u(x)-sum_ymu(x-y)kappa_yle u_x,\
&kappa_yge0,quadsum_ykappa_y=1,quad u_xge0.
end{array}
]

An equivalent compact dual LP introduces (t) and maximizes
[
rac12(langle f,
uangle-t)
]
subject to
[
-1le f(x)le1,qquad
langle f,T_ymuanglele tquad(orall y).
]

Thus a verifier need only check rational linear equalities and inequalities for a claimed primal/dual pair.

## Automorphism-symmetry reduction

Let (Gammaleoperatorname{Aut}(G)), and suppose both (mu) and (
u) are (Gamma)-invariant.

Then there is an optimal converter (kappa) that is (Gamma)-invariant, and there is an optimal dual witness (f) that is (Gamma)-invariant.

For the primal, average any converter over (Gamma). Convolution commutes with automorphisms, and convexity plus invariance of (
u) shows that the averaged converter has no larger TV error.

For the dual, average (f) over (Gamma). The term (langle f,
uangle) is unchanged. If
[
h_f(y)=langle f,T_ymuangle,
]
then the averaged witness satisfies
[
h_{ar f}(y)=rac1{|Gamma|}sum_{gammainGamma}
 h_f(gamma^{-1}y),
]
so (max_y h_{ar f}(y)lemax_y h_f(y)). Its dual objective is therefore no smaller.

The LP can consequently be collapsed from elements of (G) to (Gamma)-orbits, often cutting both primal and dual dimensions substantially.

## Sparse optimal converters

Let (C_mu) be the convolution matrix whose (y)-th column is (T_ymu), and let (r=operatorname{rank}C_mu).

Every point of (mathcal P_mu), including an optimal approximation to (
u), has a converter supported on at most (r) group elements.

Indeed, all columns of (C_mu) have coordinate sum one. Their affine hull therefore has dimension (r-1): the linear span is the direct sum of one nonzero-sum direction and the span of the column differences. Carathéodory's theorem then needs at most (r) vertices.

For finite abelian (G), the character table diagonalizes (C_mu), hence
[
r=#{chiinwidehat G:widehatmu(chi)
e0}.
]

This is a support bound, not a claim that frequency-by-frequency magnitude comparisons decide convertibility.

## Exact symmetric example

Take (G=mathbb Z/5mathbb Z), with coordinates (0,1,2,3,4), and

[
mu=(1/3,1/3,0,0,1/3),qquad

u=(1/2,1/4,0,0,1/4).
]

Both laws are invariant under inversion (xmapsto-x). The identity converter gives
[
operatorname{TV}(mu,
u)=1/6.
]

Now take the inversion-invariant witness
[
f=(1,-1,-1,-1,-1).
]
For the target, (langle f,
uangle=0). Every translate of (mu) places mass (1/3) at the uniquely positive coordinate of (f) or misses it, so
[
max_ylangle f,T_ymuangle=-1/3.
]
The dual value is therefore
[
rac12(0-(-1/3))=1/6.
]

Primal and dual values match, proving exactly that the best additive conversion error is (1/6). Inversion symmetry reduces the five coordinates to the three orbits
[
{0},quad{1,4},quad{2,3}.
]

The included verifier checks this certificate with exact rational arithmetic, checks symmetry averaging on a non-symmetric converter, and checks a rank-three sparse-support example on (mathbb Z/6mathbb Z).

## Operational meaning

If a proof replaces (
u) by the best obtainable (mu*kappa), every subsequent randomized algorithm or observation channel can change its output distribution by at most (delta(mu,
u)), by data processing for TV distance.

Conversely, the dual witness proves that no independent additive converter can make the input laws closer than (delta). The value is therefore both an achievable error budget and a matching impossibility certificate for this conversion model.

For (m) independent uses of a converter with one-sample error (delta),
[
operatorname{TV}((mu*kappa)^{otimes m},
u^{otimes m})
le 1-(1-delta)^mle mdelta.
]
This is an upper bound for the product converter; correlated multi-sample converters form a different optimization problem on (G^m).

## Prior-art boundary

The translation-experiment and convolution viewpoint is classical; see Torgersen, *Comparison of Translation Experiments* (1972), <https://doi.org/10.1214/aoms/1177692372>. The minimax identity, symmetry averaging, and support reduction use standard finite-dimensional convex duality and Carathéodory's theorem.

A targeted search did not locate this exact TV dual-certificate plus automorphism-orbit and Fourier-rank support package stated for finite additive conversion. We nevertheless make no priority claim. The contribution here is the self-contained theorem, exact certificate format, structural reductions, and rational verifier.

This complements the repository's dense-torus result in [torsion-noise-prior-coupling.md](../torsion-noise-prior-coupling.md), without repeating its Fourier-positivity obstruction.
