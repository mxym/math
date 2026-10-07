# Modulus-robust nonlinear avoidance: proof record

Research date: 2026-10-07. Prepared with AI assistance. This is a written proof record, not an external referee report or proof-assistant certificate. A complete standalone manuscript and verification interface are being assembled in the current research pass. Existing manuscripts 001--005 are not modified by this record.

## Precise additional result

Let A be a subset of the positive reals whose occupied dyadic annuli have positive upper Banach density. Fix any countable family of nondecreasing moduli omega_j(t) tending to zero as t decreases to zero. For every epsilon>0 there is a closed, nowhere-dense, one-periodic set E, of measure greater than 1-epsilon in every unit interval, with the following property. For every positive integer m, every real x, every nonzero real c, every j, and every function defined on a sufficiently small tail of A satisfying

`|f(a)-x-c*a^m| <= C*a^m*omega_j(a)`

on that tail for some finite C, infinitely many of its image points lie outside E. The same E can treat countably many prescribed configurations A.

Taking omega_j(t)=t^(1/j) excludes every smooth germ having a nonzero derivative of some positive order at zero (after subtracting its constant term), every nonconstant real-analytic germ, and every C^(1,alpha) germ with nonzero derivative at zero, for every alpha>0. It does not exclude all C^1 germs or flat smooth germs. It does not settle the unrestricted Erdos similarity conjecture.

## Uniform-tail density placement

Write delta=d*(S)>0 and fix eta<delta. For every xi>0, there is a constant C_xi such that every interval I has at most (delta+xi)|I|+C_xi points of S. This constant works in every tail, because translated-tail intervals are intervals of the original S. Every tail has upper Banach density delta; its maximal count in length T is therefore at least delta*T for every T.

Consequently, a finite template of length T_L<=C*L, whose windows have lengths at least L, can be filled at density eta beyond ANY prescribed index H once L is sufficiently large. Importantly, the lower threshold for L is independent of H. Subtract the at most two complementary interval counts from a length-T_L interval of count at least delta*T_L:

`|S intersect W| >= delta*|W| - xi*C*L - 2*C_xi`.

Choose xi first and L next. The starting index may then be required to be arbitrarily large without changing the template's span.

## Robustification of the finite routing engine

The finite engine proved in manuscript 004, Sections 3--6, supplies the following with constants independent of the template's starting index u. For a fixed small p, choose a fixed finite span T and a density-filled template [u,u+T-1]. The random blocker B is a union of cells of the finest grid with

`N = 2^(u+T+2)`.

It has expected periodic density p. Outside an unstable set of density less than p, the probability that some t in [1,2] misses all finite tests x+t*a_j is at most 2p. This statement is about the finite random construction before exceptional-center repair, not just the qualitative existence of an affine avoiding set.

Set eta_u=omega(2^(-u))+2^(-u) and d_u=2^(-u)*eta_u. Every allowed test perturbation has size at most d_u. Because T is fixed before choosing u, the uniform-tail placement permits

`4*N*d_u = 2^(T+4)*eta_u < p`.

Let B1=B+(-d_u,d_u) and B2=B+(-2*d_u,2*d_u), with sums understood periodically. Then density(B2)<=density(B)+4*N*d_u. The residual set

`R={x: some t in [1,2] has x+t*a_j outside B1 for every finite test j}`

is closed by compact projection, and its expected density is at most 3p. Select an outcome with density(B2)+density(R)<=5p, take an open periodic V containing R of density at most density(R)+p, and put H=B2 union V.

If x is outside R, one unperturbed test lies in B1, so every perturbation of that test of size at most d_u lies in B2. If x is in R, all sufficiently late perturbed points approach x and hence lie in V. Thus H has density at most 6p and meets EVERY independently perturbed normalized copy. No measurability or smoothness of the perturbation function is required.

## All coefficients, powers, tails, and signs

Occupied logarithmic-bin density stays positive under a fixed positive power and a fixed positive dilation: in logarithmic coordinates these are linear changes of bin length plus translation, with uniformly bounded bin overlaps. For a leading coefficient c>0 write c=2^k*t with t in [1,2] and put b=2^k*a^m. The error bound becomes b times a new null modulus, namely C*2^(-k)*omega_j((2^(-k)*b)^(1/m)). Enlarge C to an integer and apply the normalized construction to every k,m,j,C and every tail cutoff, with summable budgets. Reflection handles negative c. This is a countable union of open blockers, not an illegitimate union over uncountably many functions. Geometric separation of the selected parity representatives ensures that infinitely many tail hits give infinitely many distinct image points. Affine avoidance implies that E has empty interior.

## Endpoint and attribution

For a positive sequence a_(n+1)<=q*a_n with 0<q<1, every Lebesgue-measurable positive-measure set contains an increasing global C^1-diffeomorphic copy. At a density point, choose lambda and actual image points x+lambda*a_n+e_n so that |e_n|/(lambda*a_n) is uniformly smaller than theta/(2*||phi'||_infinity) for all n and tends to zero. Disjoint bumps of radius theta*a_n then give derivative between lambda/2 and 3*lambda/2, including the finite prefix, and a global C^1 inverse. The [complete manuscript and endpoint proof](../preprints/006-modulus-nonlinear-similarity/v1/main.tex) supplies the point selection and extension; merely e_n=o(a_n) would not justify uniform derivative positivity. This is closely related to the density-point construction of Feng, Lai and Xiong, *Erdos similarity problem via bi-Lipschitz embedding*, arXiv:2312.01319, Theorem 1.1; endpoint novelty is not asserted.

The finite routing, local entropy, and exceptional-center repair are inherited from OpenAI family 084 and manuscript 004. The additional argument is uniform-tail template placement followed by a perturbation buffer at the finest grid. Pinned local source: mxym/math commit e894ed8678052e45ecd9f1714b6a996cfea33cf3, preprints/004-log-density-similarity/v1.1/build/main.tex. Upstream source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, family 084. Rights and provenance notices in the repository continue to apply. No journal-tier or priority claim is made.

