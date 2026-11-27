# Prior-art addendum: q-clans and the Dempwolff lift

This addendum records a cross-terminology antecedent found after the immutable
version of this note was frozen.  It does not change the theorem, proof, or
verification outputs.  It changes the appropriate priority claim.

## Exact equation map

Penttila and Storme, [*Monomial Flocks and Herds Containing a Monomial
Oval*](https://doi.org/10.1006/jcta.1997.2855), *J. Combin. Theory Ser. A*
**83** (1998), 21--41, formulate the even-order q-clan condition in their
Section 2.1.  In compatible coordinates, let $h$ be an o-polynomial over
$F=\operatorname{GF}(2^n)$.  The $q$ planes

\[
 X_0=h(b)X_1+\sqrt b\,X_2+a_bX_3\qquad(b\in F)
\]

form the relevant flock exactly when, for every $b\ne c$,

\[
 \operatorname{Tr}\!\left(
   \frac{h(b)+h(c)}{b+c}(a_b+a_c)
 \right)=1. \tag{A}
\]

The same condition arises directly from a partial-spread lift.  Put

\[
 U_\infty=\{(x,0,0):x\in F\},\qquad
 U_b=\{(bx,x,\operatorname{Tr}(h(b)x)):x\in F\}.
\]

After fixing the lift of $U_\infty$ and reducing the other outside
representatives modulo $U_b$, pairwise disjointness is exactly (A).  Equivalently,
substitution of $(X_1,X_2,X_3)=(u^2,uv,v^2)$ turns the difference of two flock
planes into a binary quadratic form; it is anisotropic exactly when (A) holds.
Thus the Dempwolff extension problem is a fixed-coordinate q-clan problem, not
a new trace formalism.

Dempwolff's Theorem 3.5 family is carried to $h(t)=t^2$ by a Frobenius coordinate
change and a square-root relabelling.  More generally, the Frobenius family
$h(t)=t^{2^k}$ gives

\[
 \operatorname{Tr}\big((b+c)^{2^k-1}(a_b+a_c)\big)=1. \tag{B}
\]

## What the 1998 classification already implies

If (B) has any solution, average its multiplicative translates over the
odd-order group $F^*$.  The affine right side remains one, and the average has
the monomial form

\[
 a_0=0,\qquad a_b=A b^{1-2^k}\quad(b\ne0).
\]

Substitution in (B) is precisely Penttila--Storme Section 2.1, equation (3),
with their ordered exponent $e=2^k$.  Their Section 5 classification of monomial
flocks (Theorems 5.1--5.2 and the exponent analysis used in their proofs)
therefore supplies an earlier, implicit route to the same existence decision.
For Frobenius exponents with $\gcd(k,n)=1$, the surviving cases are
$k=n-1$ (the linear case) and, when $n$ is odd, $k=n-2$ (the FTWKB case), including
the small coincidence $2=1/4\pmod 7$ at $n=3$.  In particular the original
$k=1$ Dempwolff family cannot extend for $n\ge4$.

There is no contradiction with the fact that exponent $2$ is related to exponent
$1/2$ at the hyperoval level.  Penttila--Storme use the directed oval

\[
 O_e=\{(1,t,t^e):t\in F\}\cup\{(0,1,0)\},
\]

with a distinguished infinite point and nucleus.  Swapping the two points can
preserve the containing hyperoval while changing this directed oval.  For
q at least 8, $O_2$ is the pointed-conic orientation, whereas $O_{1/2}$ is the conic
orientation admitted by the linear flock.

## Revised contribution boundary

The 1998 paper does not mention Dempwolff's later 2012 question, and the 2012
paper still lists that question as open.  Nevertheless, the q-clan theory
means that the trace condition and the global nonextension consequence should
not be presented as first discovered here.  The appropriate contribution of
this repository item is:

1. an explicit bridge from Dempwolff's named partial-spread lift to the older
   q-clan equation;
2. a self-contained proof in Dempwolff's coordinates; and
3. the stronger local certificate that six finite members plus $U_\infty$
   already force the parity contradiction $0=1$ for every $n\ge4$.

The frozen artifact remains a correct independently verifiable proof.  This
addendum supersedes only its priority wording.
