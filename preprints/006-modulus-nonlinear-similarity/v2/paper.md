# Log-bi-Lipschitz profile avoidance for null configurations

**mxym — AI-assisted research manuscript. Entry 006, version 2, 7 October 2026.**

This note strengthens entry 006 version 1. Version 1 treated germs whose first
nonconstant term has the form (c a^m) with an integer (mge 1). The
finite routing and robust perturbation mechanism in fact needs only that the
leading profile carry positive logarithmic upper Banach density to another
configuration with the same property. We isolate a broad class of profiles
for which that preservation is automatic.

No claim of first discovery is made. The new argument is analytic and
combinatorial; no floating-point computation, solver output, or numerical
optimization is a proof dependency.

## 1. Logarithmic density and admissible profiles

For (Ssubseteqmathbb N={1,2,ldots}), put
[
 F_S(L)=sup_{mge 0}|Scap{m+1,ldots,m+L}|,
 qquad
 d^*(S)=lim_{L	oinfty}rac{F_S(L)}L.
]
As in version 1, subadditivity gives
[
 d^*(S)=inf_{Lge1}rac{F_S(L)}L.
]
For (Asubset(0,infty)), define
[
 S(A)={jge1:Acap(2^{-j-1},2^{-j}]
earnothing}.
]

### Definition 1.1. Log-bi-Lipschitz profile

A function
[
 phi:(0,r_0]longrightarrow(0,infty)
]
is a **log-bi-Lipschitz profile near zero** if

1. (phi) is strictly increasing and (phi(a)	o0) as (adownarrow0);
2. for
   [
   Psi(z)=-log_2phi(2^{-z}),
   ]
   there are (z_0<infty) and constants (0<cle C<infty) such that
   [
   c(v-u)le Psi(v)-Psi(u)le C(v-u)
   	ag{1.1}
   ]
   whenever (vge uge z_0).

Shrinking (r_0) is harmless. Condition (1.1) says precisely that the
profile is a bi-Lipschitz change of scale in logarithmic coordinates.

Every power (a^s), (s>0), is admissible. More generally,
[
 phi_{s,eta}(a)
 =a^sigl(log(e/a)igr)^eta
 qquad(s>0, etainmathbb R)
 	ag{1.2}
]
is admissible after restricting to a sufficiently small interval.

## 2. Density survives a log-bi-Lipschitz change of scale

### Lemma 2.1. Profile invariance of positive logarithmic upper Banach density

Let (Asubset(0,infty)) satisfy
[
 d^*(S(A))=delta>0,
]
and let (phi) be a log-bi-Lipschitz profile. Then every sufficiently small
tail of (phi(A)) has positive logarithmic upper Banach density. In
particular,
[
 d^*(S(phi(Acap(0,r))))>0
]
for every sufficiently small (r>0).

**Proof.**
Discard finitely many dyadic bins so that all selected points lie in the
domain where (1.1) holds. This does not change (delta).

For every (jin S(A)) in this tail choose
[
 a_jin Acap(2^{-j-1},2^{-j}]
]
and write
[
 z_j=-log_2 a_jin[j,j+1).
]
Then
[
 y_j=-log_2phi(a_j)=Psi(z_j).
]

Let
[
 K=lceil 1/cceil+2.
	ag{2.1}
]
If (y_j,y_k) lie in the same integer bin, then
[
 |y_j-y_k|<1.
]
The lower inequality in (1.1) gives
[
 |z_j-z_k|<1/c,
]
and therefore
[
 |j-k|<1/c+1.
]
Hence at most (K) of the chosen input indices can land in one output
integer bin.

Now fix (L). Since
(d^*(S(A))=inf_q F_{S(A)}(q)/q=delta), some integer interval
(I_L) of length (L) contains at least (delta L) selected input
indices. If (I_L={m+1,ldots,m+L}), all associated (z_j) lie in
an interval of length less than (L). The upper inequality in (1.1)
therefore places all corresponding (y_j) in an interval of length less
than (CL). By (2.1), they occupy at least
[
 rac{delta L}{K}
]
distinct integer output bins. Thus, for all large (L), there is an integer
interval (J_L) of length at most (CL+3) on which (S(phi(A))) has
density at least a fixed number
[
 eta>0
 	ag{2.2}
]
depending only on (delta,c,C). The lengths (|J_L|) tend to infinity,
because the number of occupied bins in them tends to infinity.

It remains to note that arbitrarily long intervals with a fixed positive
density already force positive upper Banach density. Indeed, fix (qge1)
and partition such a (J_L) into full blocks of length (q) and one
remainder. Then
[
 eta |J_L|
 le
 Bigllfloorrac{|J_L|}{q}Bigrfloor F_{S(phi(A))}(q)+q.
]
Letting (|J_L|	oinfty) yields
[
 rac{F_{S(phi(A))}(q)}qgeeta.
]
Since this holds for every (q),
[
 d^*(S(phi(A)))geeta>0.
]
Deleting an additional finite initial tail does not change this conclusion.
(square)

### Remark 2.2

The proof uses only bounded logarithmic distortion, not differentiability of
(phi). In particular, the relevant invariant is not the algebraic form of
the profile but its coarse geometry on logarithmic scales.

## 3. The profile-avoidance theorem

A **null modulus** is, as in version 1, a nondecreasing finite function
[
 omega:(0,infty)	o[0,infty)
]
with (omega(a)	o0) as (adownarrow0).

### Theorem 3.1. Prescribed log-bi-Lipschitz profile avoidance

Let ((A_ell)_{ellge1}) be a nonempty countable family satisfying
[
 d^*(S(A_ell))>0
qquad(ellge1).
]
Let ((phi_r)_{rge1}) be a nonempty countable family of
log-bi-Lipschitz profiles, and let ((omega_j)_{jge1}) be a nonempty
countable family of null moduli.

For every (0<arepsilon<1) there is a closed, nowhere-dense,
one-periodic set (Esubsetmathbb R) such that
[
 |Ecap[x,x+1]|>1-arepsilon
 qquad(xinmathbb R)
 	ag{3.1}
]
and with the following property.

Suppose (f) is defined on a sufficiently small tail of some (A_ell)
and, for some (r,j), some (yinmathbb R), (c
e0), and (M<infty),
[
 |f(a)-y-cphi_r(a)|
 le
 Mphi_r(a)omega_j(a)
 	ag{3.2}
]
for all sufficiently small (ain A_ell). Then, for every sufficiently
small (ho>0),
[
 f(A_ellcap(0,ho))setminus E
]
is infinite.

The same (E) works simultaneously for every choice of the displayed
countable indices and for every function satisfying (3.2); the functions
themselves are not enumerated.

**Proof.**
We use the robust normalized blocker proved in version 1: if a configuration
(B) has positive logarithmic upper Banach density and (Omega) is a
null modulus, then for every sufficiently small density budget there is an
open periodic blocker meeting every perturbed normalized copy
[
 x+t b+e(b),
 qquad
 tin[1,2],qquad |e(b)|le bOmega(b).
 	ag{3.3}
]

Fix (ell,r,j), an integer (k), an integer (qge1), and a tail
cutoff (h). After increasing (h) if necessary, (phi_r) is strictly
increasing on the whole tail and has an inverse there. Put
[
 B_{ell,r,k,h}
 =
 {,2^kphi_r(a):
       ain A_ell, 0<a<2^{-h},}.
 	ag{3.4}
]
Lemma 2.1 shows that this configuration has positive logarithmic upper
Banach density.

On a sufficiently small range of (b), define
[
 Omega_{r,j,k,q}(b)
 =
 q,2^{-k}
 omega_j!left(
   phi_r^{-1}(2^{-k}b)
 ight).
 	ag{3.5}
]
It is nondecreasing, finite, and tends to zero with (b). Extend it
constantly outside a smaller neighborhood if necessary, exactly as in
version 1. Thus it is a null modulus.

Apply the version-1 robust blocker to every tuple
[
 (ell,r,j,k,q,h)
]
with summable density budgets, and also include the reflected blocker.
There are only countably many tuples. We may additionally include the
identity profile (amapsto a) with an arbitrarily small share of the
budget; this guarantees the affine obstruction used below to make the
complement nowhere dense. Let (U) be the union of all blockers and their
reflections, and put
[
 E=mathbb Rsetminus U.
]
The budgets can be chosen so that (U) has density less than
(arepsilon). Hence (3.1) holds. The set (E) is closed and periodic.

Now assume (3.2). First suppose (c>0). Write
[
 c=2^k t,qquad tin[1,2],
]
and choose an integer (qge M). With
[
 b=2^kphi_r(a),
]
the error in (3.2) satisfies
[
 |f(a)-y-tb|
 le
 Mphi_r(a)omega_j(a)
 le
 b,Omega_{r,j,k,q}(b).
]
Consequently the blocker associated with every sufficiently late cutoff
(h) supplies a point
[
 f(a)in U,qquad ain A_ell,quad a<2^{-h}.
]
Thus there are hits at inputs tending to zero.

Because (omega_j(a)	o0), for all sufficiently small (a)
[
 rac{|c|}{2}phi_r(a)
 le |f(a)-y|
 le rac{3|c|}{2}phi_r(a).
 	ag{3.6}
]
Hence these hit values tend to (y) but are not equal to (y), and so
infinitely many distinct points of the image lie outside (E).
For (c<0), apply the same argument after reflection.

Finally, the adjoined identity profile blocks nontrivial affine copies of a
bounded tail of every (A_ell). If (E) contained a nonempty interval,
a sufficiently small affine copy of such a bounded tail would fit inside
that interval, a contradiction. Hence (E) has empty interior. Being
closed, it is nowhere dense.
(square)

## 4. Power, power-log, and smoothly varying profiles

### Corollary 4.1. Arbitrary prescribed countable power exponents

Let (Sigmasubset(0,infty)) be countable. One may choose a single set
(E) in Theorem 3.1 which simultaneously excludes every germ
[
 f(a)=y+c a^s+O(a^somega_j(a)),
 qquad sinSigma,quad c
e0.
 	ag{4.1}
]
In particular, one may take (Sigma=mathbb Q_{>0}).

**Proof.**
For (phi_s(a)=a^s),
[
 Psi_s(z)=sz,
]
so (1.1) holds with (c=C=s). Apply Theorem 3.1.
(square)

### Corollary 4.2. Power-log profiles

For any prescribed countable family of pairs
[
 (s,eta)in(0,infty)	imesmathbb R,
]
the same conclusion holds with
[
 a^s
quad	ext{replaced by}quad
 a^s(log(e/a))^eta.
]

**Proof.**
For (1.2),
[
 Psi(z)
 =
 sz-etalog_2(1+zlog 2),
]
and therefore
[
 Psi'(z)
 =
 s-rac{eta}{1+zlog2}.
]
For sufficiently large (z), this derivative lies between two positive
constants, for example (s/2) and (3s/2) after enlarging the upper bound
when necessary. The mean value theorem gives (1.1).
(square)

### Corollary 4.3. A differentiable slowly varying criterion

Let (s>0) and let (L:(0,r_0]	o(0,infty)) be (C^1). If
[
 rac{aL'(a)}{L(a)}longrightarrow0
 qquad(adownarrow0),
 	ag{4.2}
]
then
[
 phi(a)=a^sL(a)
]
is a log-bi-Lipschitz profile after restriction to a sufficiently small
interval.

**Proof.**
For (a=2^{-z}),
[
 Psi'(z)
 =
 s+rac{aL'(a)}{L(a)}.
]
By (4.2), this lies in ([s/2,3s/2]) for all sufficiently large (z).
Again use the mean value theorem.
(square)

## 5. Puiseux germs

### Corollary 5.1. Simultaneous avoidance of convergent Puiseux germs

Assume the hypotheses on the configurations (A_ell). There is a closed,
nowhere-dense, one-periodic set (E) of arbitrarily large measure which
simultaneously excludes every nonconstant real germ on the positive side
having a convergent Puiseux expansion with finite limit at zero.

More explicitly, suppose
[
 f(a)
 =
 y+sum_{
uge
u_0} c_
u a^{
u/q}
	ag{5.1}
]
converges for sufficiently small positive (a), where (qge1),
(c_{
u_0}
e0), and (s=
u_0/q>0). Then every sufficiently small
tail of (f(A_ell)) has infinitely many points outside (E).

**Proof.**
Take in Theorem 3.1 all rational power profiles
[
 phi_s(a)=a^s,qquad sinmathbb Q_{>0},
]
and the countable null moduli
[
 omega_q(a)=a^{1/q},qquad qge1.
]
Convergence of (5.1) gives
[
 f(a)
 =
 y+c_{
u_0}a^s+O(a^{s+1/q}),
]
so the relative remainder is (O(a^{1/q})). Apply Theorem 3.1.
(square)

The classical Newton--Puiseux theorem can be used separately to convert
Corollary 5.1 into an algebraic-branch statement. That external theorem is
not a dependency of Theorem 3.1 itself.

## 6. What this does and does not settle

Theorem 3.1 strictly enlarges the version-1 class of finite-order smooth and
analytic germs. The exponent need not be an integer, and the leading term
need not be a pure power. The proof also identifies the invariant actually
used by the routing method: bounded distortion in logarithmic coordinates.

The countability qualification is essential to the present construction.
The theorem does **not** claim one set excluding an arbitrary uncountable
family of profiles, and in particular does not yet give simultaneous
avoidance for every real exponent (s>0).

It also does not cross the endpoint obstruction already proved in version 1:
arbitrary null sequences can be embedded by smooth maps flat at zero, and
lacunary sequences can be embedded by increasing (C^1) diffeomorphisms.
The present theorem instead enlarges the explicitly controlled asymptotic
classes lying on the avoidable side of that boundary.

## 7. Dependency and verification scope

The only substantive inherited result is the robust normalized blocker from
entry 006 version 1, whose proof reduces the infinite statement to finite
routing plus a vanishing perturbation buffer. Version 1 includes the exact
rational finite-cover checker and boundary regression tests.

The new ingredient in this note is Lemma 2.1 and its use in Theorem 3.1.
Those arguments are written proofs and have no numerical proof dependency.
The finite checker from version 1 remains a regression test for the inherited
routing engine; it does not by itself certify the new infinite
log-bi-Lipschitz lemma.

Version 1 first complete source was publicly disclosed in commit
`478be8879564e99843ad0bc69ca6192379e5b59e`. Historical sources are not
modified by this supplement.

No novelty, priority, external-referee, or proof-assistant-formalization
claim is made here.
